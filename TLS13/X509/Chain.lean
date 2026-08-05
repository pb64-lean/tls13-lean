module

public import TLS13.X509.Signature

public section

/-!
Pure X.509 path construction and validation.

The caller supplies the current Unix epoch second and parsed trust anchors, so
the validation core performs no clock, environment, or filesystem I/O. Paths
are built by byte-exact issuer Name DER to subject Name DER equality. The
server-presented certificates are searched before trust anchors, with bounded
backtracking for same-name and cross-signed alternatives.

Revocation is deliberately out of scope: no CRL or OCSP checks are performed,
matching libpq's default certificate-verification behavior.
-/

namespace TLS13
namespace X509
namespace Chain

/-- Parsed certificate trust anchors. -/
structure TrustStore where
  anchors : Array Certificate
  deriving BEq, Inhabited

namespace TrustStore

/-- Decode every certificate in a strict PEM bundle as a trust anchor. -/
def decodePEM (text : String) : Except String TrustStore := do
  pure { anchors := ← Certificate.decodePEM text }

end TrustStore

/-- A specific certificate-path validation failure. Certificate serials make
errors useful to callers without copying attacker-controlled Names into them. -/
inductive Failure where
  | unknownIssuer (serial : Nat)
  | notYetValid (serial : Nat) (notBefore now : Int)
  | expired (serial : Nat) (notAfter now : Int)
  | badSignature (childSerial issuerSerial : Nat)
  | leafDigitalSignatureMissing (leafSerial : Nat)
  | notCA (issuerSerial : Nat)
  | keyCertSignMissing (issuerSerial : Nat)
  | pathLenExceeded (issuerSerial limit actual : Nat)
  | unhandledCriticalExtension (serial : Nat) (oid : OID)
  | loop (serial : Nat)
  | maximumDepthExceeded (limit : Nat)
  | maximumIssuerAttemptsExceeded (limit : Nat)
  deriving Repr, BEq, DecidableEq

namespace Failure

def render : Failure → String
  | .unknownIssuer serial =>
      s!"certificate {serial} has no issuer in the presented chain or trust store"
  | .notYetValid serial notBefore now =>
      s!"certificate {serial} is not valid until {notBefore} (now {now})"
  | .expired serial notAfter now =>
      s!"certificate {serial} expired at {notAfter} (now {now})"
  | .badSignature childSerial issuerSerial =>
      s!"certificate {childSerial} has an invalid signature from issuer {issuerSerial}"
  | .leafDigitalSignatureMissing leafSerial =>
      s!"leaf certificate {leafSerial} KeyUsage does not permit TLS digital signatures"
  | .notCA issuerSerial =>
      s!"issuer certificate {issuerSerial} is not a CA"
  | .keyCertSignMissing issuerSerial =>
      s!"issuer certificate {issuerSerial} KeyUsage does not permit certificate signing"
  | .pathLenExceeded issuerSerial limit actual =>
      s!"issuer certificate {issuerSerial} pathLenConstraint {limit} \
        is exceeded by {actual} intermediate CAs"
  | .unhandledCriticalExtension serial oid =>
      s!"certificate {serial} has unhandled critical extension {oid}"
  | .loop serial =>
      s!"certificate path repeats while resolving certificate {serial}"
  | .maximumDepthExceeded limit =>
      s!"certificate path exceeds the maximum of {limit} certificates"
  | .maximumIssuerAttemptsExceeded limit =>
      s!"certificate path search exceeds the maximum of {limit} issuer attempts"

end Failure

instance : ToString Failure := ⟨Failure.render⟩

/-- A successful leaf-to-anchor path. `path[0]` is `leaf` and the last entry is
the exact certificate selected from the trust store. -/
structure VerifiedChain where
  leaf : Certificate
  anchor : Certificate
  path : Array Certificate
  deriving Inhabited

/-- Maximum number of certificates, including leaf and anchor, in a path. -/
def defaultMaximumDepth : Nat := 10

/-- Global issuer-candidate work budget across every backtracking branch. -/
def defaultMaximumIssuerAttempts : Nat := 128

private def sameCertificate (left right : Certificate) : Bool :=
  left.encoded == right.encoded

private def containsCertificate
    (certificates : Array Certificate) (wanted : Certificate) : Bool :=
  certificates.any (sameCertificate · wanted)

private def findAnchor?
    (trustStore : TrustStore) (certificate : Certificate) : Option Certificate :=
  trustStore.anchors.find? (sameCertificate · certificate)

private def checkCertificate (now : Int) (certificate : Certificate) :
    Except Failure Unit := do
  let serial := certificate.tbsCertificate.serialNumber
  let validity := certificate.tbsCertificate.validity
  if now < validity.notBefore.unixSeconds then
    throw (.notYetValid serial validity.notBefore.unixSeconds now)
  if now > validity.notAfter.unixSeconds then
    throw (.expired serial validity.notAfter.unixSeconds now)
  for extension in certificate.tbsCertificate.extensions.unhandled do
    if extension.critical then
      throw (.unhandledCriticalExtension serial extension.oid)

/-- RFC 9846's TLS policy for the target certificate: absence of KeyUsage is
permitted, but when the extension is present it must authorize the signature
made in CertificateVerify. This is deliberately a leaf/target check; issuer
certificates are governed separately by `keyCertSign` in `checkIssuer`. -/
def leafKeyUsagePermitsDigitalSignature (leaf : Certificate) : Bool :=
  match leaf.tbsCertificate.extensions.keyUsage with
  | none => true
  | some usage => usage.value.digitalSignature

private def checkLeafKeyUsage (leaf : Certificate) : Except Failure Unit :=
  if leafKeyUsagePermitsDigitalSignature leaf then
    .ok ()
  else
    .error (.leafDigitalSignatureMissing leaf.tbsCertificate.serialNumber)

/-- Count non-self-issued intermediate CAs strictly between the target leaf and
an issuer candidate. RFC 5280 excludes self-issued certificates from this
count; the target certificate at index zero is never an intermediate. -/
private def intermediateCAsBelow (path : Array Certificate) : Nat := Id.run do
  let mut count := 0
  for index in [1:path.size] do
    let certificate := path[index]!
    match certificate.tbsCertificate.extensions.basicConstraints with
    | some constraints =>
      if constraints.value.ca &&
          certificate.tbsCertificate.subject.encoded !=
            certificate.tbsCertificate.issuer.encoded then
        count := count + 1
    | none => pure ()
  return count

/-- Vet one issuer/child link of a candidate path: the child's signature must
verify under the issuer's public key over the child's retained
`TBSCertificate.encoded` bytes, and the issuer must be a CA permitted to sign
at this depth. Public (but not `@[expose]`d) so `checkIssuer_verifies` can be
stated; path construction is `validate`'s business, not the caller's. -/
def checkIssuer
    (path : Array Certificate) (issuer child : Certificate) :
    Except Failure Unit := do
  let childSerial := child.tbsCertificate.serialNumber
  let issuerSerial := issuer.tbsCertificate.serialNumber
  unless Signature.verifyX509
      child.signatureAlgorithm
      issuer.tbsCertificate.subjectPublicKeyInfo
      child.tbsCertificate.encoded
      child.signature do
    throw (.badSignature childSerial issuerSerial)
  let some constraints :=
      issuer.tbsCertificate.extensions.basicConstraints
    | throw (.notCA issuerSerial)
  unless constraints.value.ca do
    throw (.notCA issuerSerial)
  match issuer.tbsCertificate.extensions.keyUsage with
  | some usage =>
    unless usage.value.keyCertSign do
      throw (.keyCertSignMissing issuerSerial)
  | none => pure ()
  match constraints.value.pathLenConstraint with
  | some limit =>
    let actual := intermediateCAsBelow path
    if actual > limit then
      throw (.pathLenExceeded issuerSerial limit actual)
  | none => pure ()

private def appendIssuerCandidates
    (result candidates path : Array Certificate) (child : Certificate) :
    Array Certificate := Id.run do
  let mut result := result
  for candidate in candidates do
    if candidate.tbsCertificate.subject.encoded ==
        child.tbsCertificate.issuer.encoded &&
        !containsCertificate path candidate &&
        !containsCertificate result candidate then
      result := result.push candidate
  return result

private def issuerCandidates
    (presented : Array Certificate) (trustStore : TrustStore)
    (path : Array Certificate) (child : Certificate) : Array Certificate :=
  let fromPresented :=
    appendIssuerCandidates #[] presented path child
  appendIssuerCandidates fromPresented trustStore.anchors path child

private def hasRepeatedIssuer
    (presented : Array Certificate) (trustStore : TrustStore)
    (path : Array Certificate) (child : Certificate) : Bool :=
  (presented ++ trustStore.anchors).any fun candidate =>
    candidate.tbsCertificate.subject.encoded ==
        child.tbsCertificate.issuer.encoded &&
      containsCertificate path candidate

private structure SearchResult where
  result : Except Failure VerifiedChain
  attemptsRemaining : Nat
  deriving Inhabited

private def searchFailed (failure : Failure) (attemptsRemaining : Nat) :
    SearchResult :=
  { result := .error failure, attemptsRemaining }

private def isAttemptLimit : Failure → Bool
  | .maximumIssuerAttemptsExceeded _ => true
  | _ => false

mutual

/-- Depth-first search for a trust anchor. Termination is lexicographic: the
remaining depth budget shrinks on every recursive descent, and the candidate
list shrinks within one level. -/
private def buildPath
    (now : Int) (maximumDepth maximumIssuerAttempts : Nat)
    (leaf current : Certificate)
    (presented : Array Certificate) (trustStore : TrustStore)
    (path : Array Certificate) (attemptsRemaining : Nat) :
    SearchResult :=
  if _hdepth : path.size ≥ maximumDepth then
    searchFailed (.maximumDepthExceeded maximumDepth) attemptsRemaining
  else if containsCertificate path current then
    searchFailed (.loop current.tbsCertificate.serialNumber) attemptsRemaining
  else
    match checkCertificate now current with
    | .error failure => searchFailed failure attemptsRemaining
    | .ok () =>
      match findAnchor? trustStore current with
      | some anchor =>
        { result := .ok { leaf, anchor, path := path.push current }
          attemptsRemaining }
      | none =>
        let candidates :=
          issuerCandidates presented trustStore (path.push current) current
        if candidates.isEmpty then
          if current.tbsCertificate.subject.encoded !=
              current.tbsCertificate.issuer.encoded &&
              hasRepeatedIssuer presented trustStore (path.push current)
                current then
            searchFailed (.loop current.tbsCertificate.serialNumber)
              attemptsRemaining
          else
            searchFailed (.unknownIssuer current.tbsCertificate.serialNumber)
              attemptsRemaining
        else
          tryIssuers now maximumDepth maximumIssuerAttempts leaf current
            presented trustStore (path.push current) candidates.toList
            none attemptsRemaining
  termination_by (maximumDepth - path.size, 0)
  decreasing_by
    apply Prod.Lex.left
    simp only [Array.size_push]
    omega

/-- One level of the issuer search: try each candidate in order, tracking the
first non-limit failure and the shared attempts budget, exactly like the
former in-place loop. -/
private def tryIssuers
    (now : Int) (maximumDepth maximumIssuerAttempts : Nat)
    (leaf current : Certificate)
    (presented : Array Certificate) (trustStore : TrustStore)
    (path : Array Certificate) (candidates : List Certificate)
    (firstFailure : Option Failure) (attemptsRemaining : Nat) :
    SearchResult :=
  match candidates with
  | [] =>
      searchFailed
        (firstFailure.getD
          (.unknownIssuer current.tbsCertificate.serialNumber))
        attemptsRemaining
  | issuer :: restCandidates =>
      if attemptsRemaining == 0 then
        searchFailed (.maximumIssuerAttemptsExceeded maximumIssuerAttempts) 0
      else
        match checkIssuer path issuer current with
        | .error failure =>
            tryIssuers now maximumDepth maximumIssuerAttempts leaf current
              presented trustStore path restCandidates
              (if firstFailure.isNone then some failure else firstFailure)
              (attemptsRemaining - 1)
        | .ok () =>
            let branch :=
              buildPath now maximumDepth maximumIssuerAttempts
                leaf issuer presented trustStore path (attemptsRemaining - 1)
            match branch.result with
            | .ok _ => branch
            | .error failure =>
                if isAttemptLimit failure then
                  branch
                else
                  tryIssuers now maximumDepth maximumIssuerAttempts leaf
                    current presented trustStore path restCandidates
                    (if firstFailure.isNone then some failure
                      else firstFailure)
                    branch.attemptsRemaining
  termination_by (maximumDepth - path.size, candidates.length + 1)
  decreasing_by
    all_goals apply Prod.Lex.right
    all_goals simp only [List.length_cons]
    all_goals omega

end

/-- Build and validate a path from `leaf` to an exact trust-store anchor.

`presented` should contain the remaining certificates sent by the peer, in any
order. When the leaf has a KeyUsage extension, its `digitalSignature` bit must
be set, as required for the TLS CertificateVerify signing certificate.
Validity is inclusive at both endpoints. Every path certificate,
including the anchor, is checked for validity and unhandled critical
extensions. Every parent is checked for signature authority, CA constraints,
KeyUsage, and pathLenConstraint before it may issue its child. Both path depth
and the total work spent trying issuer candidates are bounded. -/
def validate
    (now : Int) (leaf : Certificate) (presented : Array Certificate)
    (trustStore : TrustStore)
    (maximumDepth : Nat := defaultMaximumDepth)
    (maximumIssuerAttempts : Nat := defaultMaximumIssuerAttempts) :
    Except Failure VerifiedChain := do
  checkLeafKeyUsage leaf
  (buildPath now maximumDepth maximumIssuerAttempts
    leaf leaf presented trustStore #[] maximumIssuerAttempts).result

/-!
## The signed-bytes corollary

The message argument `checkIssuer` passes to `Signature.verifyX509` is,
definitionally, `child.tbsCertificate.encoded` — which
`Certificate.decode_tbs_encoded` proves is the byte-exact slice of the input
DER that the TBS parser consumed. The theorem below makes the connection
checkable from the outside: issuer vetting can only succeed if the signature
verified over exactly those retained bytes. -/

/-- Peel one `Except` bind off a successful computation. -/
private theorem bind_ok_ex {ε α β : Type} {x : Except ε α}
    {f : α → Except ε β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Case on the condition of a successful branching computation. -/
private theorem ite_ok_cases {ε β : Type} {c : Prop} [Decidable c]
    {t e : Except ε β} {b : β} (h : (if c then t else e) = .ok b) :
    (c ∧ t = .ok b) ∨ (¬c ∧ e = .ok b) := by
  split at h
  · exact .inl ⟨‹_›, h⟩
  · exact .inr ⟨‹_›, h⟩

/-- Successful issuer vetting requires the cryptographic signature to have
verified over exactly the retained `TBSCertificate.encoded` bytes of the
child certificate. Together with `Certificate.decode_tbs_encoded` — which says
those retained bytes are the exact DER substring the decoder consumed — this is
the link that rules out signing one certificate and presenting another. -/
theorem checkIssuer_verifies {path : Array Certificate}
    {issuer child : Certificate}
    (h : checkIssuer path issuer child = .ok ()) :
    Signature.verifyX509 child.signatureAlgorithm
      issuer.tbsCertificate.subjectPublicKeyInfo
      child.tbsCertificate.encoded child.signature = true := by
  unfold checkIssuer at h
  obtain ⟨hc, -⟩ | ⟨hc, h⟩ := ite_ok_cases h
  · exact hc
  · obtain ⟨_, hu, _⟩ := bind_ok_ex h
    cases hu

/-- Successful TLS path validation implies the RFC 9846 KeyUsage condition on
the target certificate. In particular, a present KeyUsage extension has its
`digitalSignature` bit set. -/
theorem validate_leaf_keyUsage {now : Int} {leaf : Certificate}
    {presented : Array Certificate} {trustStore : TrustStore}
    {maximumDepth maximumIssuerAttempts : Nat} {verified : VerifiedChain}
    (h : validate now leaf presented trustStore maximumDepth
      maximumIssuerAttempts = .ok verified) :
    leafKeyUsagePermitsDigitalSignature leaf = true := by
  unfold validate at h
  obtain ⟨checked, hcheck, -⟩ := bind_ok_ex h
  cases checked
  unfold checkLeafKeyUsage at hcheck
  split at hcheck
  · assumption
  · cases hcheck

end Chain
end X509
end TLS13
