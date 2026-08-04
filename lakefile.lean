import Lake
open Lake DSL

/-!
IDE project model. Bazel remains the authoritative build because it compiles
and links the HACL* C shim; these libraries let sibling Lean projects resolve
the protocol and binding declarations in `lake serve`.
-/

package «tls13-lean» where
  leanOptions := #[⟨`experimental.module, true⟩]

lean_lib «HaclStar» where
  roots := #[
    `HaclStar.Aead,
    `HaclStar.Curve25519,
    `HaclStar.Hex,
    `HaclStar.Hkdf,
    `HaclStar.Hmac,
    `HaclStar.P256,
    `HaclStar.Sha256,
    `HaclStar.Signature,
  ]

lean_lib «TLS13» where
  roots := #[
    `TLS13.KeySchedule,
    `TLS13.KeySchedule.Refinement,
    `TLS13.KeySchedule.Spec,
    `TLS13.X509,
  ]
