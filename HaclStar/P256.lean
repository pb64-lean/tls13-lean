module

public section

/-!
NIST P-256 ECDH via HACL*'s portable `Hacl_P256`.

Private scalars and shared secrets use the 32-byte, big-endian representation
required by SEC 1 and TLS 1.3. Public keys use SEC 1's 65-byte uncompressed
encoding (`0x04 || x || y`), which is the representation carried in a TLS
`key_share` for `secp256r1`.
-/

namespace HaclStar
namespace P256

/-- Derive a SEC 1 uncompressed public key from a 32-byte private scalar.
Returns `none` if the input length is not 32 or the scalar is not in
`1 .. n-1`, where `n` is the P-256 group order. -/
@[extern "tls13_hacl_p256_public_key"]
opaque publicKey (privateKey : ByteArray) : Option ByteArray

/-- P-256 ECDH using a 32-byte private scalar and a 65-byte SEC 1
uncompressed peer public key. Returns the 32-byte x coordinate of the common
point, as required by TLS 1.3, or `none` for a bad length, encoding, scalar,
or point. -/
@[extern "tls13_hacl_p256_ecdh"]
opaque ecdh (privateKey peerPublicKey : ByteArray) : Option ByteArray

end P256
end HaclStar
