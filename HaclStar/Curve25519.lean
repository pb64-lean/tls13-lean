module

public section

/-!
X25519 (Curve25519 ECDH, RFC 7748), via HACL*'s portable `Hacl_Curve25519_51`.
Scalars and points are 32 bytes. This is the default TLS 1.3 key-exchange group.
-/

namespace HaclStar
namespace X25519

/-- The public value for a 32-byte private scalar: X25519(scalar, basepoint).
HACL clamps the scalar internally. -/
@[extern "tls13_hacl_x25519_base"]
opaque base (priv : ByteArray) : ByteArray

/-- X25519 Diffie–Hellman: the shared secret for our private scalar `priv` and a
peer public value `pub`. Returns `none` when the result is the all-zero value (a
low-order input point), which RFC 8446 §7.4.2 requires the caller to reject. -/
@[extern "tls13_hacl_x25519_ecdh"]
opaque ecdh (priv pub : ByteArray) : Option ByteArray

end X25519
end HaclStar
