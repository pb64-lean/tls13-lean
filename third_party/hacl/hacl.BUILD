# Build overlay for the @hacl http_archive (hacl-star dist/, gcc-compatible).
#
# This exposes ONLY the portable, scalar translation units required by the
# TLS 1.3 cipher suite TLS_CHACHA20_POLY1305_SHA256 with X25519/P-256 key
# exchange and P-256/Ed25519 server-signature verification:
#
#   SHA-256/384/512  Hacl_Hash_SHA2.c
#   HMAC-SHA256      Hacl_HMAC.c        (agile core; see hash family below)
#   HKDF-SHA256      Hacl_HKDF.c
#   X25519           Hacl_Curve25519_51.c        (portable 51-bit limbs)
#   P-256 ECDH/ECDSA Hacl_P256.c
#   Ed25519 verify   Hacl_Ed25519.c
#   ChaCha20-Poly1305  Hacl_AEAD_Chacha20Poly1305.c + Hacl_Chacha20.c
#                      + Hacl_MAC_Poly1305.c      (scalar variants)
#
# Hacl_HMAC.c routes through an agile hash core that references every hash HACL
# supports, so its object drags in the full hash family at link time even though
# TLS only calls the SHA-256 entry point. Those extra units are all portable C,
# so we compile them rather than fight the linker:
#
#   Hacl_Hash_Blake2b.c Hacl_Hash_Blake2s.c Hacl_Hash_MD5.c
#   Hacl_Hash_SHA1.c    Hacl_Hash_SHA3.c    Lib_Memzero0.c
#
# Vale assembly, EverCrypt CPU autodetection, bignum, and the SIMD (128/256)
# variants are deliberately excluded: they are not needed for this suite and the
# scalar files build identically across x86-64 and arm64.
#
# The exact set and include roots were determined empirically by compiling and
# running a known-answer harness against the pinned commit.

package(default_visibility = ["//visibility:public"])

_INCLUDE_ROOTS = [
    "gcc-compatible",
    "karamel/include",
    "karamel/krmllib/dist/minimal",
]

cc_library(
    name = "hacl",
    srcs = [
        "gcc-compatible/Hacl_Hash_SHA2.c",
        "gcc-compatible/Hacl_HMAC.c",
        "gcc-compatible/Hacl_HKDF.c",
        "gcc-compatible/Hacl_Curve25519_51.c",
        "gcc-compatible/Hacl_Ed25519.c",
        "gcc-compatible/Hacl_P256.c",
        "gcc-compatible/Hacl_AEAD_Chacha20Poly1305.c",
        "gcc-compatible/Hacl_Chacha20.c",
        "gcc-compatible/Hacl_MAC_Poly1305.c",
        # Hash family pulled in transitively by Hacl_HMAC's agile core.
        "gcc-compatible/Hacl_Hash_Blake2b.c",
        "gcc-compatible/Hacl_Hash_Blake2s.c",
        "gcc-compatible/Hacl_Hash_MD5.c",
        "gcc-compatible/Hacl_Hash_SHA1.c",
        "gcc-compatible/Hacl_Hash_SHA3.c",
        "gcc-compatible/Lib_Memzero0.c",
    ],
    hdrs = glob([
        "gcc-compatible/*.h",
        "gcc-compatible/internal/*.h",
        "karamel/include/**/*.h",
        "karamel/krmllib/dist/minimal/*.h",
    ]),
    # karamel output leaves some helper parameters unused; these are not real
    # defects and would otherwise fail -Werror builds.
    copts = [
        "-Wno-unused-parameter",
        "-Wno-unused-but-set-variable",
    ],
    includes = _INCLUDE_ROOTS,
)
