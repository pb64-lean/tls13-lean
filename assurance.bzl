"""Shared axiom policy for tls13-lean's `lean_assurance_test` targets.

Every first-party constant in this repository closes over exactly the three
axioms the Lean standard library itself relies on, and nothing else. There is
no `sorry`, no `native_decide`, and no LRAT certificate anywhere in the
trusted surface: the byte (de)composition identities in `Tls.Record.Laws` and
`Tls.Handshake` are proved arithmetically rather than by `bv_decide`, so no
generated LRAT-certificate axiom (`<lemma>._native.bv_decide.ax_1_5`) exists
to allow. Introducing one — by reaching for `bv_decide` in a proof any
audited constant depends on — fails every assurance target and forces the
choice to be made deliberately here.
"""

TLS13_LEAN_ALLOWED_AXIOMS = [
    "propext",
    "Classical.choice",
    "Quot.sound",
]
