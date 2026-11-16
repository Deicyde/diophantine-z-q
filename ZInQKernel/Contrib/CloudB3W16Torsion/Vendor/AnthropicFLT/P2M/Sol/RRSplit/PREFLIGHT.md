# Historical preflight summary — not proof compilation

These recorded preliminary checks used Lean 4.35.0 on the restored source base
`2dc949d688c407e32823c4e751679d66b2f40e65`. They were limited to dependency and
namespace availability, used one thread, and were serialized with a build lock.
They did not establish any of the six solution proofs by themselves.

Seven definition prerequisites compiled with exit status zero:
`Def_ModularCurve_CanonicalDivisor`,
`Def_ModularCurve_CanonicalDivisorUniformizer`,
`Def_AlgebraicCurve_Repartitions`, `Def_AlgebraicCurve_AdelicIndex`,
`Def_AlgebraicCurve_CanonicalDivisor`, `Def_AlgebraicCurve_LocalResidue`, and
`Def_AlgebraicCurve_RiemannRochRows`.
The maximum recorded RSS among those checks was 6,919,144 KiB.

Two preliminary scratch checks also succeeded: 375 root export targets were
checked for availability, and the 344-line command prefix of the first RR part
was checked before its first mathematical declaration. These are availability
checks, not full proof compilation or axiom reports.

The complete six-edge proof checks were performed later and are summarized in
`VERIFICATION.md`. Labeled selections of the final type and axiom output are in
`Compile/PUBLIC_TYPE_AXIOM_EXCERPTS.md`. Full original preflight stdout and timing
records remain preserved unchanged privately and are not included in this public
tree. No modified or abbreviated output is described here as a raw transcript.

For generic local reproduction instructions, see `REPRODUCING.md`; those examples
are not the original verification command transcript.
