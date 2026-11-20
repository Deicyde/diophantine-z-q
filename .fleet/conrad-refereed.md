# Conrad row reduction

**Manuscript normalization issue, tex 765–767.** The power-zero comparison
requires the arithmetic modular normalization. With geometric modular weights
it gives one extra cyclotomic power before conversion to the Tate-module form.
This is a separate issue from the local Artin normalization.

The exact C8 row reduces to Serre's Ch. III Appendix A6 equivalence at the
arithmetic Artin map of the finite extension itself (locator **UNVERIFIED**).
The norm rewrite and both Hodge–Tate multiplicity comparisons are in Lean.
See [the report](../docs/research/conrad-refereed.md).

**Result.** `HDec.G0Galois.C8Conrad.conradAppB_of_refereed` proves both
`ConradAppBQp` and `ConradPropB3Qp` from `SerreA6Prop6`. In the row's local
normalization, the cyclotomic character has weight (+1) and its Artin formula
on units has exponent (-1). Both directions agree with this sign. The input
uses the integer units at the ground field itself; the descent through the norm
and the comparison of invariant dimensions are proved.

**Verification.** Lake built all nine new modules. All 42 theorem checks use
only `propext`, `Classical.choice` and `Quot.sound`. The focused scan reports
one discharge of `conradAppB`, assuming only `SerreA6Prop6`.
See [the results log](../scratch/conrad-refereed/log.md) for the exact output.

**Remains.** The reviewer should verify the printed locator and transcription;
the lead can then fold the adapter. The existing open-row bundle was not
edited.

Proof commit: `0a3a0e8eadec67c86f9e1e96dbee467e33fd6b11`. Verification and report commit: `d3d1e53e6297521197d043e9b17ffad650b823f9`.
Final handoff SHA: `git log -1 --format=%H -- .fleet/conrad-refereed.md`
(resolves the commit that adds this note).
