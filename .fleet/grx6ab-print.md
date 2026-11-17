# grx6ab-print (2026-11-16): `gonzalezRotgerX6Ab` from two printed leaves, one object each (−1 GLUE)

**Result.** The composite field `gonzalezRotgerX6Ab` (GLUE: "asserts the witness R1fpPropsAb plus X6Props") is
proved in Lean (`GRX6AbPrint.gonzalezRotgerX6Ab_of_print`, `ZInQKernel/Contrib/OneProof/GRX6AbPrint.lean`) from:
* `GRDict.GonzalezRotgerThm512X6` (gr-dict's statement): GR, JMSJ 58 (2006) Thm 5.12, p. 946 (locator VERIFIED in
  locators.md). Every witness, GR's own CM points. **Printed form.**
* `GRX6AbPrint.X6CoarseModuli` (new): X0(6,1)/ℚ is a proper smooth curve and a coarse moduli scheme for QM abelian
  surfaces. Clauses: Galois-equivariant bijection on ℚ̄-points, Atkin–Lehner twists, classifying map of a level-3
  family over a proper smooth curve. **Printed form with reading risk.** The locators (Shimura 1967, Deligne
  Bourbaki 389, Buzzard 1997) are UNVERIFIED, and the Atkin–Lehner action is read in its twist form.
* the existing field `shimuraMainThmIDeligneY3AbU` (supplies Y₃ with R1fpPropsAb), plus the textbook fields
  `gagaMorphism` and `mumfordTorsionAlgClosed`.
The H-168 shape (Y₃, X₆ and the forgetful map in one ∃) is now glue proved in Lean: `x6ModuliWitness_of_coarse`
builds fY as the classifying map of Y₃'s universal family. The converse `x6CoarseModuli_of_witness` shows the new
leaf is never stronger than the witness it replaces.

**Compiles (VERIFIED).** GRX6AbPrint.lean on main c1e4ed1b + gr-dict, standard axioms. Main and Discharges build.
`#discharges`: gonzalezRotgerX6Ab is discharged by `gonzalezRotgerX6Ab_of_print`
(scratch/grx6ab-print/discharges.txt). Spec scratch/grx6ab-print/autofold.json: dry run strict 16/21 → 18/20 (−1);
FoldCheck.lean compiles. Combined with elkies-print (merged; its witness taken from `x6ModuliWitness_of_coarse`):
autofold-combined.json gives 16/21 → 19/19 (−2); FoldCheckCombined.lean compiles.

**Remains.** A statement check of X6CoarseModuli, with a locators.md row (proposed in report §7). Thm 5.12 and the
coarse-moduli theorem are not formalized. shimuraMainThmIDeligneY3AbU stays composite. For the integrator: fold
this before elkies-print, or use the combined spec; it supersedes gr-dict's X6 spec.
Report: docs/research/grx6ab-print.md; log: scratch/grx6ab-print/log.md.
