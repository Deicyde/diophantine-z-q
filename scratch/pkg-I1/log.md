# pkg-I1 results log

Marks: VERIFIED (read in a source, computed, or compiled), STANDARD (published, exact reference),
SPECULATIVE. Locators from memory: UNVERIFIED.

## Step 0 (setup)
- Sources read: wk-h.md §§1-6, h-trust.md A1-A10 and F1, h-cm.md summary, N5 L377-528 (datum, degree,
  integral model), L532-543 (Igusa vector), L908-927 (theta formula); scratch/h-v14/igusa_check.py,
  scratch/rv-up/theta24.py; prereq-survey rows A2-A10, F1.
- Mathlib v4.35.0 has: `QuaternionAlgebra R c₁ c₂ c₃` (i² = c₁ + c₂ i, j² = c₃), the `GL (Fin 2) ℝ`
  action on `ℍ` (`UpperHalfPlane.glAction`), `Matrix.symplecticGroup`, `tsum`, `MeromorphicOn`.
  No Siegel upper half space, Siegel theta constants, Igusa invariants, hyperelliptic curves,
  abelian varieties with endomorphisms/polarizations, Shimura curves (VERIFIED, grep).
