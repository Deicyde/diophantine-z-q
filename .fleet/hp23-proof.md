# hp23-proof — fleet summary

**Verdict: `hP23 = H29Split.TYZProp23Printed` is PROVED outright** (TYZ Prop. 2.3, first assertion: `f_n(h²)` odd).
The statement is unchanged, no leaf is added, and the theorem uses only the standard axioms. Target met:
hP23 removed, LEAF count −1, GLUE unchanged.

* Theorem: `ZInQ.Contrib.HP23Proof.tyzProp23Printed : ZInQ.Contrib.TYZDecomp.H29Split.TYZProp23Printed`, in
  `ZInQKernel/Contrib/OneProof/TYZProp23Printed.lean`; helpers in `ZInQKernel/Contrib/OneProof/HP23Proof/`
  (`Good`, `Generic`, `Case1`, `Case3`). Finite checks use `decide +kernel` only (three small ones). A grep of
  the new files finds no native_decide, sorry, axiom or #eval.
* Proof:
  * Every test vector is `±F` on TYZ's 8 double cosets. This follows from the partition data of hfx-proof's
    `testVector_of_partition`.
  * For n ≡ 3, F ∈ {−3, 1}, so every value is odd.
  * For n ≡ 1, F = ±1 on the classes with χ₀ = 1 and F = 0 on the others. Squares lie in χ₀ = 1 classes,
    via the reduced-norm invariant `2^ℤ(1+4ℤ₂)` at 2 together with even valuations of `nrd γ` at the odd
    primes.
* Compiles:
  * `lake build ZInQKernel.Contrib.OneProof.TYZProp23Printed` succeeds.
  * `#discharges` reports: `DISCHARGES [hP23] by ZInQ.Contrib.HP23Proof.tyzProp23Printed`, still assumes [],
    axioms [propext, Classical.choice, Quot.sound] (scratch/hp23-proof/Discharges-output.txt).
  * The manual fold `scratch/hp23-proof/FoldCheck.lean` compiles with the standard axioms:
    `frozenTarget_noP23`, and `frozenTarget_noHfxP23` (also drops hfx, using hfx-proof's theorem).
* What remains (for the integrator): import the theorem in Main.lean, drop the `hP23` binder (and `hfx`),
  remove the hP23 rows from kinds.tsv, claims.tsv and frontier-crosswalk (T-23), and regenerate OPEN.md.
  The proof depends on hfx-proof's `HfxProof/*` and t21-proof's `T21Proof/*` (both already in this branch).
* Report: docs/research/hp23-proof.md. Log: scratch/hp23-proof/log.md.
