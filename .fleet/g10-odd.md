# g10-odd (G10Glue, oddness of r_ℓ): summary

**Result:** `G10Glue` (verbatim from scratch/g0-mod-galois/part_galois.lean) is **proved in Lean
from one strictly smaller named glue Prop**: `G0Galois.g10Glue_of_conjTwist :
ConjTwistNontrivial → G10Glue`. `ConjTwistNontrivial` says that complex conjugation does not
act trivially by conjugation on `ρ_ℓ(G_K)` for an abelian surface `A/K`, `K` Galois. It
assumes only `PkgI3.FaltingsTate` and mentions neither `r` nor `e`. It is STANDARD glue
(Faltings + Artin comparison + holomorphy, N5 L742-751), with the proof written out in
docs/research/g10-odd.md.

**Defect (not a falsity):** `G10Glue`'s hypotheses `HSyn.T11_RiemannGAGA` and
`HSyn.T12_ArtinComparison` are `opaque` placeholders, inert in any proof. The corrected
statement is `G10GlueConcrete`: the same conclusion, with the concrete leaves T11a, T11b, T35
(ZInQKernel/HDecomp/LeafPush2/T.lean), T5 and T26. It is proved from `ConjTwistFromLeaves`.

**Also proved (compiled, standard axioms only):**
- algebra: a 2×2 involution other than ±1 has det −1; complex conjugations are involutions;
- `G10Glue ⇐ T12K_ComplexConjEigen ∧ ConjTwistOutside`, where T12K is a number-field T12
  (glue target); `t12_of_t12K` shows that T12K implies the existing `T12_ComplexConjEigen`;
- the totally real case from T12K alone;
- `betti_skeleton` / `betti_skeleton_fd`, the linear-algebra core of the Faltings/Artin/holomorphy
  argument (`(W⊗E) ∩ U = W`; holomorphic plus antiholomorphic gives 0);
- `exists_resQ_conj`: for `K/ℚ` Galois, `G_K` is normal in `G_ℚ` through `resQ`, so the
  twist condition in `ConjTwistNontrivial` is not vacuous.

**Findings:** `T12_ComplexConjEigen` over ℚ cannot replace Faltings when `c ∉ G_K` (Weil
restriction loses the information). Under G10Glue's QM hypotheses `K` has no real place
(Shimura's argument), so in the application the content is entirely `ConjTwistOutside`.

**Compiles:** `lake env lean scratch/g10-odd/G10Odd.lean` (681 lines, after building
`ZInQKernel.HDecomp.LeafPush2.T` and `ZInQKernel.HDecomp.I3Linalg.C2`): no errors, no `sorry`;
`#print axioms` gives [propext, Classical.choice, Quot.sound] for the eight main theorems.

**Remains:** `ConjTwistNontrivial`. It needs the conjugate variety `A^c` (base change along an
automorphism of `K`), `c_*` on Tate modules, the Artin comparison over a number field
compatible with `c_*`/`F_*`, and the instantiation of `betti_skeleton_fd`. T12 needs the same
infrastructure.
Integration: in GaloisPieces (scratch/g0-mod-galois/part_bundle.lean) replace `odd : G10Glue` by `odd : ConjTwistNontrivial` and pass `g10Glue_of_conjTwist m.odd`.
