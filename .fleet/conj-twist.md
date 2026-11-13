# conj-twist (fleet summary)

**Result.** Both `ConjTwistNontrivial` and `ConjTwistFromLeaves`, copied verbatim from
scratch/g10-odd/G10Odd.lean, are proved in Lean with no glue left.
- `conjTwistFromLeaves_of_homLinearLift : HomLinearLift → ConjTwistFromLeaves`.
- `conjTwistNontrivial_of_leaves : TorsionStructure (T5) → TateModuleFree (T26) →
  UniformizationExists (T35) → HomLinearLift → ConjTwistNontrivial`. Faltings is a hypothesis
  inside `ConjTwistNontrivial`.
- Corollaries:
  - `g10GlueConcrete_of_homLinearLift : HomLinearLift → G10GlueConcrete`;
  - `g10Glue_of_leaves : T5 → T26 → T35 → HomLinearLift → G10Glue`.

`G10Glue` and `G10GlueConcrete` are copied verbatim from g10-odd.

**The one new leaf.** `HomLinearLift` is T11(a) in Hom form (Birkenhake–Lange 1.2.1 plus
holomorphy of algebraic maps; theorem numbers UNVERIFIED): a homomorphism of abelian varieties
over K lifts along analytic uniformizations (`IsUniformization`, as in T35) to a ℂ-linear map. It
cannot be derived from T11a, which covers only End over ℂ.

**What compiles.** `scratch/conj-twist/ConjTwist.lean` (2226 lines). It has no `sorry`, and all
41 `#print axioms` are `[propext, Classical.choice, Quot.sound]`. Proved there:
- Faltings in ℚ_ℓ-form.
- The conjugate variety `A^s` (Over.pullback), `c_*` on points, T_ℓ and V_ℓ, and its twisted
  equivariance.
- `dim A^s = dim A`.
- `A(K̄) → A(ℂ)`: injective, and bijective on torsion via T5.
- The Artin comparison `ℤ_ℓ ⊗ Λ ↪ T_ℓ(A)` and its naturality.
- Antiholomorphy of complex conjugation on `A^s`: values of sections at twisted points are
  conjugates (ΓSpecIso naturality), and `z ↦ conj(F(z̄))` is holomorphic.
- The antilinear lift built from N2.
- The Faltings, rationality and holomorphy contradiction on integer lattice matrices.

**What remains.** Only the leaves: Faltings, T5, T26 and T35 (all in the build) and the new
`HomLinearLift`. Integration: replace `odd : G10Glue` in GaloisPieces by `HomLinearLift`.

Report: docs/research/conj-twist.md; log: scratch/conj-twist/log.md.
