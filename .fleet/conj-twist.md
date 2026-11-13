# conj-twist (fleet summary)

**Result.** Both `ConjTwistNontrivial` and `ConjTwistFromLeaves`, copied verbatim from
scratch/g10-odd/G10Odd.lean, are proved in Lean.
- `conjTwistFromLeaves_final'' : HomLinearLift → TwistCEval → ConjTwistFromLeaves`.
  T5, T26 and T35 are already hypotheses of `ConjTwistFromLeaves`.
- `conjTwistNontrivial_final'' : TorsionStructure (T5) → TateModuleFree (T26) →
  UniformizationExists (T35) → HomLinearLift → TwistCEval → ConjTwistNontrivial`.
  Faltings is a hypothesis inside `ConjTwistNontrivial`.

File: `scratch/conj-twist/ConjTwist.lean` (1922 lines). It has no `sorry`, and all 36
`#print axioms` are `[propext, Classical.choice, Quot.sound]`.

**What compiles (proved).**
- Faltings in ℚ_ℓ-form, and `c ∈ G_ℚ` as an involution `cc` of K̄.
- The conjugate variety `A^s` (Over.pullback), the transport `c_*` on points, T_ℓ and V_ℓ, and its
  twisted equivariance.
- `dim A^s = dim A`.
- `A(K̄) → A(ℂ)` is injective (Mathlib's `ext_of_isDominant_of_isSeparated`) and bijective on
  torsion (counting via T5 and a lattice).
- The Artin comparison `ℤ_ℓ ⊗ Λ ↪ T_ℓ(A)` and its naturality for homomorphisms and for `c_*`.
- The antilinear lift of complex conjugation, built from N2.
- The Faltings, rationality and holomorphy contradiction on integer lattice matrices.

**What remains.**
- One new textbook leaf, `HomLinearLift`: T11(a) in Hom form, Birkenhake–Lange 1.2.1. It cannot
  be derived from T11a, which covers only End over ℂ.
- One glue Prop, `TwistCEval`, purely scheme-theoretic with no analysis. For a number field,
  opens and sections of `A^s` correspond to those of `A` (`A^s → A` is an isomorphism), with
  `f(twistC Q) = conj(f'(Q))`. It is STANDARD and true.
- The analytic part is proved, including `differentiableOn_conj_conj`: `z ↦ conj(F(z̄))` is
  holomorphic.

Report: docs/research/conj-twist.md; log: scratch/conj-twist/log.md.
