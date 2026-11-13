# conj-twist (fleet summary)

**Result.** Both `ConjTwistNontrivial` and `ConjTwistFromLeaves`, copied verbatim from
scratch/g10-odd/G10Odd.lean, are proved in Lean from leaves and two smaller named glue Props.
- `conjTwistNontrivial_of_surj : TateModuleFree → UniformizationExists → ArtinTorsionSurj →
  HomLinearLift → ConjAntiLift → ConjTwistNontrivial`.
- `conjTwistFromLeaves_of_surj : ArtinTorsionSurj → HomLinearLift → ConjAntiLift →
  ConjTwistFromLeaves`. T26 and T35 are already hypotheses of `ConjTwistFromLeaves`.

File: `scratch/conj-twist/ConjTwist.lean`. It has no `sorry`, and every `#print axioms` is
`[propext, Classical.choice, Quot.sound]`.

**What compiles (proved).**
- `faltingsV`: Faltings in ℚ_ℓ-form.
- complex conjugation moved to `cc ∈ Aut(K̄)`.
- The conjugate variety `conjVar A s`, the transport `c_*`, and its twisted equivariance.
  g10-odd listed these as missing.
- `toC_conjPt`: `c_*` is complex conjugation on points.
- The Artin comparison `ℤ_ℓ ⊗ Λ ↪ T_ℓ(A)` from N1 (`tateLatticeInj_of_artinTorsion`) and its
  naturality.
- `dim A^s = dim A` (`conjVarDim`).
- Injectivity of `A(K̄) → A(ℂ)` (`toC_injective`).
- The Faltings + rationality + holomorphy contradiction on lattice matrices.

**What remains.**
- Leaves: `FaltingsTate`, T26 and T35 (in the build), plus one new textbook leaf, `HomLinearLift`
  (T11(a) in Hom form, Birkenhake–Lange 1.2.1). It cannot be derived from T11a, which covers only
  End over ℂ.
- Glue, STANDARD and true:
  - `ArtinTorsionSurj`: torsion of `A(ℂ)` comes from `A(K̄)`, from T5 over K̄ and over ℂ.
  - `ConjAntiLift`: complex conjugation lifts to an injective antilinear map of uniformizations.

Report: docs/research/conj-twist.md; log: scratch/conj-twist/log.md.
