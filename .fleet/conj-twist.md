# conj-twist (fleet summary)

**Result.** Both `ConjTwistNontrivial` and `ConjTwistFromLeaves`, copied verbatim from
scratch/g10-odd/G10Odd.lean, are proved in Lean from leaves and four smaller named glue Props.
- `conjTwistNontrivial_of_lattice : TateModuleFree → UniformizationExists → ArtinTorsion →
  HomLinearLift → ConjAntiLift → TateLattice → ConjVarDim → ConjTwistNontrivial`.
- `conjTwistFromLeaves_of_lattice` is the same reduction without T26 and T35, which are already
  hypotheses of `ConjTwistFromLeaves`.

File: `scratch/conj-twist/ConjTwist.lean`. It has no `sorry`, and all 14 `#print axioms` are
`[propext, Classical.choice, Quot.sound]`.

**What compiles (proved).**
- `faltingsV`: Faltings in ℚ_ℓ-form.
- `conjData` / `exists_twist`: complex conjugation moved to `cc ∈ Aut(K̄)`.
- The conjugate variety `conjVar A s`, the transport `c_*` (`conjPt`/`conjT`/`conjV`), and its
  twisted equivariance `conjV_galRep`. g10-odd listed these as missing.
- `toC_conjPt`: `c_*` is complex conjugation at the level of points.
- Naturality of the Tate–lattice comparison (`homT_tateLattice`, `conjT_tateLattice`).
- The matrix/rationality contradiction `lattice_contradiction`.
- An intermediate route through `ConjBettiData` / `ConjBettiComparison`.

**What remains.**
- Leaves: `FaltingsTate`, T26 and T35 (all in the build), plus one new textbook leaf, N2
  `HomLinearLift`. This is T11(a) in Hom form (Birkenhake–Lange 1.2.1; it cannot be derived from
  T11a, which covers only End over ℂ).
- Glue, all STANDARD and true:
  - N1 `ArtinTorsion`: `A(K̄) → A(ℂ)` is injective and onto torsion, from T5.
  - N4 `TateLattice`: `T_ℓ ≅ Λ ⊗ ℤ_ℓ`. Purely algebraic from N1, so a good first target.
  - N3 `ConjAntiLift`: complex conjugation lifts to an injective antilinear map.
  - N5 `ConjVarDim`: `dim A^s = dim A`.

Report: docs/research/conj-twist.md; log: scratch/conj-twist/log.md.
