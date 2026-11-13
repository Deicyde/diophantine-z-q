# g12-det (fleet note)

**I closed all three targets.** `ResQFiniteIndex` is proved, `DetTate` is proved from leaves,
and `G12Weight` is proved from two new leaves. Every glue step is proved in Lean: no `sorry`,
and every theorem uses only `[propext, Classical.choice, Quot.sound]`. Full report:
`docs/research/g12-det.md`. Log: `scratch/g12-det/log.md`.

- **`ResQFiniteIndex`** (`ResQ.lean`, Mathlib only). `ℚ̄ → K̄` is bijective, so `Fix(K') ≤
  range(resQ K)` where `K'` is the image of `K` in `ℚ̄`. The index of `Fix(K')` is `[K:ℚ]`.
- **`DetTate`** (`DetLeaves.lean`) follows from weil-pairing's leaves `T09_SymmIsogenyExists`,
  `IsogenyQuasiInverse`, `DivisiblePoints` and T26 (`PkgI3.TateModuleFree`). The steps:
  - `Darboux` (symplectic bases) is proved.
  - `det = cⁿ` for a symplectic similitude follows from Mathlib's `SymplecticGroup.det_eq_one`.
    This settles the Pfaffian sign that weil-pairing's `det² = χ^{2g}` left open.
  - The `ℤ_ℓ`-pairing on `T_ℓ` extends to `V_ℓ`.
  - The cyclotomic character of `K̄` is compared with that of `ℚ̄` along `resQ`.
- **`G12Weight`** (`Weight.lean`) follows from the two new leaves `SenTwist` (Sen 1980) and
  `FiniteImageHT` (Tate 1967 with Ax–Sen–Tate), plus the R13, R14, R15, T18 and T19 that
  `G12Weight` already takes. Proved glue: `TwistExists`, `TwistConj` (from T18 and
  Brauer–Nesbitt), `HTConj` and `HTExtend`. The last two are invariance of `PkgI4.htMult` under
  conjugation and under enlarging the coefficient field. Finding: for `k ≥ 1`, the conclusion of
  `G12Weight` is equivalent to `k = 2`. No statement was changed.
- **Integration** (`Integrate.lean`, built from g0-mod-galois's own `ModGalois.lean` without any
  copies): `galoisPieces_of` and `g8_g12_of_leaves'` compile with 0 errors. This leaves the G8-G12
  range with two pieces of glue, `G9Glue` and `G10Glue`.
- **Model review** (read-only subagent): every new Prop is true and non-vacuous, and neither leaf
  is stronger than its source.
- **What remains:** a primary-source check of the theorem numbers for `SenTwist` and
  `FiniteImageHT`; registering them as leaves; replacing the fields `weight`, `detTate` and
  `finIndex` of `GaloisPieces` (g0-mod-galois) with the proofs above.
