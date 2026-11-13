# g8-tate results log

## Step 0 (2026-11-13 09:03-09:18 PST): environment
- Merged origin/wip/local-glue (origin/wip/g8-object already in the base).
- `lake build` of the kernel modules imported by g8-object's and local-glue's files (incl.
  `ZInQKernel.Main`, `ZInQKernel.Contrib.AbVarBC.Dim`): 6 min, success.
- `build_prefix.sh` assembles `Prefix.lean` (10 791 lines, not committed: generated) =
  `scratch/g8-object/G8Object.lean` (verbatim) + `scratch/local-data/part_local.lean` (verbatim, in a
  `noncomputable section`) + local-glue's parts (verbatim, without `galois_block.lean`, whose text is
  already in G8Object.lean).
- Compile (VERIFIED): `lake env lean -o olean/Prefix.olean Prefix.lean`: 2m10s, 0 errors, no sorry;
  133 `#print axioms` reports, all `[propext, Classical.choice, Quot.sound]`.

## Step 1 (09:20-09:45 PST): tools and `LocalDataS` (part_tools.lean, part_local.lean)
- `ctail.sh F` compiles `F` against `olean/Prefix.olean` (`import Prefix`).
- New (namespace `G8Tate`): `padic_card_le` (`#ℚ_p ≤ 𝔠`), `padicAlgCl_card` (`#ℚ̄_ℓ = 𝔠`),
  **`exists_complex_equiv`** (`Nonempty (ℂ ≃+* ℚ̄_ℓ)`, Steinitz via Mathlib's
  `IsAlgClosed.ringEquiv_of_equiv_of_charZero`), **`exists_finGal_tame`** (`[E:ℚ_p] < p` ⟹ a finite
  Galois `F ⊇ E` with `p ∤ e(F)`), `T_prime`, `g7Clauses_of_g7Data` (G7Data's cochain clauses
  transported along `Φ : ℂ ≃+* ℚ̄_ℓ` are local-data's `G7Clauses`, with `[L:ℚ] ≤ D`),
  `descentPts_self` (`DescentPts A L` for `A` over `L`), `containsL_of_Lv`,
  **`localDataS_of_g7Data`**: R6 + I2-Tors + (`p = 2 →` `UnramRoots p ℓ`) + `p ≠ ℓ` + `G7Data` +
  `[L:ℚ] ≤ D` + `dim A = 2` ⟹ `G8Object.LocalDataS p L A ℓ β` (g8-object's text, unchanged).
- Compile (VERIFIED): `ctail.sh Part.lean` (= part_tools + part_local): exit 0, 49 s, no sorry;
  axioms of `exists_complex_equiv`, `exists_finGal_tame`, `g7Clauses_of_g7Data`, `descentPts_self`,
  `localDataS_of_g7Data`: `[propext, Classical.choice, Quot.sound]`.

## Step 2 (09:50-10:05 PST): `LinkedTateObjS` reduced to `TateBridgeOnL` (part_link.lean)
- New: `TateBridgeOnL` (def, GLUE): the text of g8-object's `LinkedTateObjS` with its two
  `LocalDataS` conjuncts deleted (produced by a python string replacement from `part_split.lean`).
- **`linkedTateObjS_of_onL`**: R6 + I2-Tors + `UnramRoots 2 5` + `TateBridgeOnL` ⟹
  `G8Object.LinkedTateObjS`. `dim A = 2` from `G7Out`'s `dim A_{L'} = 2` and the kernel's
  `PkgI3.AbVar.dim_baseChange` (`ZInQKernel/Contrib/AbVarBC/Dim.lean`).
- **`linkedTateDataD_of_onL`**: + T7 ⟹ `G8Object.LinkedTateDataD` (via g8-object's
  `linkedTateDataD_of_S`).
- Compile (VERIFIED): `ctail.sh Part.lean` (= part_tools + part_local + part_link): exit 0, 60 s;
  all axiom reports `[propext, Classical.choice, Quot.sound]`, no sorry.
