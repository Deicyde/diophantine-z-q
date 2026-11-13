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

## Step 1 (09:18-09:27 PST): tools and `LocalDataS` (part_tools.lean, part_local.lean)
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

## Step 2 (09:27-09:30 PST): `LinkedTateObjS` reduced to `TateBridgeOnL` (part_link.lean)
- New: `TateBridgeOnL` (def, GLUE): the text of g8-object's `LinkedTateObjS` with its two
  `LocalDataS` conjuncts deleted (produced by a python string replacement from `part_split.lean`).
- **`linkedTateObjS_of_onL`**: R6 + I2-Tors + `UnramRoots 2 5` + `TateBridgeOnL` ⟹
  `G8Object.LinkedTateObjS`. `dim A = 2` from `G7Out`'s `dim A_{L'} = 2` and the kernel's
  `PkgI3.AbVar.dim_baseChange` (`ZInQKernel/Contrib/AbVarBC/Dim.lean`).
- **`linkedTateDataD_of_onL`**: + T7 ⟹ `G8Object.LinkedTateDataD` (via g8-object's
  `linkedTateDataD_of_S`).
- Compile (VERIFIED): `ctail.sh Part.lean` (= part_tools + part_local + part_link): exit 0, 60 s;
  all axiom reports `[propext, Classical.choice, Quot.sound]`, no sorry.

## Step 3 (09:30-09:50 PST): Prefix2 (unram-tate's Tate-functor construction, linked-tate's linked data)
- `build_prefix2.sh` assembles `Prefix2.lean` (`import Prefix`) = linked-tate's
  `parts/96_unramtate.lean` (= unram-tate's `TateBridge.lean` L1038-1825 verbatim) without its copy
  of BCPoints.lean (identical text already in Prefix as local-glue's `bc_block.lean`, namespace
  `UnramTate`) + linked-tate's `parts/97_linkeddata.lean` L1-445 (`scalarTransferQ`, `tmOf`,
  `LinkedFrobRam`, `LinkedFrob`, `LinkedRam`, `linkedFrobRam_of`, `linkedTateCoreDR_of`; without the
  two Leaves-layer composites).
- Compile (VERIFIED): `lean -o olean/Prefix2.olean Prefix2.lean`: 1m11s, 0 errors.
  (linked-tate's Leaves-layer parts compile unchanged over the kernel-layer Prefix.)

## Step 4 (09:32-09:42 PST): `OnL` for the canonical operators (part_onl.lean)
- New: `VX`, `tateMapX_comp`, `tateMapX_id`, `opV_conjE` (`opV(Ξ f Ξ⁻¹) = V(Ξ) opV(f) V(Ξ)⁻¹`),
  `VX_comp_symm`, `VXe`, `exists_equiv_of_quasiInv` (`f g = λ·1`, `g f = μ·1` ⟹ `f` invertible),
  `m_one` (`m 1 = id` from `DescentDatum`'s clauses), **`onL_canon`**: for any descent datum `m`
  (clauses of `DescentDatum`), transport `Θ`, `h`, and scalars `= 1` on `G_L`,
  `∃ ψ, G8Object.OnL L A (tmOf hLL' A Θ h m ℓ) aℓ ψ`. `ψ⁻¹ = opV(m_x) ∘ V(Θ ∘ trPt φ₁)`,
  `φ₁ : L̄ ≃ₐ[L] ℚ̄`, `x = h g₁⁻¹`, `g₁ = φ₁ ∘ (embedding ℚ̄ → L̄ of resQ)`.
- Compile (VERIFIED): `ctail.sh Part2.lean` (`import Prefix2` + part_onl): exit 0; axioms of
  `opV_conjE`, `exists_equiv_of_quasiInv`, `onL_canon`: `[propext, Classical.choice, Quot.sound]`.
  (`set_option maxHeartbeats 1000000 in` on `onL_canon`, as linked-tate's `linkedTateCoreDR_of`.)

## Step 5 (09:42-09:48 PST): `TateBridgeOnL` proved (part_tb.lean)
- `assemble.sh` builds the iteration file `Tail.lean` (`import Prefix2` + parts 1-5).
- New: `EndRank4` (def, GLUE: `rank_ℤ End(A_{L'}) = 4` for every fibre context and G7 datum;
  linked-tate derives it from `FibreSimple` + `QMEndRank` over Leaves.lean, not re-checked here),
  `exists_preimage` (algebraic `z ∈ ℂ` is in the image of any `κ : ℚ̄ → ℂ`), `beta_pow_eq_one`,
  `beta_conj` (`β(hkh⁻¹) = β(k)` for `k ∈ H` when `ε` is normalized on `H`),
  **`tateBridgeOnL_of`**: T26 (`PkgI3.TateModuleFree`) + `EndRank4` + linked-tate's
  `UnramTate.LinkedFrob` ⟹ `TateBridgeOnL`. Data: unram-tate's `tatePoints` `(Θ, h)`, G7Data's
  descent datum, `Tm_ℓ = tmOf … ℓ`, `γ₀` from `scalarTransferQ`, `βQ = κ⁻¹ ∘ β`,
  `aQ g = βQ g / γ₀(hgh⁻¹)`, `ε_ℓ = ∂(j_ℓ ∘ βQ)`, `j_ℓ = IsAlgClosed.lift`; the `key` block of
  linked-tate's `linkedTateCoreDR_of` copied with these scalars; `OnL` from `onL_canon`;
  `dim A_{L'} = 2` proved (`PK.surface`, kernel `dim_baseChange`).
- **`linkedTateObjS_of_frob`**: R6 + I2-Tors + `UnramRoots 2 5` + T26 + `EndRank4` + `LinkedFrob`
  ⟹ `G8Object.LinkedTateObjS`; **`linkedTateDataD_of_frob`**: + T7 ⟹ `G8Object.LinkedTateDataD`.
- Compile (VERIFIED): `ctail.sh Tail.lean`: exit 0, 0 errors, no sorry; all axiom reports
  `[propext, Classical.choice, Quot.sound]` (incl. `tateBridgeOnL_of`, `linkedTateObjS_of_frob`,
  `linkedTateDataD_of_frob`).

## Step 6 (09:48-09:55 PST): flat check file
- `build_flat.sh` writes `G8Tate.lean` (12 857 lines) = `Prefix.lean` + `Prefix2.lean` + `Tail.lean`
  (imports first). Committed; the intermediate files are regenerated by the scripts.
- Compile (VERIFIED): `lake env lean scratch/g8-tate/G8Tate.lean`: 5m30s (load ~47), 0 errors,
  no sorry; 147 `#print axioms` reports, all `[propext, Classical.choice, Quot.sound]`.

## Step 7 (10:00 PST): `EndRank4` weakened
- Premise `Module.finrank ℚ L ≤ ZInQ.heightD` added to `EndRank4` (weaker hypothesis; the consumer
  `tateBridgeOnL_of` has it). Compile (VERIFIED): `ctail.sh Tail.lean` exit 0, 0 errors, 14 axiom
  reports, all standard.

## Step 8 (09:58-10:05 PST): review, flat re-check
- One read-only model review of the report and parts. Findings: the `EndRank4` edit was not yet
  in the flat file (re-checked below); cross-reference §3→§2; the `TateBridge35` row should say
  `TateBridgeOnL` (premises differ); stale committed iteration files `Part.lean`, `Part2.lean`
  (removed, gitignored). Confirmed: `TateBridgeOnL` = `LinkedTateObjS` minus the two `LocalDataS`
  conjuncts (diffed); `EndRank4` follows from linked-tate's `FibreSimple` + `QMEndRank` by its
  `linkedTateCore_of` argument; `LinkedFrob` applied to the right data; counts.
- Compile (VERIFIED): `lake env lean scratch/g8-tate/G8Tate.lean` (12 858 lines): 3m40s, 0 errors,
  no sorry; 147 axiom reports, all `[propext, Classical.choice, Quot.sound]`.
