# g15-ram results log

## Step 1 (2026-11-13 04:20 PST): statements
- `scratch/g15-ram/G15Ram.lean` §0: verbatim copies of `ModData`, `U0`, `LocalRamG`, `G15RamG`
  (scratch/g0-mod-newform/NewForm.lean 1684-1690, 2037, 2448-2464) and `G0Galois.G11Out`
  (scratch/g0-mod-galois/part_galois.lean 164).
- §1: named Props `HilbertSerreLadic`, `UpperBreakFix`, `UpperWild`, `WildFixTame` (closed,
  local fields), `TwistShape`, `TwistUpper`, `TwistTame`, `SmallPrimeData`, `LargePrimeData`,
  `LocalData` (on G8's data).
- Compile: `lake env lean scratch/g15-ram/G15Ram.lean` exit 0, no output (VERIFIED, 7 s, after
  `lake build` of the six imported kernel modules).
- Finding F1 (VERIFIED, logical): `G15RamG D u` is a predicate on `D : ModData L A`, whose fields
  are bare representations; for arbitrary `D` it is false (take `r5` with a wildly ramified
  finite-order twist). So it cannot be proved as a closed statement; it is proved here from Props
  on the same `D` (G8's construction) and closed local-field Props.

## Step 2 (04:25-04:32 PST): reduction and local-field proofs
- `G15Ram.lean` §2 `upperBreakFix_of_hilbertSerre : HilbertSerreLadic p → UpperBreakFix p`
  (proved): `G^t_{ℚ_p} ⊆ G_F` for `t > 4a²` when `e(F/ℚ_p) ≤ a!`. Uses the kernel's
  `GlueConductor.upper_break_le` (D1 arithmetic), and new lemmas on `LadicCond.phiAt`:
  integrand antitone (so interval integrable), `phi_mono`, slope `≤ 1` on `[0,∞)`
  (`phi_sub_le`), `φ(u) ≥ u/g₀` (`phi_ge`), `φ(m) = ∑_{k<m} g_{k+1}/g₀` (`phi_nat`), and the
  `sInf` computation of `ψ(t) > n − 1` with `n` minimal such that `G_n` fixes `F`.
- §2b `upperWild : UpperWild p` (proved, no hypothesis): for `t > 0`, `G^t_{ℚ_p} ⊆ P_p`.
  `F` = Mathlib's `FiniteGaloisIntermediateField.adjoin ℚ_p {x}`; `ψ_F(t) ≥ t > 0` gives
  `σ ∈ G_1(F)`; `|F^×| = |ϖ|^ℤ` (from `IsUnif` and `exists_mem_Ioc_zpow`); the set of `y` with
  `‖σy − y‖ < ‖y‖` is closed under products (ultrametric, `PadicAlgCl.isUltrametricDist`) and
  inverses.
- §3 `localRamG_of`, `g15RamG_of_pieces`, `g15RamG_of_hilbertSerre` (proved).
- Compile: `lake env lean scratch/g15-ram/G15Ram.lean` exit 0, 0 errors, no sorry
  (`scratch/g15-ram/compile.out`); `#print axioms` = [propext, Classical.choice, Quot.sound] for
  `upperBreakFix_of_hilbertSerre`, `g15RamG_of_pieces`, `g15RamG_of_hilbertSerre`, `upperWild`
  (VERIFIED, ~8 s).
- Sanity (VERIFIED by inspection of the definitions): `LocalData p r` is satisfiable (trivial
  `r`, `F = ⊥`, `β = 1`), so the hypotheses are not contradictory.
- Finding F2 (logical, VERIFIED): `LargePrimeData p r` follows from clause (ii) itself with
  `F = ⊥`, `β = 1`; so at `p > D` the reduction only isolates the local-field fact
  `WildFixTame`. At `p ≤ D`, `SmallPrimeData` is not implied by clause (i) in this trivial way:
  it is a finite-level statement (scalar on `G_F ∩ P_p`, `e(F) ≤ (DG₀)!`) plus the bound for the
  character `β`.

## Step 3 (04:35-04:40 PST): T20 + T21 bridge, verbatim check
- §2c `LadicDVRModel p` (glue, transport) and `hilbertSerre_of_model : LadicDVRModel p →
  HilbertSerreLadic p` using the kernel's `PkgI6.hilbertDifferentFormula` (T20) and
  `PkgI6.differentBound` (T21); `span_natCast_eq`: `(e) = 𝔪^{e·v_p(e)}`.
- §3 `g15RamG_of_model` (hypotheses: `LadicDVRModel`, `WildFixTame`, `LocalData`, `G11Out`).
- Step 4 verbatim check (VERIFIED, python string comparison): the blocks `ModData`, `U0`,
  `LocalRamG`, `G15RamG` with their docstrings equal those of
  `scratch/g0-mod-newform/NewForm.lean`; `G11Out` equals `scratch/g0-mod-galois/part_galois.lean`.

## Step 5 (04:45-04:53 PST): full compile, tail integration
- `G15Ram.lean` compile (VERIFIED): exit 0, 0 errors; axioms standard for all six printed
  declarations incl. `hilbertSerre_of_model`, `g15RamG_of_model`.
- `Tail.lean` (built by `build_tail.sh`: verbatim `scratch/g0-mod-newform/NewForm.lean` with four
  extra imports appended after its own, `G11Out`, `G15Ram.lean` §1-§3, `tail_part.lean`):
  `G0ModNewform.modularConstituent_tail_R` (the tail with `G15RamG` replaced by the pieces)
  compiles; exit 0, 0 errors, ~42 s; axioms standard (VERIFIED, `tail_compile.out`).
- Note: with the four extra imports placed *before* NewForm's imports, the copied
  `bcPt.map_one'` (E1 copy) fails with "No goals to be solved" (its `rw` closes the goal, so
  the trailing `rfl` errors); placing them after NewForm's imports avoids it.

## Step 6 (04:46-04:52 PST): WildFixTame proved
- §2d `wildFixTame : WildFixTame p` (proved, no hypothesis). `inertiaSub F` (subgroup of
  `G_{ℚ_p}`), `ramSet_zero_eq` (`ramSet F 0 = inertiaSub F` via `IsUnif`), `ramCard_zero_eq`
  (`ramCard F 0 = |(inertiaSub F).map restrictNormalHom|`), Lagrange
  (`orderOf_dvd_natCard`), and the averaging lemma `fix_of_wild_pow` (`m z = ∑(z − σ^k z)`,
  ultrametric, `‖m‖ = 1`).
- `g15RamG_of_dvrModel` (only closed hypothesis: `LadicDVRModel`). `Tail.lean`'s
  `modularConstituent_tail_R` updated to it.
- Compile (VERIFIED): `G15Ram.lean` exit 0, 0 errors, axioms standard for all 8 printed
  declarations; `Tail.lean` exit 0, 0 errors, ~40 s, `modularConstituent_tail_R` axioms standard.
