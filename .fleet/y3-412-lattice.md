# y3-412-lattice (branch `wip/y3-412-lattice`, base `d28aef9839b8c12dcda2b24b3a22c993f4975dbf`)

**No count change.** The work is additive and nothing is folded. No existing file was changed.

**Proved (compiled with `lake build`, no `sorry`; `#print axioms` = `[propext, Classical.choice, Quot.sound]`
for all 30 theorems, see `ZInQKernel/Contrib/OneProof/Y3Lattice412/Check.lean`):**
- A0 `Y3Lattice412.rat_mem_ZhatQ_iff`: `algebraMap ℚ AQ r ∈ ZhatQ ↔ ∃ z : ℤ, r = z`.
- A1 `bEmb_mem_OhatQ_iff`: `bEmb b ∈ OhatQ ↔ InO b`.
- A2 `latticeAt g := {b | bEmb b * g ∈ OhatQ}` (`L_g = B ∩ 𝒪̂g⁻¹`); `latticeAt_of_mem_OhatU`: `u ∈ OhatU → latticeAt u = {b | InO b}`.
- A3 closure under `+`, `−`, `0` and left multiplication by `𝒪`; `latticeAt_bounds` (`N𝒪 ⊆ L_g ⊆ N⁻¹𝒪`);
  `latticeAt_eq_O_mul` (`L_g = 𝒪α`, via the tree's `classNumberOneB_proof`); `latticeAt_basis` (a `ℚ`-basis
  `e : Fin 4 → B` of `B` with `L_g = ⊕ ℤ eᵢ`).
- A4 `latticeAt_dc`: `γ ≠ 0`, `k ∈ K3Q`, `g' = bEmb γ * g * k` ⇒ `latticeAt g' = (· * binv γ) '' latticeAt g`;
  `latticeAt_of_DCRel`.
- A5 `latticeAt_eq_deligne`: `b ∈ latticeAt g ↔ bEmb b ∈ app (toGAf g⁻¹)⁻¹ '' VZhat`
  (Deligne's `k⁻¹(V̂_ℤ)` with `k = toGAf g⁻¹`, by `dcRelDel_iff_PM`). The convention is confirmed:
  `B ∩ 𝒪̂g⁻¹`, not `B ∩ g𝒪̂`.
- B1 `IsHodgeH1PrintAt P τ L`; `isHodgeH1PrintAt_O_iff : IsHodgeH1PrintAt P τ {b | InO b} ↔ IsHodgeH1Print P τ`.
- B2 `ModuliAtLattice`; `moduliAtUnitsHP_of_lattice : ModuliAtLattice Y Φ Ψ → ModuliAtUnitsHP Y Φ Ψ`;
  `moduliAtUsedUnitsHP_of_lattice` (for `fun τ g => Ψ (toPM τ) g`).

**Files:** `ZInQKernel/Contrib/OneProof/Y3Lattice412/{Lattice,Convention,Moduli,Check}.lean`,
`docs/research/y3-412-lattice.md` (exact types, the convention check, the proposed row-U text for
`DeligneY3Bridges/README.md`, the part-C analysis), `scratch/y3-412-lattice/{log.md,axioms.txt}`.

**What remains (part C, report only):** the existence and uniqueness half of 4.12 (`T̂(B) = k⁻¹(V̂_ℤ)` in
each isogeny class). Missing pieces:
- the quotient by a finite subgroup over `ℂ`; the tree has `finiteSubgroupQuotient_exists` over `ℚ` only;
- the analytic description of the quotient's `ℂ`-points;
- algebraization; `HomLatticeCorr` is a leaf.

The `H₁` dictionary for a general `L` (generalizing `print_iff_hodge`) looks within reach. For this datum,
class number one (`L_g = 𝒪γ⁻¹`) plus the `Jmat` conjugation law would give a converse to B2 without any
quotient. That converse is not attempted (B3).

Report commit: `394f371169a4895011e24edcfc01131e629ab5f9`; this file is committed in the next commit on
top of it (its SHA is given in the final message of the run).
