# size-formal: the successful formal multiple

Branch `wip/size-formal`. Modules under `ZInQKernel/Size/FormalMultiple/`, root module
`ZInQKernel/Size/FormalMultiple.lean` (imported from `ZInQKernel.lean`). Everything is in
namespace `ZInQ.Size`. All seven leaves are proved: no `sorry`, no axioms beyond `propext`,
`Classical.choice`, `Quot.sound` (checked with `#print axioms` on the main theorems), no
`native_decide`, and no finite-computation hypotheses. `lake build ZInQKernel` succeeds.

## Leaves

| Article | Lean name | Status |
| --- | --- | --- |
| `size/formal-multiple/reduction-homomorphism.md` | `ZInQ.Size.E0sub`, `ZInQ.Size.E1sub`, `ZInQ.Size.redK`, `ZInQ.Size.reductionHom`, `ZInQ.Size.ker_reductionHom`, `ZInQ.Size.E0_eq_top_of_good`, `ZInQ.Size.zsmul_addOrderOf_mem_E1` (file `Reduction.lean`) | proved |
| `size/formal-multiple/trivial-point-count.md` | `ZInQ.Size.card_affineSolutions_le`, `ZInQ.Size.card_points_le`, `ZInQ.Size.addOrderOf_le_two_card_add_one`, `ZInQ.Size.odd_prime_count_bounds` (file `PointCount.lean`) | proved |
| `size/formal-multiple/bad-place-congruences.md` | `ZInQ.Size.bad_place_congruences` (and the `𝔽₇` form `bad_place_congruences_zmod`), by `decide` (file `Congruences.lean`) | proved |
| `size/formal-multiple/bad-place-reduction.md` | `ZInQ.Size.genP0_mem_E0_d`, `ZInQ.Size.redK_genP0_d`, `ZInQ.Size.resK_genA_d`, `ZInQ.Size.E0_eq_top_of_ne_d` (file `BadPlace.lean`) | proved |
| `size/formal-multiple/reduction-orders.md` | `ZInQ.Size.exists_reduction_multiple` (file `ReductionOrders.lean`) | proved |
| `size/formal-multiple/odd-coefficient-extraction.md` | `ZInQ.Size.padicValRat_coords_ge` (file `OddCoefficients.lean`) | proved |
| `size/formal-multiple/formal-multiple-existence.md` | `ZInQ.Size.exists_formal_multiple`, `ZInQ.Size.leastFormalMultiple_bounds`, `ZInQ.Size.leastFormalMultiple_formalCondition`, `ZInQ.Size.M0_bounds` (file `Existence.lean`) | proved |

## How the statements read in Lean, and where they differ from the articles

1. **Reduction on the nonsingular part.** The article's prime `𝔭` is a prime element `π`
   (`ℤ[s]` is a PID), and its residue field is any field `k` with a ring map
   `ρ : ℤ[s] →+* k` of kernel `(π)` (`hρ : ∀ a, ρ a = 0 ↔ π ∣ a`). The article's case is
   `k = ℤ[s] ⧸ (π)` with `ρ` the quotient map (`quotient_mk_eq_zero_iff` gives `hρ`). The
   residue map of `𝒪_π` is `resK π ρ : K₀ → k`, and the reduced coefficient is `Ab` with
   `hAb : resK π ρ A = Ab`. The coefficient `A` is any element of `K₀` that is integral at `π`
   (`VGe π 0 A`), which is more general than the article's `A ∈ ℤ[s]`. The hypothesis
   `2 ∉ 𝔭` becomes `h2 : ¬π ∣ 2`. It is really needed: the case of opposite reductions
   cancels a factor `2` in `k`. `W₁(π)` is `E1sub` (carrier `InE1`: `O`, or `x ∉ 𝒪_π`) and
   `W₀(π)` is `E0sub` (carrier `InE0`). `ker_reductionHom` says
   `ker = E1sub.addSubgroupOf E0sub`. `E1sub_eq_formalNbhd` identifies `W₁(π)` with the
   multiplication chapter's `Mult.formalNbhd` at `vP π`. In the "consequently" part, `n` is
   `addOrderOf (redK … Q)` and the statement holds for every `m : ℤ`; finiteness, which gives
   `n ≥ 1`, comes in `exists_order_of_mem_E0`. The nonsingularity of `W̃` when `ρ(A) ≠ 0` is
   the existing `ZInQ.shortCurve_isElliptic`.
2. **The trivial point count.** The hypothesis "odd characteristic" is not needed, so it is
   dropped. For each `x`, `y² = c` has at most two roots in any field. The bound is stated for
   `Nat.card` of Mathlib's `Point` (the nonsingular points together with `O`), so it covers
   `W̃_ns(k)` in the cuspidal case as well. `addOrderOf_le_two_natCard_add_one` is the
   `Nat.card` form, for a residue field that has no chosen `Fintype` structure.
3. **The bad place.** Part 1 is `genP0_mem_E0_d` at `π = d` with `ρ = residueSeven`. The
   congruences come from `bad_place_congruences_zmod` (the same statements in `𝔽₇`). In part 2,
   "every other prime" means `¬Associated π genDZ`, and the conclusion holds for every residue
   map `ρ` with kernel `(π)`.
4. **Reduction orders.** "Every prime `𝔭` containing `p`" means every prime element `π` with
   `π ∣ (p : ℤ[s])`. The conclusion is `(m₀ : ℤ) • genP0 ∈ E1sub hπ (vge_genA hπ)`;
   `mem_E1sub_iff_vp` unfolds this to `[m₀]P₀ = O ∨ (x ≠ 0 ∧ v_π(x) < 0)`. At the bad place
   the order is bounded by `2 · 7 + 1`, the same trivial count as at the good places.
5. **Rational coordinates.** The hypothesis is
   `∀ π (hπ : Prime π), π ∣ p → (k : WithTop ℤ) ≤ Mult.vP π hπ u` (`vP 0 = ⊤`). The conclusion
   is stated for the nonzero coordinates: `u.re ≠ 0 → k ≤ padicValRat p u.re`, and the same
   for `u.im`.
6. **The successful formal multiple.** The condition is the syntax chapter's
   `Syntax.FormalCondition N m` (normalized representation of `xi (m • genP0)`). The proof
   follows the article. `formalCondition_of_padicValRat` does the normalization step from the
   coordinate bounds. As the article says, the infinite order of `P₀` is not used.

## Lemmas added beyond the leaves

- `Residue.lean`: `resK`, the residue map into an arbitrary residue field. It copies the model
  chapter's `ZInQ.res`, which only maps to `ZMod p`, together with its algebra lemmas
  (`resK_add`, `resK_mul`, `resK_div`, `resK_eq_zero_iff`, …). `res_eq_resK` shows the two
  agree on `ZMod p` (by `rfl`).
- `Reduction.lean`: `int_add` (an integral chord whose reductions are not opposite: the sum is
  integral and reduces by the chord formulas, with no nonsingularity needed), `add_of_red_opp`,
  `add_kernel`, `inE0_add_redK_add`, `inE1_add`/`inE1_neg`, `E1sub_eq_formalNbhd`,
  `mem_E1sub_iff_vp`, `quotient_mk_eq_zero_iff`, and `red_eq_redK`: the model chapter's
  `ZInQ.red` is the special case `k = 𝔽_p` of `redK`.
- `FormalMul.lean`: the parts of `assembly/local-tests/formal-multiplication.md` used here,
  in the generic setting (any field, any `AddValuation K (WithTop ℤ)`):
  `formal_third_point_five`, `chord_add_five` (the chord estimate with `5m` where `Chord.lean`
  records `m + 1`), `zCoord_add_sub_ge` (item 1), `zCoord_nsmul_sub_ge` (item 2 for `n ∈ ℕ`),
  `nsmul_mem_formalFilt_add` and `nsmul_mem_formalFilt_of_val` (item 3 when `v(q) = e`,
  `0 ≤ e ≤ 4`: `[qᵃ n] W_k ⊆ W_{k + a e}`, with no `k ≥ 1` hypothesis needed). Also
  `zCoord_neg'`.
- `ReductionOrders.lean`: `inE1_congr`/`mem_E1sub_congr` (`E₁` depends only on the ideal),
  `exists_order_of_mem_E0`, `exists_order_at_prime`, `exists_order_at_odd_prime`,
  `not_dvd_two_of_dvd_odd`, `exists_generator`, `span_isMaximal`, `natCard_quot_genDZ`, and
  `orderAbove` (the chosen order above `p`).
- `OddCoefficients.lean`: `exists_prime_dvd_natCast`, `vp_two_of_dvd_odd`,
  `vp_sqrt2_of_dvd_odd`, `re_mul_two`, `im_mul_two_sqrt2`.
- `Existence.lean`: `not_dvd_den_of_nonneg`, `den_coprime`, `formalCondition_of_padicValRat`,
  `vP_xi_ge` (`v_π(ξ) ≥ 2r` on `E_r(π)`), `vP_natCast_of_dvd`, `vS_two'`, `exists_split`.
- `BadPlace.lean`: `instance fact_prime_seven : Fact (Nat.Prime 7)`, `vge_genA`,
  `genX0_mul`/`genY0_mul`, `vge_genX0_d`/`vge_genY0_d`, `nonsingular_two_six`,
  `resK_genA_ne_zero`.

## Problems

- None blocking. The assembly-local branch had not been pushed when I started, so
  `FormalMul.lean` proves the needed cases of the formal-multiplication article itself.
  `chord_add_five` duplicates the algebra of `Mult.formal_third_point`/`Mult.chord_add`, with
  `5m` in place of `m + 1`.
- Lean pitfall: `genP0` is a `genCurve` point. Membership in subgroups of
  `(shortCurve (-genD ^ 2)).toAffine.Point` works through `change`/`exact`, but `rw` and
  `convert` across the two types leave instance-mismatch goals. I avoided them, for example by
  rewriting with an explicit equation of indices (`ReductionOrders`, `Existence`).

## Suggestions for the next agent

- When `wip/assembly-local` lands, replace `FormalMul.lean` by its item 1/3 lemmas, or keep
  `chord_add_five` and have `Mult.formal_third_point` record `5m` directly so the copy can go.
- The model chapter's `ZInQKernel/Model/Descent/Reduction.lean` could be rederived from
  `redK`/`reductionHom` through `red_eq_redK` and `res_eq_resK`, as its implementation note
  intended. I did not edit that directory.
- Blueprint `lean:` fields: use the names in the table above.
- `Congruences.lean` imports `Mathlib` wholesale, like several existing files. A lighter import
  is possible if the build-time warnings matter.
