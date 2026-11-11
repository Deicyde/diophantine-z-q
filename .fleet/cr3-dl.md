# cr3-dl report

## Result

All steps 1–6 and the optional step are done. New file: `ZInQKernel/RouteK/RankDL.lean` (~210 lines). No
other Lean file was edited except one import line in `ZInQKernel.lean`. `lake build ZInQKernel`
succeeds, and `lake env lean scripts/print_axioms.lean` shows only `propext`, `Classical.choice`,
`Quot.sound` for all 44 entries, including the 6 new ones. There is no `sorry`.

## Exact statement

```lean
def ZInQ.RouteK.Rank.CertifiedRankDLRk : Prop :=
  ∀ (β θ : ℤ) (p₀ : ℕ), Inputs β θ p₀ → ∃ D : Slots β θ p₀,
    (∃ P : (shortCurve (-((D.d₁ : ℕ) : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P) ∧
    (∃ P : (shortCurve (-((D.d₁ * θ.natAbs : ℕ) : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P)
```

## Lean names (all in `ZInQKernel/RouteK/RankDL.lean`; namespace `ZInQ.RouteK.Rank` except the last)

- `sel_of_selmerCertified` (step 1): `d % 8 = 5`, `Squarefree d`, `Squarefree a`, `a ∣ d`,
  `SelmerCertified d a` ⊢ `(Sel2 d).ncard = 8 ∧ ∃ b, (a, b) ∈ Sel2 d`. This is the body of
  `certifiedRank_of_sel` with `prop0Statement`; `certifiedRank_of_sel` is unchanged.
- `CertifiedRankDLRk` (step 2), shown above.
- `slots_d₂_facts`: for `C_{D.d₁ |θ|}`: `≡ 5 (mod 8)`, squarefree, `β ∣ d`, `SelmerCertified d β`.
- `exists_infinite_order_of_certifiedRankTYZRk_of_selmerCertified`, `certifiedRankDLRk_of_certifiedRankTYZRk`
  (step 3): D comes from `exists_slots`. `T5b = 1` follows from `det_M5b_eq_one` and `det_M5b_eq_T5b`.
- `exists_point_of_selmerCertified_of_infinite_order`: step 1, then
  `loc_of_mem_sel2_of_infinite_order` with `fg_points`, then `exists_point_of_loc`. Together these give
  the CR₃ conclusion at one curve.
- `poleSoluble_of_slots_infinite_order`, a per-B core taking `m`, `Inputs` and `D` with points on both
  curves, and `poleCompleteness_of_certifiedRankDLRk` (step 4).
- `CertifiedRankDLAdmRk` (optional): for every admissible `B` there exist `m ∣ 2730`, `β` odd with
  `|β| ≡ 7 (mod 8)`, `p₀ ∈ primesOf β` and `D : Slots β θ p₀` whose two curves have points of
  infinite order. Its implications are `certifiedRankDLAdmRk_of_certifiedRankDLRk` and
  `poleCompleteness_of_certifiedRankDLAdmRk`.
- `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLRk`
  (step 5) uses `Assembly.assembly_AP` with `haltingAddMulBound`, `poleCompleteness_of_certifiedRankDLRk`
  and `slopeRepresentationAP_of_goodPrimeAP (goodPrimeAP_of_greenTaoDense greenTaoDense
  Density.goodPrimeDensity)`, the same route as the `sixContactMin_certifiedRank` variant.
- New entries in `scripts/print_axioms.lean`: the main variant, `sel_of_selmerCertified`,
  `certifiedRankDLRk_of_certifiedRankTYZRk`, `poleCompleteness_of_certifiedRankDLRk`,
  `poleCompleteness_of_certifiedRankDLAdmRk`, `certifiedRankDLAdmRk_of_certifiedRankDLRk`.

## Problems

Only one: `obtain ⟨-, hcard, σ, hσ, hfirst⟩` on `SelmerCertified` also cleared the hypotheses that
depend on the `Odd d` witness. Using `_` instead of `-` fixed it.

## Paragraph for KERNEL_PLAN.md

CR₃ restricted to the curves the proof uses (`RouteK/RankDL.lean`). Pole completeness applies CR₃ at
only two curves, `C_{d₁}` and `C_{d₁|θ|}`, where `d₁ = D.d₁` comes from a slot choice
`D : RouteK.Slots β θ p₀`. `RouteK.Rank.CertifiedRankDLRk` says: for every `β, θ, p₀` with
`RouteK.Inputs β θ p₀` there is some slot choice `D` whose two curves both have a rational point of
infinite order. Lean proves `CertifiedRankTYZRk → CertifiedRankDLRk`
(`certifiedRankDLRk_of_certifiedRankTYZRk`, by Corollary 4.4 and Theorem 3.6) and
`CertifiedRankDLRk → PoleCompleteness` (`poleCompleteness_of_certifiedRankDLRk`, by Proposition 0,
RK9 and Mordell–Weil). The main theorem follows from 6C_min and `CertifiedRankDLRk`
(`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLRk`). The
variant `CertifiedRankDLAdmRk` quantifies only over admissible `B` and the multiplier, `p₀` and
slots of `exists_multiplier_and_slots`. These forms rest on the same literature as CR₃^TYZ,Rk. Any
statement Lean derives from that hypothesis, down to `PoleCompleteness`, is equally justified. What
these forms add is a smaller target for partial results, such as explicit families of points on the
curves of some slot choice. They depend on the internal definitions `Inputs` and `Slots` (and
`Slots.d₁`), so changing the slot construction changes what they mean.

## Suggestions

A partial result would most easily plug in through `poleSoluble_of_slots_infinite_order`. Given
explicit points for a sub-family of `B`, that lemma proves `PoleSoluble B` directly for that
sub-family.
