import ZInQKernel.Contrib.OneProof.BShTracesCosets
import ZInQKernel.Contrib.OneProof.BShStandardWeber
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_VeluOrderTwo
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_VeluQuotientMap

/-! ON THE SPOT (provenance (c)): compare the two short Weierstrass
coefficients and the marked coordinate using the same coset enumeration.
Summing over *all* nonzero cosets counts a pair of opposite points twice;
an order-two point occurs only once. -/

noncomputable section

namespace BShTraces

open PeriodPair WeierstrassCurve
open scoped PeriodPair Topology
open Filter

/-- The coefficient at a nonzero coset in the short Vélu formula for (a_4). -/
def shortT {R : Type*} [CommRing R] (a x : R) : R := 3 * x ^ 2 + a

/-- The coefficient at a nonzero coset in the short Vélu formula for (a_6). -/
def shortW {R : Type*} [CommRing R] (a b x : R) : R := 5 * x ^ 3 + 3 * a * x + 2 * b

/-- The contribution to the image's (x)-coordinate per nonzero coset.
For opposite points the contributions agree. For a point of order two
the second summand vanishes. -/
def shortShift {R : Type*} [Field R] (a b x t : R) : R :=
  shortT a t / (x - t) + (2 * (t ^ 3 + a * t + b)) / (x - t) ^ 2

private theorem invPow₄ (L : PeriodPair) {w : ℂ} (hw : w ∉ L.lattice) :
    6 * L.sumInvPow w 4 = 6 * ℘[L] w ^ 2 - L.g₂ / 2 := by
  rw [← L.deriv_derivWeierstrassPExcept_self,
    L.derivWeierstrassPExcept_of_notMem w hw]
  exact P2MW.S_PeriodPair_isUniformization_toPoint.PeriodPair.kw_deriv_derivWeierstrassP L hw

private theorem invPow₆ (L : PeriodPair) {w : ℂ} (hw : w ∉ L.lattice) :
    120 * L.sumInvPow w 6 = 120 * ℘[L] w ^ 3 - 18 * L.g₂ * ℘[L] w - 12 * L.g₃ := by
  have h₄ := L.iteratedDeriv_weierstrassPExcept_self w (n := 4)
  rw [L.weierstrassPExcept_of_notMem w hw] at h₄
  norm_num at h₄
  have hd₂ : deriv (deriv ℘'[L]) =ᶠ[𝓝 w] fun z => 12 * ℘[L] z * ℘'[L] z := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hw] with z hz
    exact P2MW.S_PeriodPair_isUniformization_toPoint.PeriodPair.kw_deriv2_derivWeierstrassP L hz
  have hP : HasDerivAt ℘[L] (℘'[L] w) w := by
    rw [← L.deriv_weierstrassP]
    exact (L.analyticOnNhd_weierstrassP w hw).differentiableAt.hasDerivAt
  have hD : HasDerivAt ℘'[L] (6 * ℘[L] w ^ 2 - L.g₂ / 2) w := by
    rw [← P2MW.S_PeriodPair_isUniformization_toPoint.PeriodPair.kw_deriv_derivWeierstrassP L hw]
    exact (L.analyticOnNhd_derivWeierstrassP w hw).differentiableAt.hasDerivAt
  rw [show iteratedDeriv 4 ℘[L] w = deriv (deriv (deriv ℘'[L])) w by
    rw [show (4 : ℕ) = ((0 + 1) + 1) + 1 + 1 from rfl]
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, L.deriv_weierstrassP],
    hd₂.deriv_eq] at h₄
  change deriv ((fun z => 12 * ℘[L] z) * ℘'[L]) w = _ at h₄
  rw [((hP.const_mul 12).mul hD).deriv] at h₄
  linear_combination -h₄ + 12 * L.derivWeierstrassP_sq w hw

/-- The coefficients (a_4,a_6) of the quotient lattice are the short
Vélu coefficients, with one summand per nonzero coset. -/
theorem short_coefficients_of_cosets {L M : PeriodPair} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : CosetEnumeration L M ι) (o : ι)
    (h₀ : D.representative o = 0) (hne : ∀ i ≠ o, D.representative i ∉ L.lattice) :
    M.weierstrassCurve.a₄ =
        L.weierstrassCurve.a₄ - 5 * ∑ i ∈ Finset.univ.erase o,
          shortT L.weierstrassCurve.a₄ (℘[L] (D.representative i)) ∧
    M.weierstrassCurve.a₆ =
        L.weierstrassCurve.a₆ - 7 * ∑ i ∈ Finset.univ.erase o,
          shortW L.weierstrassCurve.a₄ L.weierstrassCurve.a₆ (℘[L] (D.representative i)) := by
  classical
  have hsum₄ := G_cosets D (n := 4) (by decide)
  have hsum₆ := G_cosets D (n := 6) (by decide)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ o), h₀, sumInvPow_zero] at hsum₄ hsum₆
  have hT (i : ι) (hi : i ∈ Finset.univ.erase o) :
      shortT L.weierstrassCurve.a₄ (℘[L] (D.representative i)) =
        3 * L.sumInvPow (D.representative i) 4 := by
    simp only [shortT, weierstrassCurve_a₄]
    linear_combination -(1/2 : ℂ) * invPow₄ L (hne i (Finset.mem_erase.mp hi).1)
  have hW (i : ι) (hi : i ∈ Finset.univ.erase o) :
      shortW L.weierstrassCurve.a₄ L.weierstrassCurve.a₆ (℘[L] (D.representative i)) =
        5 * L.sumInvPow (D.representative i) 6 := by
    simp only [shortW, weierstrassCurve_a₄, weierstrassCurve_a₆]
    linear_combination -(1/24 : ℂ) * invPow₆ L (hne i (Finset.mem_erase.mp hi).1)
  constructor
  · rw [Finset.sum_congr rfl hT, ← Finset.mul_sum]
    simp only [weierstrassCurve_a₄, g₂]
    rw [hsum₄]
    ring
  · rw [Finset.sum_congr rfl hW, ← Finset.mul_sum]
    simp only [weierstrassCurve_a₆, g₃]
    rw [hsum₆]
    ring

/-- For a short model, the vendored pair contributions are twice the
contributions for one of the two points. -/
theorem short_pair_weights {F : Type*} [Field F] (E : WeierstrassCurve F)
    (h₁ : E.a₁ = 0) (h₂ : E.a₂ = 0) (h₃ : E.a₃ = 0)
    {t y : F} (h : E.toAffine.Equation t y) :
    E.veluT t y = 2 * shortT E.a₄ t ∧
    E.veluW t y = 2 * shortW E.a₄ E.a₆ t ∧
    E.veluU t y = 2 * (2 * (t ^ 3 + E.a₄ * t + E.a₆)) := by
  have he : y ^ 2 = t ^ 3 + E.a₄ * t + E.a₆ := by
    rw [Affine.equation_iff] at h
    simp [h₁, h₂, h₃] at h
    exact h
  simp only [veluW, veluU, veluT, veluGx, veluGy, h₁, h₂, h₃, shortT, shortW]
  constructor
  · ring
  constructor <;> linear_combination 4 * he

/-- The order-two quotient uses a single weight and the pole of order two
in the marked-coordinate summand disappears. -/
theorem short_two_weights {F : Type*} [Field F] (E : WeierstrassCurve F)
    (h₁ : E.a₁ = 0) (h₂ : E.a₂ = 0) (h₃ : E.a₃ = 0)
    {t : F} (h : E.toAffine.Equation t 0) (x : F) :
    (E.veluQuotient2 t 0).a₄ = E.a₄ - 5 * shortT E.a₄ t ∧
    (E.veluQuotient2 t 0).a₆ = E.a₆ - 7 * shortW E.a₄ E.a₆ t ∧
    shortShift E.a₄ E.a₆ x t = shortT E.a₄ t / (x - t) := by
  have he : t ^ 3 + E.a₄ * t + E.a₆ = 0 := by
    rw [Affine.equation_iff] at h
    simpa [h₁, h₂, h₃] using h.symm
  simp only [veluQuotient2_a₄, veluQuotient2_a₆, b₂, veluGx, shortT, shortW, shortShift,
    h₁, h₂, he, mul_zero, zero_mul, add_zero, zero_div, sub_zero, true_and, and_true,
    zero_pow (show (2 : ℕ) ≠ 0 by decide)]
  linear_combination 14 * he

private theorem weierstrassP_add_formula (L : PeriodPair) (hΔ : L.DiscriminantNeZero)
    {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hne : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w) = ((℘'[L] z - ℘'[L] w) / 2 / (℘[L] z - ℘[L] w)) ^ 2
      - ℘[L] z - ℘[L] w := by
  classical
  have h := (L.isUniformization_toPoint hΔ).1 z w
  rw [L.toPoint_of_notMem hΔ hzw, L.toPoint_of_notMem hΔ hz,
    L.toPoint_of_notMem hΔ hw, Affine.Point.add_of_X_ne hne] at h
  have hx := congrArg (LeafModCurves.xCoord (W := L.weierstrassCurve)) h
  change ℘[L] (z + w) = L.weierstrassCurve.toAffine.addX
    (℘[L] z) (℘[L] w) (L.weierstrassCurve.toAffine.slope
      (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2)) at hx
  rw [Affine.slope_of_X_ne hne] at hx
  rw [hx]
  simp only [Affine.addX, weierstrassCurve_a₁, weierstrassCurve_a₂,
    zero_mul, add_zero, sub_zero]
  congr 3
  ring

/-- The sum of the two opposite marked translates is twice the short Vélu
shift. The identity also applies when the two translates represent the same
order-two coset. -/
theorem short_shift_of_opposites (L : PeriodPair) (hΔ : L.DiscriminantNeZero)
    {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hplus : z + w ∉ L.lattice) (hminus : z - w ∉ L.lattice)
    (hne : ℘[L] z ≠ ℘[L] w) :
    (℘[L] (z + w) - ℘[L] w) + (℘[L] (z - w) - ℘[L] w) =
      2 * shortShift L.weierstrassCurve.a₄ L.weierstrassCurve.a₆ (℘[L] z) (℘[L] w) := by
  have hnw : -w ∉ L.lattice := by simpa
  have h₁ := weierstrassP_add_formula L hΔ hz hw hplus hne
  have h₂ := weierstrassP_add_formula L hΔ hz hnw (by simpa [sub_eq_add_neg] using hminus)
    (by simpa only [L.weierstrassP_neg] using hne)
  rw [L.weierstrassP_neg, L.derivWeierstrassP_neg, ← sub_eq_add_neg] at h₂
  rw [h₁, h₂]
  simp only [shortShift, shortT, weierstrassCurve_a₄, weierstrassCurve_a₆]
  have hd := sub_ne_zero.mpr hne
  have hdz := L.derivWeierstrassP_sq z hz
  have hdw := L.derivWeierstrassP_sq w hw
  field_simp
  linear_combination 8 * hdz + 8 * hdw

/-- For a sign permutation of the nonzero cosets, the larger lattice's
marked coordinate is the short Vélu expression over the cosets. -/
theorem short_mark_of_cosets {L M : PeriodPair} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : CosetEnumeration L M ι) (o : ι) (h₀ : D.representative o = 0)
    (hΔ : L.DiscriminantNeZero) (z : ℂ) (hz : z ∉ L.lattice)
    (hne : ∀ i ≠ o, D.representative i ∉ L.lattice)
    (hplus : ∀ i ≠ o, z + D.representative i ∉ L.lattice)
    (hminus : ∀ i ≠ o, z - D.representative i ∉ L.lattice)
    (hx : ∀ i ≠ o, ℘[L] z ≠ ℘[L] (D.representative i))
    (σ : Equiv.Perm {i : ι // i ≠ o})
    (hσ : ∀ i, D.representative (σ i).val + D.representative i.val ∈ L.lattice) :
    ℘[M] z = ℘[L] z + ∑ i ∈ Finset.univ.erase o,
      shortShift L.weierstrassCurve.a₄ L.weierstrassCurve.a₆ (℘[L] z) (℘[L] (D.representative i)) := by
  let f : ι → ℂ := fun i => ℘[L] (z + D.representative i) - ℘[L] (D.representative i)
  let g : ι → ℂ := fun i => ℘[L] (z - D.representative i) - ℘[L] (D.representative i)
  let S : Finset ι := Finset.univ.erase o
  have hs (i : ι) : i ∈ S ↔ i ≠ o := by simp [S]
  have hfg (i : {i : ι // i ≠ o}) : f (σ i).val = g i.val := by
    let l : L.lattice := ⟨D.representative (σ i).val + D.representative i.val, hσ i⟩
    have h₁ : z + D.representative (σ i).val = (z - D.representative i.val) + (l : ℂ) := by
      dsimp [l]; ring
    have h₂ : D.representative (σ i).val = -D.representative i.val + (l : ℂ) := by
      dsimp [l]; ring
    dsimp only [f, g]
    rw [h₁, h₂, L.weierstrassP_add_coe, L.weierstrassP_add_coe, L.weierstrassP_neg]
  have he : ∑ i ∈ S, f i = ∑ i ∈ S, g i := by
    rw [Finset.sum_subtype S hs f, Finset.sum_subtype S hs g]
    simpa only [Function.comp_apply, hfg] using (Equiv.sum_comp σ (fun i => f i.val)).symm
  have hh : (∑ i ∈ S, f i) + (∑ i ∈ S, g i) =
      2 * ∑ i ∈ S, shortShift L.weierstrassCurve.a₄ L.weierstrassCurve.a₆
        (℘[L] z) (℘[L] (D.representative i)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have h := (hs i).mp hi
    exact short_shift_of_opposites L hΔ hz (hne i h) (hplus i h) (hminus i h) (hx i h)
  rw [weierstrassP_cosets D z, ← Finset.sum_erase_add _ _ (Finset.mem_univ o), h₀,
    add_zero, L.weierstrassP_zero, sub_zero]
  change (∑ i ∈ S, f i) + ℘[L] z = _
  rw [← he] at hh
  linear_combination (1/2 : ℂ) * hh

open T5Glue in
/-- The rational coordinate pair of a short Weierstrass equation and a mark,
on the generic Weber branch. -/
def shortCoordinates {F : Type*} [Field F] (a b x : F) : F × F :=
  let g₂ := -4 * a
  let g₃ := -4 * b
  let Δ := g₂ ^ 3 - 27 * g₃ ^ 2
  (1728 * g₂ ^ 3 / Δ, g₂ * g₃ / Δ * x)

/-- A change in the (x)-coordinate by a nonzero factor of weight two,
and the matching changes of the two short coefficients, preserve both
intrinsic coordinates. -/
theorem short_coordinates_scale {F : Type*} [Field F]
    (a b x u : F) (hu : u ≠ 0) :
    shortCoordinates (u ^ 2 * a) (u ^ 3 * b) (u * x) = shortCoordinates a b x := by
  let Δ := (-4 * a) ^ 3 - 27 * (-4 * b) ^ 2
  have hΔ : (-4 * (u ^ 2 * a)) ^ 3 - 27 * (-4 * (u ^ 3 * b)) ^ 2 = u ^ 6 * Δ := by
    dsimp [Δ]; ring
  have h₂ : 1728 * (-4 * (u ^ 2 * a)) ^ 3 = u ^ 6 * (1728 * (-4 * a) ^ 3) := by ring
  have h₃ : -4 * (u ^ 2 * a) * (-4 * (u ^ 3 * b)) * (u * x) =
      u ^ 6 * (-4 * a * (-4 * b) * x) := by ring
  apply Prod.ext
  · simp only [shortCoordinates, hΔ, h₂, mul_div_mul_left _ _ (pow_ne_zero _ hu)] <;> rfl
  · simp only [shortCoordinates, hΔ]
    rw [← mul_div_right_comm, ← mul_div_right_comm, h₃, mul_div_mul_left _ _ (pow_ne_zero _ hu)]

/-- The three short Vélu summands transform with their respective weights. -/
theorem short_weights_scale {F : Type*} [Field F] (a b x t u : F) (hu : u ≠ 0) :
    shortT (u ^ 2 * a) (u * t) = u ^ 2 * shortT a t ∧
    shortW (u ^ 2 * a) (u ^ 3 * b) (u * t) = u ^ 3 * shortW a b t ∧
    shortShift (u ^ 2 * a) (u ^ 3 * b) (u * x) (u * t) = u * shortShift a b x t := by
  have ht : shortT (u ^ 2 * a) (u * t) = u ^ 2 * shortT a t := by unfold shortT; ring
  refine ⟨ht, by unfold shortW; ring, ?_⟩
  unfold shortShift
  rw [ht, ← mul_sub,
    show 2 * ((u * t) ^ 3 + u ^ 2 * a * (u * t) + u ^ 3 * b) =
      u ^ 3 * (2 * (t ^ 3 + a * t + b)) by ring]
  by_cases h : x - t = 0
  · simp [h]
  · field_simp
    <;> ring

open T5Glue in
/-- The same short Vélu sums determine both coordinates of the superlattice
with its marked image. The two generic Weber tests are on the target lattice. -/
theorem short_coordinates_of_cosets {L M : PeriodPair} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : CosetEnumeration L M ι) (o : ι) (h₀ : D.representative o = 0)
    (hΔ : L.DiscriminantNeZero) (z : ℂ) (hz : z ∉ L.lattice)
    (hne : ∀ i ≠ o, D.representative i ∉ L.lattice)
    (hplus : ∀ i ≠ o, z + D.representative i ∉ L.lattice)
    (hminus : ∀ i ≠ o, z - D.representative i ∉ L.lattice)
    (hx : ∀ i ≠ o, ℘[L] z ≠ ℘[L] (D.representative i))
    (σ : Equiv.Perm {i : ι // i ≠ o})
    (hσ : ∀ i, D.representative (σ i).val + D.representative i.val ∈ L.lattice)
    (h₂ : M.g₂ ≠ 0) (h₃ : M.g₃ ≠ 0) :
    let a := L.weierstrassCurve.a₄
    let b := L.weierstrassCurve.a₆
    let x := ℘[L] z
    let t := fun i => ℘[L] (D.representative i)
    shortCoordinates (a - 5 * ∑ i ∈ Finset.univ.erase o, shortT a (t i))
        (b - 7 * ∑ i ∈ Finset.univ.erase o, shortW a b (t i))
        (x + ∑ i ∈ Finset.univ.erase o, shortShift a b x (t i)) =
      (jL M, weber M z) := by
  dsimp only
  obtain ⟨ha, hb⟩ := short_coefficients_of_cosets D o h₀ hne
  rw [← ha, ← hb, ← short_mark_of_cosets D o h₀ hΔ z hz hne hplus hminus hx σ hσ]
  have ha' : -4 * M.weierstrassCurve.a₄ = M.g₂ := by rw [weierstrassCurve_a₄]; ring
  have hb' : -4 * M.weierstrassCurve.a₆ = M.g₃ := by rw [weierstrassCurve_a₆]; ring
  simp only [shortCoordinates, ha', hb', jL, weber, h₃, h₂, ite_false, discL]

private theorem x_ne_of_sub_add_notMem (L : PeriodPair) (hΔ : L.DiscriminantNeZero)
    {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hplus : z + w ∉ L.lattice) (hminus : z - w ∉ L.lattice) :
    ℘[L] z ≠ ℘[L] w := by
  intro he
  let toPt : ℂ →+ L.weierstrassCurve.toAffine.Point :=
    ⟨⟨L.toPoint hΔ, L.toPoint_zero hΔ⟩, (L.isUniformization_toPoint hΔ).1⟩
  have e : ℘'[L] z ^ 2 = ℘'[L] w ^ 2 := by
    rw [L.derivWeierstrassP_sq z hz, L.derivWeierstrassP_sq w hw, he]
  have aux {v : ℂ} (hv : v ∉ L.lattice) (hx : ℘[L] z = ℘[L] v)
      (hy : ℘'[L] z = ℘'[L] v) : z - v ∈ L.lattice := by
    apply (X1Igusa.Weber.toPoint_eq_zero_iff L hΔ _).mp
    change toPt (z - v) = 0
    rw [map_sub, sub_eq_zero]
    change L.toPoint hΔ z = L.toPoint hΔ v
    rw [L.toPoint_of_notMem hΔ hz, L.toPoint_of_notMem hΔ hv]
    exact Affine.Point.some.injEq .. |>.mpr ⟨hx, by rw [hy]⟩
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp e with e | e
  · exact hminus (aux hw he e)
  · have hn : -w ∉ L.lattice := by simpa
    have hx : ℘[L] z = ℘[L] (-w) := by rwa [L.weierstrassP_neg]
    have hy : ℘'[L] z = ℘'[L] (-w) := by rwa [L.derivWeierstrassP_neg]
    exact hplus (by simpa only [sub_neg_eq_add] using aux hn hx hy)

/-- Compute the short Vélu coefficients and mark from the x-coordinates
of the nonzero cosets. -/
def markedLatticeCoordinates {L M : PeriodPair} {ι : Type*} [Fintype ι]
    (D : CosetEnumeration L M ι) (o : ι) (z : ℂ) : ℂ × ℂ :=
    letI := Classical.decEq ι
    let a := L.weierstrassCurve.a₄
    let b := L.weierstrassCurve.a₆
    let x := ℘[L] z
    let t := fun i => ℘[L] (D.representative i)
    shortCoordinates (a - 5 * ∑ i ∈ Finset.univ.erase o, shortT a (t i))
        (b - 7 * ∑ i ∈ Finset.univ.erase o, shortW a b (t i))
        (x + ∑ i ∈ Finset.univ.erase o, shortShift a b x (t i))

open T5Glue in
/-- Intrinsic form of the simultaneous coordinate comparison: the only
condition on the mark is that it remain outside the enlarged lattice. -/
theorem short_coordinates_of_surviving_mark {L M : PeriodPair} {ι : Type*} [Fintype ι]
    (D : CosetEnumeration L M ι) (o : ι) (h₀ : D.representative o = 0)
    (hΔ : L.DiscriminantNeZero) (z : ℂ) (hz : z ∉ M.lattice)
    (h₂ : M.g₂ ≠ 0) (h₃ : M.g₃ ≠ 0) :
    markedLatticeCoordinates D o z = (jL M, weber M z) := by
  classical
  have hL := lattice_le D o h₀
  have hzl : z ∉ L.lattice := fun h => hz (hL h)
  have hplus (i : ι) : z + D.representative i ∉ L.lattice := by
    intro h
    exact hz (by simpa using M.lattice.sub_mem (hL h) (representative_mem D i))
  have hminus (i : ι) : z - D.representative i ∉ L.lattice := by
    intro h
    exact hz (by simpa using M.lattice.add_mem (hL h) (representative_mem D i))
  have hne (i : ι) (hi : i ≠ o) := representative_notMem D o h₀ hi
  obtain ⟨σ, hσ⟩ := exists_neg_perm D o h₀
  unfold markedLatticeCoordinates
  exact short_coordinates_of_cosets D o h₀ hΔ z hzl hne (fun i _ => hplus i)
    (fun i _ => hminus i) (fun i hi => x_ne_of_sub_add_notMem L hΔ hzl (hne i hi) (hplus i)
      (hminus i)) σ hσ h₂ h₃

#print axioms invPow₄
#print axioms invPow₆
#print axioms short_coefficients_of_cosets
#print axioms short_pair_weights
#print axioms short_two_weights
#print axioms weierstrassP_add_formula
#print axioms short_shift_of_opposites
#print axioms short_mark_of_cosets
#print axioms short_coordinates_scale
#print axioms short_weights_scale
#print axioms short_coordinates_of_cosets
#print axioms x_ne_of_sub_add_notMem
#print axioms short_coordinates_of_surviving_mark

end BShTraces
