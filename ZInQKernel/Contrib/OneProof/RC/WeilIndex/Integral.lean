import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Gauss
import Mathlib.MeasureTheory.Integral.Prod

/-! Scalar versions of the manuscript's polar Haar normalization and
completion of the square, tex 8646–8653 and 8746–8753.
The reduction of a phase to a residue ring is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.WeilIndex

open Intertwine Intertwine2 MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal Topology

/-- Haar for (x\mapsto a x^2), scaled by (sqrt{|2a|_p}). -/
def lineHaar (p : Place) (a : ℚ_[p.val]) : Measure ℚ_[p.val] :=
  ENNReal.ofReal (Real.sqrt ‖2 * a‖) • padicHaar p

instance (p : Place) (a : ℚ_[p.val]) : (lineHaar p a).IsAddLeftInvariant := by
  unfold lineHaar
  infer_instance

theorem lineHaar_integerBall (p : Place) (a : ℚ_[p.val]) :
    lineHaar p a (PadicInt.subring p.val) = ENNReal.ofReal (Real.sqrt ‖2 * a‖) := by
  have h : padicHaar p (PadicInt.subring p.val) = 1 := addHaarMeasure_self (K₀ := padicCompacts p)
  rw [lineHaar, Measure.smul_apply, h, smul_eq_mul, mul_one]

/-- Translation by the stationary point gives the phase in the local
Fourier identity on every measurable additive lattice containing it.
The remaining integral is the scalar quadratic integral at zero. -/
theorem integral_completeSquare (p : Place) (a v : ℚ_[p.val])
    (L : AddSubgroup ℚ_[p.val]) (hL : MeasurableSet (L : Set ℚ_[p.val])) (hv : v ∈ L) :
    (∫ x in (L : Set ℚ_[p.val]), localPhase p (a * x ^ 2 + 2 * a * x * v) ∂lineHaar p a) =
      localPhase p (-(a * v ^ 2)) *
        ∫ x in (L : Set ℚ_[p.val]), localPhase p (a * x ^ 2) ∂lineHaar p a := by
  let f : ℚ_[p.val] → ℂ :=
    (L : Set ℚ_[p.val]).indicator (fun x => localPhase p (a * x ^ 2 + 2 * a * x * v))
  rw [← integral_indicator hL, ← integral_indicator hL, ← integral_const_mul]
  change (∫ x, f x ∂lineHaar p a) = _
  rw [← integral_add_left_eq_self (μ := lineHaar p a) f (-v)]
  congr 1
  funext x
  have he : -v + x ∈ L ↔ x ∈ L := L.add_mem_cancel_left (L.neg_mem hv)
  have hp : a * (-v + x) ^ 2 + 2 * a * (-v + x) * v = -(a * v ^ 2) + a * x ^ 2 := by ring
  by_cases hx : x ∈ L
  · simp only [f, Set.indicator_of_mem hx, Set.indicator_of_mem (he.mpr hx), hp]
    rw [localPhase_add]
  · simp [f, hx, he]

theorem localPhase_congr_integer (p : Place) (x y : ℚ_[p.val])
    (h : x - y ∈ PadicInt.subring p.val) : localPhase p x = localPhase p y := by
  calc
    localPhase p x = localPhase p (x - y + y) := by rw [sub_add_cancel]
    _ = _ := by rw [localPhase_add, (localPhase_eq_one p _).mpr h, one_mul]

/-- The quotient character used by the finite Gaussian integral is
literally the reduction of the local Fourier character. -/
theorem localPhase_integer_div_pow (p : Place) (n : ℕ) (x : ℤ_[p.val]) :
    localPhase p ((x : ℚ_[p.val]) / (p.val : ℚ_[p.val]) ^ n) =
      negativeChar (p.val ^ n) (PadicInt.toZModPow n x) := by
  let j := (PadicInt.toZModPow n x).val
  have hj : (j : ZMod (p.val ^ n)) = PadicInt.toZModPow n x := ZMod.natCast_zmod_val _
  have hk : x - (j : ℤ_[p.val]) ∈ RingHom.ker (PadicInt.toZModPow n) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, hj, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hk
  obtain ⟨y, hy⟩ := hk
  have hy' := congrArg (fun z : ℤ_[p.val] => (z : ℚ_[p.val])) hy
  push_cast at hy'
  have hp : (p.val : ℚ_[p.val]) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have he : (x : ℚ_[p.val]) / (p.val : ℚ_[p.val]) ^ n -
      (j : ℚ_[p.val]) / (p.val : ℚ_[p.val]) ^ n = (y : ℚ_[p.val]) := by
    rw [← sub_div, hy', mul_div_cancel_left₀ _ (pow_ne_zero _ hp)]
  calc
    _ = localPhase p ((j : ℚ_[p.val]) / (p.val : ℚ_[p.val]) ^ n) :=
      localPhase_congr_integer p _ _ (by rw [he]; exact y.property)
    _ = _ := by rw [localPhase_fraction, hj]

/-- At an odd unit coefficient the compact integer ball already gives
the value one for the normalized integral. -/
theorem odd_unit_integral (p : Place) (hp : p ≠ dyadicPlace) (a : ℚ_[p.val]ˣ)
    (ha : valAt p a = 0) :
    (∫ x in (PadicInt.subring p.val : Set ℚ_[p.val]),
      localPhase p ((a : ℚ_[p.val]) * x ^ 2) ∂lineHaar p a) = (finiteGamma p a : ℂ) := by
  have hp2 : p.val ≠ 2 := fun he => hp (Subtype.ext he)
  have h2 : ‖(2 : ℚ_[p.val])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (odd_coprime_two (p.property.odd_of_ne_two hp2))
  have hn : ‖(a : ℚ_[p.val])‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation a.ne_zero, ← valAt, ha, neg_zero, zpow_zero]
  have hm : Real.sqrt ‖2 * (a : ℚ_[p.val])‖ = 1 := by rw [norm_mul, h2, hn, one_mul, Real.sqrt_one]
  have hf : Set.EqOn (fun x => localPhase p ((a : ℚ_[p.val]) * x ^ 2)) (fun _ => (1 : ℂ))
      (PadicInt.subring p.val) := by
    intro x hx
    apply (localPhase_eq_one p _).mpr
    exact (PadicInt.subring p.val).mul_mem hn.le ((PadicInt.subring p.val).pow_mem hx 2)
  rw [setIntegral_congr_fun (padicIntegers_open p).measurableSet hf, setIntegral_const,
    measureReal_def, lineHaar_integerBall, hm, ENNReal.ofReal_one, ENNReal.toReal_one, one_smul,
    finiteGamma_even_odd_place p hp a (by rw [ha]; decide), Units.val_one]

open Classical in
/-- Character orthogonality on a measurable additive subgroup. -/
theorem integral_linearPhase (p : Place) (a t : ℚ_[p.val])
    (L : AddSubgroup ℚ_[p.val]) (hL : MeasurableSet (L : Set ℚ_[p.val])) :
    (∫ x in (L : Set ℚ_[p.val]), localPhase p (t * x) ∂lineHaar p a) =
      if ∀ x ∈ L, t * x ∈ PadicInt.subring p.val
      then ((lineHaar p a).real (L : Set ℚ_[p.val]) : ℂ) else 0 := by
  classical
  split_ifs with h
  · have he : Set.EqOn (fun x => localPhase p (t * x)) (fun _ => (1 : ℂ)) (L : Set ℚ_[p.val]) :=
      fun x hx => (localPhase_eq_one p _).mpr (h x hx)
    rw [setIntegral_congr_fun hL he, setIntegral_const, RCLike.real_smul_eq_coe_mul, mul_one]
    rfl
  · push Not at h
    obtain ⟨y, hy, hny⟩ := h
    let f : ℚ_[p.val] → ℂ := (L : Set ℚ_[p.val]).indicator (fun x => localPhase p (t * x))
    have he (x : ℚ_[p.val]) : f (y + x) = localPhase p (t * y) * f x := by
      have hm : y + x ∈ L ↔ x ∈ L := L.add_mem_cancel_left hy
      by_cases hx : x ∈ L <;> simp [f, hm, hx, mul_add, localPhase_add]
    have hh := integral_add_left_eq_self (μ := lineHaar p a) f y
    simp_rw [he, integral_const_mul] at hh
    rw [← integral_indicator hL]
    by_contra hc
    exact hny ((localPhase_eq_one p _).mp
      (mul_right_cancel₀ hc (hh.trans (one_mul _).symm)))

open Classical in
/-- A coset of a lattice on which the quadratic phase is trivial contributes
only on its polar dual. The integral is expressed after translating the
coset (c+L) back to (L). -/
theorem integral_quadratic_coset (p : Place) (a c : ℚ_[p.val])
    (L : AddSubgroup ℚ_[p.val]) (hL : MeasurableSet (L : Set ℚ_[p.val]))
    (hint : ∀ x ∈ L, a * x ^ 2 ∈ PadicInt.subring p.val) :
    (∫ x in (L : Set ℚ_[p.val]), localPhase p (a * (c + x) ^ 2) ∂lineHaar p a) =
      if ∀ x ∈ L, (2 * a * c) * x ∈ PadicInt.subring p.val then
        localPhase p (a * c ^ 2) * ((lineHaar p a).real (L : Set ℚ_[p.val]) : ℂ)
      else 0 := by
  have he : Set.EqOn (fun x => localPhase p (a * (c + x) ^ 2))
      (fun x => localPhase p (a * c ^ 2) * localPhase p ((2 * a * c) * x))
      (L : Set ℚ_[p.val]) := by
    intro x hx
    change localPhase p (a * (c + x) ^ 2) = _
    rw [show a * (c + x) ^ 2 = (a * c ^ 2 + (2 * a * c) * x) + a * x ^ 2 by ring]
    rw [localPhase_congr_integer p _ (a * c ^ 2 + (2 * a * c) * x)
      (by simpa only [add_sub_cancel_left] using hint x hx), localPhase_add]
  rw [setIntegral_congr_fun hL he, integral_const_mul, integral_linearPhase p a _ L hL]
  split_ifs <;> simp

/-- The cutoff (p^{-N}\mathbb Z_p) used for the oscillatory integral. -/
def cutoffLattice (p : Place) (N : ℕ) : AddSubgroup ℚ_[p.val] :=
  (PadicInt.subring p.val).toAddSubgroup.comap
    { toFun := fun x => (p.val : ℚ_[p.val]) ^ N * x
      map_zero' := mul_zero _
      map_add' := mul_add _ }

theorem cutoffLattice_measurable (p : Place) (N : ℕ) :
    MeasurableSet (cutoffLattice p N : Set ℚ_[p.val]) :=
  (padicIntegers_open p).measurableSet.preimage ((continuous_const.mul continuous_id).measurable)

theorem eventually_cutoffLattice (p : Place) (x : ℚ_[p.val]) :
    ∀ᶠ N : ℕ in Filter.atTop, x ∈ cutoffLattice p N := by
  by_cases hx : x = 0
  · exact Filter.Eventually.of_forall (fun N => hx ▸ (cutoffLattice p N).zero_mem)
  filter_upwards [Filter.eventually_ge_atTop (-x.valuation).toNat] with N hN
  change ‖(p.val : ℚ_[p.val]) ^ N * x‖ ≤ 1
  rw [Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_mul (pow_ne_zero _ (Nat.cast_ne_zero.mpr p.property.ne_zero)) hx,
    Padic.valuation_pow, Padic.valuation_p, mul_one]
  omega

/-- The finite cutoff of the one-dimensional Fourier integral, with
(v) the stationary shift in the polar pairing. -/
def cutoffGaussian (p : Place) (a v : ℚ_[p.val]) (N : ℕ) : ℂ :=
  ∫ x in (cutoffLattice p N : Set ℚ_[p.val]),
    localPhase p (a * x ^ 2 + 2 * a * x * v) ∂lineHaar p a

/-- For all sufficiently large cutoffs the shifted integral reduces
to the one at zero with exactly the manuscript's phase. -/
theorem eventually_cutoffGaussian (p : Place) (a v : ℚ_[p.val]) :
    ∀ᶠ N : ℕ in Filter.atTop,
      cutoffGaussian p a v N = localPhase p (-(a * v ^ 2)) * cutoffGaussian p a 0 N := by
  filter_upwards [eventually_cutoffLattice p v] with N hv
  simpa only [cutoffGaussian, mul_zero, add_zero] using
    integral_completeSquare p a v (cutoffLattice p N) (cutoffLattice_measurable p N) hv


private theorem continuous_localPhase (p : Place) : Continuous (localPhase p) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hn : {y : ℚ_[p.val] | y - x ∈ PadicInt.subring p.val} ∈ 𝓝 x := by
    apply ((padicIntegers_open p).preimage (continuous_id.sub continuous_const)).mem_nhds
    change x - x ∈ PadicInt.subring p.val
    rw [sub_self]
    exact (PadicInt.subring p.val).zero_mem
  change Tendsto (localPhase p) (𝓝 x) (𝓝 (localPhase p x))
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [hn] with y hy
  exact (localPhase_congr_integer p y x hy).symm

private theorem norm_localPhase (p : Place) (x : ℚ_[p.val]) : ‖localPhase p x‖ = 1 := by
  simp [localPhase, rationalPhase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- Polar dual with respect to \(2axy\), written as an intersection of closed subgroups. -/
def polarDualLattice (p : Place) (a : ℚ_[p.val]) (L : AddSubgroup ℚ_[p.val]) :
    Set ℚ_[p.val] :=
  {x | ∀ y ∈ L, (2 * a * x) * y ∈ PadicInt.subring p.val}

private theorem polarDualLattice_measurable (p : Place) (a : ℚ_[p.val])
    (L : AddSubgroup ℚ_[p.val]) : MeasurableSet (polarDualLattice p a L) := by
  have he : polarDualLattice p a L =
      ⋂ y : L, {x | (2 * a * x) * (y : ℚ_[p.val]) ∈ PadicInt.subring p.val} := by
    ext x
    simp [polarDualLattice]
  rw [he]
  apply IsClosed.measurableSet
  exact isClosed_iInter (fun y => (padicIntegers_compact p).isClosed.preimage
    ((continuous_const.mul continuous_id).mul continuous_const))

/-- Averaging over a small compact lattice restricts the quadratic integral to
its polar dual. This makes the cancellation on each coset into cancellation
in any larger compact cutoff. -/
theorem integral_quadratic_polarDual (p : Place) (a : ℚ_[p.val])
    (K L : AddSubgroup ℚ_[p.val]) (hK : IsCompact (K : Set ℚ_[p.val]))
    (hL : IsCompact (L : Set ℚ_[p.val])) (hle : L ≤ K)
    (hvol : (lineHaar p a).real (L : Set ℚ_[p.val]) ≠ 0)
    (hint : ∀ x ∈ L, a * x ^ 2 ∈ PadicInt.subring p.val) :
    (∫ x in (K : Set ℚ_[p.val]), localPhase p (a * x ^ 2) ∂lineHaar p a) =
    (∫ x in (K : Set ℚ_[p.val]) ∩ polarDualLattice p a L,
      localPhase p (a * x ^ 2) ∂lineHaar p a) := by
  classical
  let μ := lineHaar p a
  let f : ℚ_[p.val] → ℂ := fun x => localPhase p (a * x ^ 2)
  let D := polarDualLattice p a L
  let m : ℂ := μ.real (L : Set ℚ_[p.val])
  have hm : m ≠ 0 := Complex.ofReal_ne_zero.mpr hvol
  have hμ : IsFiniteMeasureOnCompacts μ := by
    unfold μ lineHaar
    exact IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top
  have hμK : IsFiniteMeasure (μ.restrict (K : Set ℚ_[p.val])) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hμL : IsFiniteMeasure (μ.restrict (L : Set ℚ_[p.val])) :=
    isFiniteMeasure_restrict.mpr hL.measure_lt_top.ne
  have hK' := hK.isClosed.measurableSet
  have hL' := hL.isClosed.measurableSet
  have hD : MeasurableSet D := polarDualLattice_measurable p a L
  have hf : Integrable (Function.uncurry (fun x y => f (x + y)))
      ((μ.restrict (K : Set ℚ_[p.val])).prod (μ.restrict (L : Set ℚ_[p.val]))) := by
    have hc : Continuous fun z : ℚ_[p.val] × ℚ_[p.val] =>
        localPhase p (a * (z.1 + z.2) ^ 2) :=
      (continuous_localPhase p).comp (continuous_const.mul ((continuous_fst.add continuous_snd).pow 2))
    exact Integrable.of_bound hc.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z => (norm_localPhase p _).le))
  have hur (x : ℚ_[p.val]) :
      (∫ y in (L : Set ℚ_[p.val]), f (x + y) ∂μ) = m * D.indicator f x := by
    rw [show (∫ y in (L : Set ℚ_[p.val]), f (x + y) ∂μ) =
        if x ∈ D then f x * m else 0 from integral_quadratic_coset p a x L hL' hint]
    by_cases hx : x ∈ D <;> simp [hx, mul_comm]
  have hul (y : ℚ_[p.val]) (hy : y ∈ L) :
      (∫ x in (K : Set ℚ_[p.val]), f (x + y) ∂μ) =
      (∫ x in (K : Set ℚ_[p.val]), f x ∂μ) := by
    have he : (fun x => (K : Set ℚ_[p.val]).indicator (fun z => f (z + y)) x) =
        fun x => (K : Set ℚ_[p.val]).indicator f (y + x) := by
      funext x
      have hmem := K.add_mem_cancel_left (hle hy : y ∈ K) (y := x)
      by_cases hx : x ∈ K <;> simp [hx, hmem, add_comm x y]
    rw [← integral_indicator hK', ← integral_indicator hK', he, integral_add_left_eq_self]
  have h := integral_integral_swap hf
  simp_rw [hur] at h
  rw [integral_const_mul, integral_indicator hD, Measure.restrict_restrict hD, Set.inter_comm] at h
  rw [setIntegral_congr_fun hL' hul, setIntegral_const, RCLike.real_smul_eq_coe_mul] at h
  exact (mul_left_cancel₀ hm h).symm


/-- The lattice of \(x\) for which \(cx\) is integral. -/
def scaledLattice (p : Place) (c : ℚ_[p.val]) : AddSubgroup ℚ_[p.val] :=
  (PadicInt.subring p.val).toAddSubgroup.comap
    { toFun := fun x => c * x
      map_zero' := mul_zero _
      map_add' := mul_add _ }

theorem scaledLattice_compact (p : Place) (c : ℚ_[p.val]) (hc : c ≠ 0) :
    IsCompact (scaledLattice p c : Set ℚ_[p.val]) := by
  have he : (scaledLattice p c : Set ℚ_[p.val]) =
      (fun z : ℚ_[p.val] => c⁻¹ * z) '' (PadicInt.subring p.val : Set ℚ_[p.val]) := by
    ext x
    change c * x ∈ PadicInt.subring p.val ↔ _
    constructor
    · exact fun hx => ⟨c * x, hx, inv_mul_cancel_left₀ hc x⟩
    · rintro ⟨z, hz, rfl⟩
      rwa [mul_inv_cancel_left₀ hc]
  rw [he]
  exact (padicIntegers_compact p).image (continuous_const.mul continuous_id)

private theorem eventually_scaledLattice_subset (p : Place) (c : ℚ_[p.val]) (hc : c ≠ 0) :
    ∀ᶠ N : ℕ in Filter.atTop, scaledLattice p c ≤ cutoffLattice p N := by
  filter_upwards [eventually_cutoffLattice p c⁻¹] with N hN x hx
  change ‖(p.val : ℚ_[p.val]) ^ N * c⁻¹‖ ≤ 1 at hN
  change ‖c * x‖ ≤ 1 at hx
  change ‖(p.val : ℚ_[p.val]) ^ N * x‖ ≤ 1
  have he : (p.val : ℚ_[p.val]) ^ N * x = ((p.val : ℚ_[p.val]) ^ N * c⁻¹) * (c * x) := by
    rw [mul_assoc, inv_mul_cancel_left₀ hc]
  rw [he, norm_mul]
  exact (mul_le_mul_of_nonneg_right hN (norm_nonneg _)).trans (by simpa using hx)

theorem polarDualLattice_scaled (p : Place) (a c : ℚ_[p.val]) (hc : c ≠ 0) :
    polarDualLattice p a (scaledLattice p c) =
      (scaledLattice p (2 * a / c) : Set ℚ_[p.val]) := by
  ext x
  change (∀ y, c * y ∈ PadicInt.subring p.val → (2 * a * x) * y ∈ PadicInt.subring p.val) ↔
    (2 * a / c) * x ∈ PadicInt.subring p.val
  constructor
  · intro h
    have hh := h c⁻¹ (by rw [mul_inv_cancel₀ hc]; exact (PadicInt.subring p.val).one_mem)
    rwa [show 2 * a * x * c⁻¹ = (2 * a / c) * x by rw [div_eq_mul_inv]; ring] at hh
  · intro hx y hy
    have he : 2 * a * x * y = ((2 * a / c) * x) * (c * y) := by field_simp
    rw [he]
    exact (PadicInt.subring p.val).mul_mem hx hy

/-- Restriction to the fixed polar dual gives stabilization of the
zero-shift oscillatory integral. -/
theorem eventually_cutoffGaussian_polarDual (p : Place) (a c : ℚ_[p.val])
    (ha : a ≠ 0) (hc : c ≠ 0)
    (hint : ∀ x ∈ scaledLattice p c, a * x ^ 2 ∈ PadicInt.subring p.val) :
    ∀ᶠ N : ℕ in Filter.atTop, cutoffGaussian p a 0 N =
      ∫ x in (scaledLattice p (2 * a / c) : Set ℚ_[p.val]),
        localPhase p (a * x ^ 2) ∂lineHaar p a := by
  have htwo : (2 : ℚ_[p.val]) ≠ 0 := by norm_num
  have hdual := div_ne_zero (mul_ne_zero htwo ha) hc
  have hvol : (lineHaar p a).real (scaledLattice p c : Set ℚ_[p.val]) ≠ 0 := by
    have ho : IsOpen (scaledLattice p c : Set ℚ_[p.val]) :=
      (padicIntegers_open p).preimage (continuous_const.mul continuous_id)
    have hpos : padicHaar p (scaledLattice p c : Set ℚ_[p.val]) ≠ 0 :=
      (ho.measure_pos _ ⟨0, (scaledLattice p c).zero_mem⟩).ne'
    rw [measureReal_def, lineHaar, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    exact mul_ne_zero (Real.sqrt_pos.mpr (norm_pos_iff.mpr (mul_ne_zero htwo ha))).ne'
      ((ENNReal.toReal_pos hpos (scaledLattice_compact p c hc).measure_lt_top.ne).ne')
  filter_upwards [eventually_scaledLattice_subset p c hc,
    eventually_scaledLattice_subset p _ hdual] with N hN hN'
  have hK : IsCompact (cutoffLattice p N : Set ℚ_[p.val]) :=
    scaledLattice_compact p _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr p.property.ne_zero))
  have h := integral_quadratic_polarDual p a (cutoffLattice p N) (scaledLattice p c)
    hK (scaledLattice_compact p c hc) hN hvol hint
  rw [polarDualLattice_scaled p a c hc, Set.inter_eq_right.mpr hN'] at h
  simpa only [cutoffGaussian, mul_zero, add_zero] using h


/-- Every nonzero scalar cutoff stabilizes: the valuation chooses a lattice on
which the quadratic phase is trivial, and the resulting polar dual is fixed. -/
theorem eventually_cutoffGaussian_at_valuation (p : Place) (a : ℚ_[p.val]ˣ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      cutoffGaussian p a 0 N =
        ∫ x in (scaledLattice p (2 * (a : ℚ_[p.val]) /
          (p.val : ℚ_[p.val]) ^ (valAt p a / 2)) : Set ℚ_[p.val]),
          localPhase p ((a : ℚ_[p.val]) * x ^ 2) ∂lineHaar p a := by
  have hp : (p.val : ℚ_[p.val]) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  refine eventually_cutoffGaussian_polarDual p a _ a.ne_zero (zpow_ne_zero _ hp) ?_
  intro x hx
  by_cases h0 : x = 0
  · simp [h0, (PadicInt.subring p.val).zero_mem]
  change ‖(p.val : ℚ_[p.val]) ^ (valAt p a / 2) * x‖ ≤ 1 at hx
  change ‖(a : ℚ_[p.val]) * x ^ 2‖ ≤ 1
  rw [Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_mul (zpow_ne_zero _ hp) h0, Padic.valuation_zpow,
    Padic.valuation_p, mul_one] at hx
  rw [Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_mul a.ne_zero (pow_ne_zero _ h0), Padic.valuation_pow, ← valAt]
  omega

/-- At an odd prime and unit coefficient the normalized oscillatory integral,
also with the linear term, equals the explicit local formula. -/
theorem eventually_odd_unit_integral (p : Place) (hp : p ≠ dyadicPlace)
    (a : ℚ_[p.val]ˣ) (ha : valAt p a = 0) (v : ℚ_[p.val]) :
    ∀ᶠ N : ℕ in Filter.atTop,
      cutoffGaussian p a v N = localPhase p (-((a : ℚ_[p.val]) * v ^ 2)) * (finiteGamma p a : ℂ) := by
  have hp2 : p.val ≠ 2 := fun he => hp (Subtype.ext he)
  have h2 : ‖(2 : ℚ_[p.val])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (odd_coprime_two (p.property.odd_of_ne_two hp2))
  have hn : ‖(a : ℚ_[p.val])‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation a.ne_zero, ← valAt, ha, neg_zero, zpow_zero]
  have hL : (scaledLattice p (2 * (a : ℚ_[p.val]) /
      (p.val : ℚ_[p.val]) ^ (valAt p a / 2)) : Set ℚ_[p.val]) = PadicInt.subring p.val := by
    ext x
    change ‖2 * (a : ℚ_[p.val]) / (p.val : ℚ_[p.val]) ^ (valAt p a / 2) * x‖ ≤ 1 ↔ ‖x‖ ≤ 1
    simp [ha, norm_mul, h2, hn]
  filter_upwards [eventually_cutoffGaussian_at_valuation p a, eventually_cutoffGaussian p a v]
    with N hz hv
  rw [hv, hz, hL, odd_unit_integral p hp a ha]

#print axioms eventually_cutoffGaussian_at_valuation
#print axioms eventually_odd_unit_integral
#print axioms scaledLattice_compact
#print axioms eventually_scaledLattice_subset
#print axioms polarDualLattice_scaled
#print axioms eventually_cutoffGaussian_polarDual
#print axioms continuous_localPhase
#print axioms norm_localPhase
#print axioms polarDualLattice_measurable
#print axioms integral_quadratic_polarDual
#print axioms cutoffLattice_measurable
#print axioms eventually_cutoffLattice
#print axioms eventually_cutoffGaussian
#print axioms integral_linearPhase
#print axioms integral_quadratic_coset
#print axioms lineHaar_integerBall
#print axioms integral_completeSquare
#print axioms localPhase_congr_integer
#print axioms localPhase_integer_div_pow
#print axioms odd_unit_integral

end ZInQ.Manuscript.RC.WeilIndex
