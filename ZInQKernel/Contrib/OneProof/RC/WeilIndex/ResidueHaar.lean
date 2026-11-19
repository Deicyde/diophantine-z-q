import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Integral

/-! The uniform Haar mass of the finite residue fibers of a scaled integer
lattice. This is on-the-spot (c), used for the computation in tex 8746–8753. -/

noncomputable section

namespace ZInQ.Manuscript.RC.WeilIndex

open Intertwine Intertwine2 MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal

private def residueFiber (p : Place) (n : ℕ) (c : ℚ_[p.val]) (j : ZMod (p.val ^ n)) :
    Set ℚ_[p.val] :=
  {x | ∃ z : ℤ_[p.val], c * x = (z : ℚ_[p.val]) ∧ PadicInt.toZModPow n z = j}

private theorem residueFiber_eq (p : Place) (n : ℕ) (c : ℚ_[p.val]) (hc : c ≠ 0)
    (j : ZMod (p.val ^ n)) :
    residueFiber p n c j = (fun x => -(j.val : ℚ_[p.val]) / c + x) ⁻¹'
      (scaledLattice p (c / (p.val : ℚ_[p.val]) ^ n) : Set ℚ_[p.val]) := by
  have hp : (p.val : ℚ_[p.val]) ^ n ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr p.property.ne_zero)
  have hmul (x : ℚ_[p.val]) :
      (c / (p.val : ℚ_[p.val]) ^ n) * (-(j.val : ℚ_[p.val]) / c + x) =
      (c * x - (j.val : ℚ_[p.val])) / (p.val : ℚ_[p.val]) ^ n := by
    field_simp
    ring
  have hkernel (z : ℤ_[p.val]) :
      PadicInt.toZModPow n z = j ↔
        ∃ y : ℤ_[p.val], z - (j.val : ℤ_[p.val]) = (p.val : ℤ_[p.val]) ^ n * y := by
    change _ ↔ (p.val : ℤ_[p.val]) ^ n ∣ z - (j.val : ℤ_[p.val])
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
      map_sub, map_natCast, ZMod.natCast_zmod_val, sub_eq_zero]
  ext x
  change (∃ z : ℤ_[p.val], c * x = (z : ℚ_[p.val]) ∧ PadicInt.toZModPow n z = j) ↔
    (c / (p.val : ℚ_[p.val]) ^ n) * (-(j.val : ℚ_[p.val]) / c + x) ∈ PadicInt.subring p.val
  rw [hmul]
  constructor
  · rintro ⟨z, hz, hj⟩
    obtain ⟨y, hy⟩ := (hkernel z).1 hj
    have hy' := congrArg (fun z : ℤ_[p.val] => (z : ℚ_[p.val])) hy
    push_cast at hy'
    rw [hz, hy', mul_div_cancel_left₀ _ hp]
    exact y.property
  · intro hx
    let y : ℤ_[p.val] := ⟨(c * x - (j.val : ℚ_[p.val])) / (p.val : ℚ_[p.val]) ^ n, hx⟩
    let z := (p.val : ℤ_[p.val]) ^ n * y + (j.val : ℤ_[p.val])
    have hz : c * x = (z : ℚ_[p.val]) := by
      change _ = (((p.val : ℤ_[p.val]) ^ n * y + (j.val : ℤ_[p.val]) : ℤ_[p.val]) : ℚ_[p.val])
      push_cast
      change _ = _ * ((c * x - _) / _) + _
      rw [mul_comm ((p.val : ℚ_[p.val]) ^ n), div_mul_cancel₀ _ hp, sub_add_cancel]
    exact ⟨z, hz, (hkernel z).2 ⟨y, add_sub_cancel_right _ _⟩⟩

private theorem iUnion_residueFiber (p : Place) (n : ℕ) (c : ℚ_[p.val]) :
    (⋃ j : ZMod (p.val ^ n), residueFiber p n c j) = (scaledLattice p c : Set ℚ_[p.val]) := by
  ext x
  rw [Set.mem_iUnion]
  change (∃ j : ZMod (p.val ^ n), ∃ z : ℤ_[p.val], c * x = (z : ℚ_[p.val]) ∧
      PadicInt.toZModPow n z = j) ↔ c * x ∈ PadicInt.subring p.val
  constructor
  · rintro ⟨j, z, hz, _⟩
    rw [hz]
    exact z.property
  · intro hx
    exact ⟨PadicInt.toZModPow n ⟨c * x, hx⟩, ⟨c * x, hx⟩, rfl, rfl⟩

private theorem residueFiber_disjoint (p : Place) (n : ℕ) (c : ℚ_[p.val]) :
    Pairwise (fun i j => Disjoint (residueFiber p n c i) (residueFiber p n c j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro x ⟨z, hz, hi⟩ ⟨y, hy, hj⟩
  have hz' : z = y := Subtype.ext (hz.symm.trans hy)
  exact hij (hi.symm.trans (hz' ▸ hj))

/-- A function factoring through the residue ring on a scaled lattice has
integral equal to the finite sum times the common fiber mass. -/
theorem integral_scaledLattice_residue (p : Place) (a c : ℚ_[p.val]) (hc : c ≠ 0) (n : ℕ)
    (f : ZMod (p.val ^ n) → ℂ) (g : ℚ_[p.val] → ℂ)
    (hg : ∀ (x : ℚ_[p.val]) (z : ℤ_[p.val]), c * x = (z : ℚ_[p.val]) →
      g x = f (PadicInt.toZModPow n z)) :
    (∫ x in (scaledLattice p c : Set ℚ_[p.val]), g x ∂lineHaar p a) =
      ((lineHaar p a).real (scaledLattice p (c / (p.val : ℚ_[p.val]) ^ n) :
        Set ℚ_[p.val]) : ℂ) * ∑ j, f j := by
  classical
  let μ := lineHaar p a
  have hμ : IsFiniteMeasureOnCompacts μ := by
    unfold μ lineHaar
    exact IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top
  let D := (scaledLattice p (c / (p.val : ℚ_[p.val]) ^ n) : Set ℚ_[p.val])
  have hd : IsCompact D := scaledLattice_compact p _
    (div_ne_zero hc (pow_ne_zero _ (Nat.cast_ne_zero.mpr p.property.ne_zero)))
  have hmeas (j : ZMod (p.val ^ n)) : MeasurableSet (residueFiber p n c j) := by
    rw [residueFiber_eq p n c hc j]
    exact hd.isClosed.measurableSet.preimage (continuous_const.add continuous_id).measurable
  have hmass (j : ZMod (p.val ^ n)) : μ (residueFiber p n c j) = μ D := by
    rw [residueFiber_eq p n c hc j, measure_preimage_add]
  have hg' (j : ZMod (p.val ^ n)) :
      Set.EqOn g (fun _ => f j) (residueFiber p n c j) := by
    rintro x ⟨z, hz, hj⟩
    rw [hg x z hz, hj]
  rw [← iUnion_residueFiber p n c, integral_iUnion_fintype hmeas (residueFiber_disjoint p n c)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [setIntegral_congr_fun (hmeas j) (hg' j), setIntegral_const,
      RCLike.real_smul_eq_coe_mul, measureReal_def, hmass]
    rfl
  · intro j
    exact (integrableOn_congr_fun (hg' j) (hmeas j)).2
      (integrableOn_const (by rw [hmass]; exact hd.measure_lt_top.ne))

/-- The kernel lattice has index \(p^n\) in the lattice being reduced;
this is also the ratio of their real Haar masses. -/
theorem lineHaar_scaledLattice_div (p : Place) (a c : ℚ_[p.val]) (hc : c ≠ 0) (n : ℕ) :
    (lineHaar p a).real (scaledLattice p c : Set ℚ_[p.val]) =
      ((p.val : ℝ) ^ n) * (lineHaar p a).real
        (scaledLattice p (c / (p.val : ℚ_[p.val]) ^ n) : Set ℚ_[p.val]) := by
  have h := integral_scaledLattice_residue p a c hc n (fun _ => 1) (fun _ => 1)
    (fun _ _ _ => rfl)
  rw [setIntegral_const, RCLike.real_smul_eq_coe_mul, mul_one, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one, mul_comm] at h
  apply Complex.ofReal_inj.mp
  rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast,
    ← Nat.cast_pow]
  exact h


private theorem scaledLattice_one (p : Place) :
    (scaledLattice p 1 : Set ℚ_[p.val]) = PadicInt.subring p.val := by
  ext x
  change 1 * x ∈ PadicInt.subring p.val ↔ x ∈ PadicInt.subring p.val
  rw [one_mul]

/-- A uniformizer power changes the unit ball's additive measure by the
reciprocal of its \(p\)-adic norm in the preimage convention. -/
theorem lineHaar_scaledLattice_zpow (p : Place) (a : ℚ_[p.val]) (k : ℤ) :
    (lineHaar p a).real (scaledLattice p ((p.val : ℚ_[p.val]) ^ k) : Set ℚ_[p.val]) =
      (p.val : ℝ) ^ k * Real.sqrt ‖2 * a‖ := by
  have hp : (p.val : ℚ_[p.val]) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have hpR : (p.val : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have h1 : (lineHaar p a).real (scaledLattice p 1 : Set ℚ_[p.val]) = Real.sqrt ‖2 * a‖ := by
    rw [scaledLattice_one, measureReal_def, lineHaar_integerBall,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · simp only [zpow_natCast]
    rw [lineHaar_scaledLattice_div p a _ (pow_ne_zero _ hp) n,
      div_self (pow_ne_zero _ hp), h1]
  · have h := lineHaar_scaledLattice_div p a 1 one_ne_zero n
    rw [h1, one_div] at h
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, mul_comm]
    exact (eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hpR)).2 (by rw [mul_comm, ← h])

/-- Polar Haar masses of scaled integer lattices depend on the valuation
of the scalar multiplying the coordinate. -/
theorem scaledLattice_eq_of_valuation (p : Place) (b c : ℚ_[p.val]) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : b.valuation = c.valuation) : scaledLattice p b = scaledLattice p c := by
  ext x
  change ‖b * x‖ ≤ 1 ↔ ‖c * x‖ ≤ 1
  simp only [norm_mul, Padic.norm_eq_zpow_neg_valuation hb,
    Padic.norm_eq_zpow_neg_valuation hc, h]

/-- The unnormalized local sum at depth (n), in the valuation-unit coordinate. -/
def unitResidueSum (p : Place) (a : ℚ_[p.val]ˣ) (n : ℕ) : ℂ :=
  quadraticSum (p.val ^ n) (PadicInt.toZModPow n (unitAt p a : ℤ_[p.val]))

/-- Scalar oscillatory integral as the normalized Gauss sum at the required
residue modulus. The depth is \(e+2d\) and the denominator is
\(p^{(e+3d)/2}\), with \(e=v_p(a)\bmod 2\), \(d=v_p(2)\). -/
theorem eventually_cutoffGaussian_eq_quadraticSum (p : Place) (a : ℚ_[p.val]ˣ) :
    let d := padicValNat p.val 2
    let e := (valAt p a % 2).toNat
    ∀ᶠ N : ℕ in Filter.atTop, cutoffGaussian p a 0 N =
      unitResidueSum p a (e + 2 * d) /
        (Real.sqrt ((p.val : ℝ) ^ (e + 3 * d)) : ℂ) := by
  let v := valAt p a
  let d := padicValNat p.val 2
  let e := (v % 2).toNat
  let k := v / 2
  let l := (d : ℤ) + v - k
  let n := e + 2 * d
  let P := (p.val : ℚ_[p.val])
  let Pr := (p.val : ℝ)
  let u : ℤ_[p.val] := unitAt p a
  have hP : P ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have hPr : 0 < Pr := Nat.cast_pos.mpr p.property.pos
  have htwo : (2 : ℚ_[p.val]) ≠ 0 := by norm_num
  have hd : (2 : ℚ_[p.val]).valuation = d := Padic.valuation_natCast 2
  have h2a : (2 * (a : ℚ_[p.val])).valuation = (d : ℤ) + v := by
    rw [Padic.valuation_mul htwo a.ne_zero, hd]
    rfl
  have he : (e : ℤ) = v % 2 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  have hln : v - 2 * l = -(n : ℤ) := by
    simp only [l, n, k, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    omega
  have hau : (u : ℚ_[p.val]) * P ^ v = (a : ℚ_[p.val]) := by
    rw [show (u : ℚ_[p.val]) = (a : ℚ_[p.val]) * P ^ (-v) from unitAt_coe p a,
      mul_assoc, ← zpow_add₀ hP, neg_add_cancel, zpow_zero, mul_one]
  have hL : scaledLattice p (2 * (a : ℚ_[p.val]) / P ^ k) = scaledLattice p (P ^ l) := by
    apply scaledLattice_eq_of_valuation p _ _
      (div_ne_zero (mul_ne_zero htwo a.ne_zero) (zpow_ne_zero _ hP)) (zpow_ne_zero _ hP)
    have hval (j : ℤ) : (P ^ j).valuation = j := by
      rw [Padic.valuation_zpow, show P.valuation = 1 from Padic.valuation_p, mul_one]
    rw [div_eq_mul_inv, Padic.valuation_mul (mul_ne_zero htwo a.ne_zero)
      (inv_ne_zero (zpow_ne_zero _ hP)), Padic.valuation_inv, h2a, hval, hval]
    simp only [l, sub_eq_add_neg]
  have hfun (x : ℚ_[p.val]) (z : ℤ_[p.val]) (hz : P ^ l * x = (z : ℚ_[p.val])) :
      localPhase p ((a : ℚ_[p.val]) * x ^ 2) =
        negativeChar (p.val ^ n)
          (PadicInt.toZModPow n u * (PadicInt.toZModPow n z) ^ 2) := by
    have harg : (a : ℚ_[p.val]) * x ^ 2 =
        (((u * z ^ 2 : ℤ_[p.val]) : ℚ_[p.val])) / P ^ n := by
      push_cast
      rw [← hz, mul_pow, ← hau, div_eq_mul_inv, ← zpow_natCast P n, ← zpow_neg,
        ← hln, show v - 2 * l = v + -(l * 2) by ring, zpow_add₀ hP, zpow_neg,
        zpow_mul]
      field_simp
    rw [harg, localPhase_integer_div_pow, map_mul, map_pow]
  have hμ : (lineHaar p a).real (scaledLattice p (P ^ l / P ^ n) : Set ℚ_[p.val]) =
      (Real.sqrt (Pr ^ (e + 3 * d)))⁻¹ := by
    rw [← zpow_natCast P n, ← zpow_sub₀ hP,
      lineHaar_scaledLattice_zpow, Padic.norm_eq_zpow_neg_valuation (mul_ne_zero htwo a.ne_zero),
      h2a]
    change Pr ^ (l - (n : ℤ)) * Real.sqrt (Pr ^ (-((d : ℤ) + v))) = _
    have hexp : 2 * (l - (n : ℤ)) - ((d : ℤ) + v) = -((e + 3 * d : ℕ) : ℤ) := by
      simp only [l, n, k, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      omega
    have hh := calc
      (Pr ^ (l - (n : ℤ)) * Real.sqrt (Pr ^ (-((d : ℤ) + v)))) ^ 2 =
          Pr ^ (2 * (l - (n : ℤ)) - ((d : ℤ) + v)) := by
        rw [mul_pow, Real.sq_sqrt (zpow_nonneg hPr.le _), ← zpow_natCast (Pr ^ (l - (n : ℤ))) 2,
          ← zpow_mul, ← zpow_add₀ hPr.ne']
        congr 1
        ring
      _ = (Pr ^ (e + 3 * d))⁻¹ := by rw [hexp, zpow_neg, zpow_natCast]
    have := congrArg Real.sqrt hh
    rwa [Real.sqrt_sq (mul_nonneg (zpow_nonneg hPr.le _) (Real.sqrt_nonneg _)), Real.sqrt_inv] at this
  change ∀ᶠ N : ℕ in Filter.atTop, cutoffGaussian p a 0 N =
    quadraticSum (p.val ^ n) (PadicInt.toZModPow n u) /
      (Real.sqrt (Pr ^ (e + 3 * d)) : ℂ)
  filter_upwards [eventually_cutoffGaussian_at_valuation p a] with N hN
  change cutoffGaussian p a 0 N =
    ∫ x in (scaledLattice p (2 * (a : ℚ_[p.val]) / P ^ k) : Set ℚ_[p.val]),
      localPhase p ((a : ℚ_[p.val]) * x ^ 2) ∂lineHaar p a at hN
  rw [hN, hL, integral_scaledLattice_residue p a _ (zpow_ne_zero _ hP) n
    (fun j => negativeChar (p.val ^ n) (PadicInt.toZModPow n u * j ^ 2)) _ hfun,
    hμ, Complex.ofReal_inv, quadraticSum, div_eq_mul_inv, mul_comm]

private theorem quadraticSum_cast {n m : ℕ} [NeZero n] [NeZero m] (h : n = m)
    (u : ZMod n) : quadraticSum n u = quadraticSum m (ZMod.cast u) := by
  subst m
  rw [ZMod.cast_id]

private theorem toZModPow_one (p : Place) (x : ℤ_[p.val]) :
    (ZMod.cast (PadicInt.toZModPow 1 x) : ZMod p.val) = PadicInt.toZMod x := by
  have hk := PadicInt.toZMod_spec (x := x)
  rw [PadicInt.maximalIdeal_eq_span_p, ← pow_one (p.val : ℤ_[p.val]),
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hk
  rw [hk, ZMod.cast_eq_val (R := ℤ_[p.val])]
  change (ZMod.cast (PadicInt.toZModPow 1 ((PadicInt.toZMod x).val : ℤ_[p.val])) :
    ZMod p.val) = PadicInt.toZMod x
  rw [map_natCast, ZMod.cast_natCast (by simp : p.val ∣ p.val ^ 1), ZMod.natCast_zmod_val]

private theorem depth_two_odd (p : Place) (hp : p ≠ dyadicPlace) :
    padicValNat p.val 2 = 0 := by
  refine padicValNat.eq_zero_of_not_dvd ?_
  intro hd
  exact hp (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp hd))

/-- Every even valuation at an odd prime gives the actual index one. -/
theorem eventually_odd_evenGauss (p : Place) (hp : p ≠ dyadicPlace) (a : ℚ_[p.val]ˣ)
    (ha : valAt p a % 2 = 0) :
    ∀ᶠ N : ℕ in Filter.atTop, cutoffGaussian p a 0 N = (finiteGamma p a : ℂ) := by
  have h := eventually_cutoffGaussian_eq_quadraticSum p a
  dsimp only at h
  simp only [ha, depth_two_odd p hp, Int.toNat_zero, mul_zero, add_zero] at h
  filter_upwards [h] with N hN
  rw [hN, finiteGamma_even_odd_place p hp a ha, Units.val_one, unitResidueSum,
    quadraticSum_cast (pow_zero p.val)]
  simp only [pow_zero, Real.sqrt_one, Complex.ofReal_one, div_one]
  have hs (u : ZMod 1) : quadraticSum 1 u = 1 := by
    rw [quadraticSum, Finset.sum_eq_single 0]
    · simp
    · intro b _ h
      exact False.elim (h (Subsingleton.elim _ _))
    · simp
      exact Subsingleton.elim _ _
  exact hs _

/-- Every odd valuation at an odd prime gives the normalized ordinary
quadratic Gauss sum for the local negative character. -/
theorem eventually_odd_oddGauss (p : Place) (hp : p ≠ dyadicPlace) (a : ℚ_[p.val]ˣ)
    (ha : valAt p a % 2 ≠ 0) :
    ∀ᶠ N : ℕ in Filter.atTop, cutoffGaussian p a 0 N =
      oddGauss p (oddUnitResidue p a) := by
  have he : valAt p a % 2 = 1 := by omega
  have h := eventually_cutoffGaussian_eq_quadraticSum p a
  dsimp only at h
  simp only [he, depth_two_odd p hp, Int.toNat_one, mul_zero, add_zero] at h
  filter_upwards [h] with N hN
  rw [hN, unitResidueSum, quadraticSum_cast (pow_one p.val), toZModPow_one, pow_one, oddGauss]
  rfl

/-- At two the normalized oscillatory integral is the explicit
eighth-root phase in both valuation parity cases. -/
theorem eventually_dyadic_Gauss (a : ℚ_[dyadicPlace.val]ˣ) :
    ∀ᶠ N : ℕ in Filter.atTop, cutoffGaussian dyadicPlace a 0 N = (finiteGamma dyadicPlace a : ℂ) := by
  have hd : padicValNat dyadicPlace.val 2 = 1 := padicValNat_self
  have h := eventually_cutoffGaussian_eq_quadraticSum dyadicPlace a
  dsimp only at h
  by_cases ha : valAt dyadicPlace a % 2 = 0
  · simp only [ha, hd, Int.toNat_zero] at h
    filter_upwards [h] with N hN
    rw [finiteGamma, finiteExponent_dyadic]
    change cutoffGaussian dyadicPlace a 0 N =
      (exponentRoot (dyadicExponent (decide (valAt dyadicPlace a % 2 ≠ 0))
        (dyadicUnitResidue a : ZMod 8)) : ℂ)
    simp only [ha, ne_eq, not_true_eq_false, decide_false]
    rw [hN]
    change quadraticSum 4 (PadicInt.toZModPow 2 (unitAt dyadicPlace a : ℤ_[2])) /
      (Real.sqrt ((2 : ℝ) ^ 3) : ℂ) = _
    rw [show Real.sqrt ((2 : ℝ) ^ 3) = 2 * Real.sqrt 2 by
      rw [pow_succ, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]]
    push_cast
    rw [← PadicInt.cast_toZModPow 2 3 (by decide) (unitAt dyadicPlace a : ℤ_[2])]
    exact dyadic_evenGauss (dyadicUnitResidue a)
  · have he : valAt dyadicPlace a % 2 = 1 := by omega
    simp only [he, hd, Int.toNat_one] at h
    filter_upwards [h] with N hN
    rw [finiteGamma, finiteExponent_dyadic]
    rw [show decide (valAt dyadicPlace a % 2 ≠ 0) = true from decide_eq_true ha, hN]
    change quadraticSum 8 (dyadicUnitResidue a : ZMod 8) /
      (Real.sqrt ((2 : ℝ) ^ 4) : ℂ) = _
    rw [show Real.sqrt ((2 : ℝ) ^ 4) = 4 by
      rw [show (2 : ℝ) ^ 4 = (4 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact dyadic_oddGauss (dyadicUnitResidue a)

/-- The actual finite Weil index: the exceptional odd-valuation odd-prime
branch is defined by its Gauss integral rather than a chosen square root. -/
def gaussGamma : FiniteIndexFamily := fun p a =>
  if hp : p ≠ dyadicPlace ∧ valAt p a % 2 ≠ 0 then
    Units.mk0 (oddGauss p (oddUnitResidue p a)) (by
      have hp2 : p.val ≠ 2 := fun h => hp.1 (Subtype.ext h)
      have hs := oddGauss_sq p hp2 (oddUnitResidue p a)
      intro hz
      rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
      have hn : ZMod.χ₄ (p.val : ZMod 4) ≠ 0 := by
        rw [ZMod.χ₄_nat_eq_if_mod_four]
        have hpodd := Nat.odd_iff.mp (p.property.odd_of_ne_two hp2)
        have hz : p.val % 2 ≠ 0 := by omega
        rw [ite_eq_right hz]
        split <;> decide
      exact hn (by exact_mod_cast hs.symm))
  else finiteGamma p a

/-- The actual finite index gives the scalar in the shifted, normalized
oscillatory Fourier integral with the inherited local character. -/
theorem eventually_cutoffGaussian_gaussGamma (p : Place) (a : ℚ_[p.val]ˣ) (v : ℚ_[p.val]) :
    ∀ᶠ N : ℕ in Filter.atTop, cutoffGaussian p a v N =
      localPhase p (-((a : ℚ_[p.val]) * v ^ 2)) * (gaussGamma p a : ℂ) := by
  have h0 : ∀ᶠ N : ℕ in Filter.atTop, cutoffGaussian p a 0 N = (gaussGamma p a : ℂ) := by
    by_cases hp : p = dyadicPlace
    · subst p
      simpa only [gaussGamma, ne_eq, not_true_eq_false, false_and, dite_false] using
        eventually_dyadic_Gauss a
    · by_cases ha : valAt p a % 2 = 0
      · simpa only [gaussGamma, ha, ne_eq, not_true_eq_false, and_false, dite_false] using
          eventually_odd_evenGauss p hp a ha
      · rw [gaussGamma, dite_eq_left ⟨hp, ha⟩, Units.val_mk0]
        exact eventually_odd_oddGauss p hp a ha
  filter_upwards [eventually_cutoffGaussian p a v, h0] with N hN hz
  rw [hN, hz]

#print axioms quadraticSum_cast
#print axioms toZModPow_one
#print axioms depth_two_odd
#print axioms eventually_odd_evenGauss
#print axioms eventually_odd_oddGauss
#print axioms eventually_dyadic_Gauss
#print axioms eventually_cutoffGaussian_gaussGamma
#print axioms eventually_cutoffGaussian_eq_quadraticSum
#print axioms scaledLattice_one
#print axioms lineHaar_scaledLattice_zpow
#print axioms scaledLattice_eq_of_valuation
#print axioms residueFiber_eq
#print axioms iUnion_residueFiber
#print axioms residueFiber_disjoint
#print axioms integral_scaledLattice_residue
#print axioms lineHaar_scaledLattice_div

end ZInQ.Manuscript.RC.WeilIndex
