import ZInQKernel.Contrib.OneProof.RC.LocalDivision.Algebra
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! The compact open integral quaternion order and its maximality.
The proof by the reduced norm is provenance (c). -/

namespace ZInQ.Manuscript.RC.LocalDivision

open QuaternionAlgebra Set Topology
open scoped Quaternion

variable {p : ℕ} [Fact p.Prime]

/-- The integral quaternion presentation on the same basis. -/
abbrev IntegralD (p : ℕ) [Fact p.Prime] := QuaternionAlgebra ℤ_[p] (-1) 0 (-(p : ℤ_[p]))

/-- Entrywise inclusion of the integral presentation. -/
noncomputable def includeIntegral : IntegralD p →ₐ[ℤ_[p]] D p where
  toFun x := ⟨x.re, x.imI, x.imJ, x.imK⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

theorem includeIntegral_injective : Function.Injective (includeIntegral (p := p)) := by
  intro x y h
  exact QuaternionAlgebra.ext
    (Subtype.ext (congrArg QuaternionAlgebra.re h))
    (Subtype.ext (congrArg QuaternionAlgebra.imI h))
    (Subtype.ext (congrArg QuaternionAlgebra.imJ h))
    (Subtype.ext (congrArg QuaternionAlgebra.imK h))

/-- The span of the integral quaternion basis, as a subalgebra. -/
noncomputable def order (p : ℕ) [Fact p.Prime] : Subalgebra ℤ_[p] (D p) :=
  includeIntegral.range

noncomputable def orderEquiv : IntegralD p ≃ₐ[ℤ_[p]] order p :=
  AlgEquiv.ofBijective includeIntegral.rangeRestrict
    ⟨fun _ _ h => includeIntegral_injective (congrArg Subtype.val h),
      fun ⟨_, x, h⟩ => ⟨x, Subtype.ext h⟩⟩

@[simp] theorem coe_orderEquiv (x : IntegralD p) : (orderEquiv x).val = includeIntegral x := rfl

@[simp] theorem includeIntegral_symm (x : order p) :
    includeIntegral (orderEquiv.symm x) = x.val := by
  rw [← coe_orderEquiv, AlgEquiv.apply_symm_apply]

theorem mem_order (x : D p) : x ∈ order p ↔
    ‖x.re‖ ≤ 1 ∧ ‖x.imI‖ ≤ 1 ∧ ‖x.imJ‖ ≤ 1 ∧ ‖x.imK‖ ≤ 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.re.property, y.imI.property, y.imJ.property, y.imK.property⟩
  · rintro ⟨ha, hb, hc, hd⟩
    exact ⟨⟨⟨x.re, ha⟩, ⟨x.imI, hb⟩, ⟨x.imJ, hc⟩, ⟨x.imK, hd⟩⟩, mk.eta x⟩

theorem finite_order : Module.Finite ℤ_[p] (order p) :=
  Module.Finite.of_surjective orderEquiv.toLinearMap orderEquiv.surjective

theorem order_open : IsOpen (order p : Set (D p)) := by
  have h : IsOpen {x : ℚ_[p] | ‖x‖ ≤ 1} := by
    simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
      IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero
  have hs := (h.prod (h.prod (h.prod h))).preimage (coordHomeomorph (p := p)).continuous
  convert hs using 1
  ext x
  exact mem_order x

theorem order_compact : IsCompact (order p : Set (D p)) := by
  have h : IsCompact {x : ℚ_[p] | ‖x‖ ≤ 1} :=
    isCompact_iff_compactSpace.mpr (PadicInt.compactSpace p)
  have hs := (h.prod (h.prod (h.prod h))).image (coordHomeomorph (p := p)).symm.continuous
  convert hs using 1
  ext x
  change x ∈ order p ↔ x ∈ (coordHomeomorph (p := p)).toEquiv.symm '' _
  rw [Equiv.image_symm_eq_preimage]
  exact mem_order x

/-- The four integral coordinates, as continuous maps on the order. -/
theorem orderCoord_continuous :
    Continuous (fun x : order p =>
      QuaternionAlgebra.equivProd _ _ _ (orderEquiv.symm x)) := by
  apply (PadicInt.isOpenEmbedding_coe.prodMap (PadicInt.isOpenEmbedding_coe.prodMap
    (PadicInt.isOpenEmbedding_coe.prodMap PadicInt.isOpenEmbedding_coe))).isEmbedding.continuous_iff.mpr
  convert (coordHomeomorph (p := p)).continuous.comp
    (continuous_subtype_val : Continuous (Subtype.val : order p → D p)) using 1
  funext x
  exact congrArg (coordHomeomorph (p := p)) (includeIntegral_symm x)

variable [Fact (p % 4 = 3)]

omit [Fact (p % 4 = 3)] in
private theorem norm_le_one_of_weighted_sq {a : ℚ_[p]} (h : ‖(p : ℚ_[p])‖ * ‖a‖ ^ 2 ≤ 1) :
    ‖a‖ ≤ 1 := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [← zpow_zero (p : ℝ), Padic.norm_le_pow_iff_norm_lt_pow_add_one]
  simp only [zero_add, zpow_one]
  by_contra! ha
  rw [Padic.norm_p, inv_mul_le_iff₀ (zero_lt_one.trans hp)] at h
  nlinarith

/-- A quaternion lies in the order exactly when its reduced norm is integral. -/
theorem mem_order_iff_nrd (x : D p) :
    x ∈ order p ↔ ‖nrd x‖ ≤ 1 := by
  rw [mem_order, norm_nrd, max_le_iff]
  constructor
  · rintro ⟨ha, hb, hc, hd⟩
    exact ⟨pow_le_one₀ (le_trans (norm_nonneg _) (le_max_left _ _)) (max_le ha hb),
      (mul_le_of_le_one_left (by positivity) Padic.norm_p_lt_one.le).trans
        (pow_le_one₀ (le_trans (norm_nonneg _) (le_max_left _ _)) (max_le hc hd))⟩
  · rintro ⟨hab, hcd⟩
    have hcd' : ∀ a : ℚ_[p], ‖a‖ ≤ max ‖x.imJ‖ ‖x.imK‖ → ‖a‖ ≤ 1 := by
      intro a ha
      apply norm_le_one_of_weighted_sq
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ha 2)
        (norm_nonneg _)).trans hcd
    have hab' : max ‖x.re‖ ‖x.imI‖ ≤ 1 := by
      nlinarith [le_max_left ‖x.re‖ ‖x.imI‖, norm_nonneg x.re]
    exact ⟨(le_max_left _ _).trans hab', (le_max_right _ _).trans hab',
      hcd' _ (le_max_left _ _), hcd' _ (le_max_right _ _)⟩

theorem mem_order_iff_valuation (x : D p) :
    x ∈ order p ↔ 0 ≤ (nrd x).valuation :=
  (mem_order_iff_nrd x).trans (Padic.norm_le_one_iff_val_nonneg _)

theorem nrd_valuation_mul (x y : D p) (hx : x ≠ 0) (hy : y ≠ 0) :
    (nrd (x * y)).valuation = (nrd x).valuation + (nrd y).valuation := by
  rw [map_mul, Padic.valuation_mul (mt (nrd_eq_zero x).mp hx) (mt (nrd_eq_zero y).mp hy)]

theorem norm_nrd_add_le_max (x y : D p) :
    ‖nrd (x + y)‖ ≤ max ‖nrd x‖ ‖nrd y‖ := by
  let q := max ‖nrd x‖ ‖nrd y‖
  have bound (a b c d : ℚ_[p]) (r : ℝ) (hr : 0 ≤ r)
      (h₁ : r * max ‖a‖ ‖c‖ ^ 2 ≤ q) (h₂ : r * max ‖b‖ ‖d‖ ^ 2 ≤ q) :
      r * max ‖a + b‖ ‖c + d‖ ^ 2 ≤ q := by
    have hle : max ‖a + b‖ ‖c + d‖ ≤ max (max ‖a‖ ‖c‖) (max ‖b‖ ‖d‖) := by
      refine max_le ((Padic.nonarchimedean _ _).trans (max_le ?_ ?_))
        ((Padic.nonarchimedean _ _).trans (max_le ?_ ?_))
      · exact (le_max_left _ _).trans (le_max_left _ _)
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_right _ _).trans (le_max_left _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
    refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hle 2) hr).trans ?_
    rcases le_total (max ‖a‖ ‖c‖) (max ‖b‖ ‖d‖) with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  have ha (z : D p) : max ‖z.re‖ ‖z.imI‖ ^ 2 ≤ ‖nrd z‖ :=
    (le_max_left _ _).trans_eq (norm_nrd z).symm
  have hb (z : D p) : ‖(p : ℚ_[p])‖ * max ‖z.imJ‖ ‖z.imK‖ ^ 2 ≤ ‖nrd z‖ :=
    (le_max_right _ _).trans_eq (norm_nrd z).symm
  rw [norm_nrd]
  apply max_le
  · change max ‖x.re + y.re‖ ‖x.imI + y.imI‖ ^ 2 ≤ q
    simpa only [one_mul] using bound x.re y.re x.imI y.imI 1 zero_le_one
      (by rw [one_mul]; exact (ha x).trans (le_max_left _ _))
      (by rw [one_mul]; exact (ha y).trans (le_max_right _ _))
  · exact bound x.imJ y.imJ x.imK y.imK _ (norm_nonneg _)
      ((hb x).trans (le_max_left _ _)) ((hb y).trans (le_max_right _ _))

/-- Integrality forces the norm to be integral: otherwise the leading term of a
monic integral equation has strictly larger norm than every lower term. -/
theorem integral_mem_order {x : D p} (hx : IsIntegral ℤ_[p] x) : x ∈ order p := by
  rw [mem_order_iff_nrd]
  by_contra! hbad
  obtain ⟨f, hf, he⟩ := hx
  change Polynomial.aeval x f = 0 at he
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, ← Polynomial.leadingCoeff,
    hf, one_smul] at he
  let r := ‖nrd x‖ ^ f.natDegree
  have hr : 0 < r := pow_pos (zero_lt_one.trans hbad) _
  have hb (i : ℕ) (hi : i < f.natDegree) : ‖nrd (f.coeff i • x ^ i)‖ < r := by
    rw [Algebra.smul_def, map_mul, map_pow, norm_mul, norm_pow]
    have hc : ‖nrd (algebraMap ℤ_[p] (D p) (f.coeff i))‖ ≤ 1 :=
      (mem_order_iff_nrd _).mp ((order p).algebraMap_mem _)
    exact (mul_le_of_le_one_left (by positivity) hc).trans_lt (pow_lt_pow_right₀ hbad hi)
  have hs (n : ℕ) (hn : n ≤ f.natDegree) :
      ‖nrd (∑ i ∈ Finset.range n, f.coeff i • x ^ i)‖ < r := by
    induction n with
    | zero => simpa [nrd_formula] using hr
    | succ k ih =>
      rw [Finset.sum_range_succ]
      exact (norm_nrd_add_le_max _ _).trans_lt
        (max_lt (ih (by omega)) (hb k (by omega)))
  have ht := hs f.natDegree le_rfl
  rw [eq_neg_of_add_eq_zero_left he] at ht
  have hneg (z : D p) : nrd (-z) = nrd z := by simp [nrd_formula]
  rw [hneg, map_pow, norm_pow] at ht
  exact (lt_irrefl r) ht

/-- The integral basis order is maximal among finite subalgebras containing it. -/
theorem maximal_order (S : Subalgebra ℤ_[p] (D p)) (hS : Module.Finite ℤ_[p] S)
    (h : order p ≤ S) : S = order p :=
  le_antisymm (fun _ hx => integral_mem_order ((isIntegral_algHom_iff S.val Subtype.val_injective).mpr (IsIntegral.of_finite ℤ_[p] (⟨_, hx⟩ : S)))) h

omit [Fact (p % 4 = 3)] in
theorem exists_integralTrace (x : order p) : ∃ t : ℤ_[p], (t : ℚ_[p]) = tr x.val := by
  refine ⟨2 * (orderEquiv.symm x).re, ?_⟩
  rw [tr_apply, ← includeIntegral_symm x]
  rfl

/-- Integral reduced norm on the order. -/
noncomputable def integralNorm : order p →* ℤ_[p] where
  toFun x := ⟨nrd x.val, (mem_order_iff_nrd _).mp x.property⟩
  map_one' := Subtype.ext (map_one nrd)
  map_mul' x y := Subtype.ext (map_mul nrd x.val y.val)

noncomputable def normUnits : (order p)ˣ →* ℤ_[p]ˣ := Units.map integralNorm

theorem normUnits_eq (u : (order p)ˣ) :
    ((normUnits u).val : ℚ_[p]) = nrd u.val.val := rfl

theorem orderUnit_iff_norm (x : order p) : IsUnit x ↔ ‖nrd x.val‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact PadicInt.isUnit_iff.mp (normUnits u).isUnit
  · intro h
    have hx : x.val ≠ 0 := by
      intro hz
      simp [hz, nrd_formula] at h
    have hi : nrd x.val⁻¹ = (nrd x.val)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [← map_mul, mul_inv_cancel₀ hx, map_one]
    let y : order p := ⟨x.val⁻¹, (mem_order_iff_nrd _).mpr (by rw [hi, norm_inv, h, inv_one])⟩
    exact ⟨⟨x, y, Subtype.ext (mul_inv_cancel₀ hx), Subtype.ext (inv_mul_cancel₀ hx)⟩, rfl⟩

#print axioms includeIntegral
#print axioms includeIntegral_injective
#print axioms coe_orderEquiv
#print axioms includeIntegral_symm
#print axioms mem_order
#print axioms finite_order
#print axioms order_open
#print axioms order_compact
#print axioms orderCoord_continuous
#print axioms norm_le_one_of_weighted_sq
#print axioms mem_order_iff_nrd
#print axioms mem_order_iff_valuation
#print axioms nrd_valuation_mul
#print axioms norm_nrd_add_le_max
#print axioms integral_mem_order
#print axioms maximal_order
#print axioms exists_integralTrace
#print axioms normUnits_eq
#print axioms orderUnit_iff_norm

end ZInQ.Manuscript.RC.LocalDivision
