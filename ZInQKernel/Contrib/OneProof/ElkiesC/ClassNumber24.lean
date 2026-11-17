import ZInQKernel.Contrib.OneProof.RayClassShimura
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# elkies-c, part 1: the closed facts for `ℚ(√−6)`

Task elkies-c (docs/research/elkies-c.md). For `K24 = ℚ(√−6)` (`ShimuraGlue.Ray.K24`, with `y24 = √−6`
and `𝓞 = ℤ[√−6]` from rayclass-cft's `RayClassCFT.ringOfIntegersGen_K24`):

* `discr_K24 : NumberField.discr K24 = −24` (the basis `{1, √−6}` of `𝓞`);
* `card_classGroup_le_two : Fintype.card (ClassGroup 𝓞) ≤ 2` (Minkowski: every class contains an ideal of norm
  `≤ 2√24/π < 4`; the ideals of norm 2 and 3 are `𝔭₂ = (2, √−6)`, `𝔭₃ = (3, √−6)`, with `𝔭₂² = (2)` and
  `𝔭₂𝔭₃ = (√−6)`);
* `pic_R24_le_two`, `pic_R24_ne_zero`: the same for `CommRing.Pic` of `R24 = (integralClosure ℤ K24).toSubring`;
* `inertCount6_K24 : inertCount6 K24 = 0` (2 and 3 ramify), `conductor_R24 : conductor R24 = 1`.

No `sorry`; standard axioms only.
-/

set_option linter.all false

noncomputable section

namespace ElkiesC

open NumberField Module ShimuraGlue.Ray RayClassCFT
open scoped nonZeroDivisors Real

local notation "O24" => 𝓞 K24

theorem y24_mul : y24 * y24 = -6 := by
  have h := y24_rel; push_cast at h; linear_combination h

theorem y24_ne : ∀ r : ℚ, y24 ≠ r := not_rat_of_disc y24_rel (by norm_num)

theorem y24_integral : IsIntegral ℤ y24 :=
  ⟨Polynomial.X ^ 2 + Polynomial.C 6, Polynomial.monic_X_pow_add_C _ two_ne_zero, by
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    rw [sq, y24_mul]; simp⟩

/-- `√−6 ∈ 𝓞 K24`. -/
def w : O24 := ⟨y24, y24_integral⟩

theorem w_coe : ((w : O24) : K24) = y24 := rfl

theorem w_mul : w * w = -6 := by
  ext
  simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_neg, map_ofNat]
  exact y24_mul

theorem repr_w (x : O24) : ∃ a b : ℤ, x = a + b * w := by
  obtain ⟨a, b, h⟩ := ringOfIntegersGen_K24 x
  refine ⟨a, b, RingOfIntegers.ext ?_⟩
  rw [h]
  simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast]
  rfl

theorem eq_zero_of_repr {a b : ℤ} (h : (a : O24) + b * w = 0) : a = 0 ∧ b = 0 := by
  have h' : ((a : ℚ) : K24) + (b : ℚ) * y24 = ((0 : ℚ) : K24) + (0 : ℚ) * y24 := by
    have := congrArg (fun x : O24 => (x : K24)) h
    simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast, map_zero] at this
    push_cast
    simpa using this
  obtain ⟨h1, h2⟩ := repr_unique y24_ne h'
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-! ## The discriminant -/

/-- The `ℤ`-basis `{1, √−6}` of `𝓞 K24`. -/
def basis24 : Basis (Fin 2) ℤ O24 :=
  Basis.mk (v := ![1, w])
    (by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have : (s : O24) + t * w = 0 := by simpa [zsmul_eq_mul] using hst
      exact eq_zero_of_repr this)
    (by
      rintro x -
      obtain ⟨a, b, rfl⟩ := repr_w x
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨![a, b], ?_⟩
      simp [Fin.sum_univ_two, zsmul_eq_mul])

theorem basis24_zero : basis24 0 = 1 := by simp [basis24]
theorem basis24_one : basis24 1 = w := by simp [basis24]

theorem finrank_O24 : finrank ℤ O24 = 2 := by rw [RingOfIntegers.rank, finrank_K24]

theorem discr_K24 : discr K24 = -24 := by
  classical
  rw [← discr_eq_discr K24 basis24]
  have htr1 : Algebra.trace ℤ O24 1 = 2 := by
    rw [← map_one (algebraMap ℤ O24), Algebra.trace_algebraMap, finrank_O24]; norm_num
  have hrepr1 : basis24.repr w = Finsupp.single 1 1 := by rw [← basis24_one, basis24.repr_self]
  have hrepr0 : basis24.repr 1 = Finsupp.single 0 1 := by rw [← basis24_zero, basis24.repr_self]
  have hww : w * w = (-6 : ℤ) • (1 : O24) := by rw [w_mul]; simp
  have htrw : Algebra.trace ℤ O24 w = 0 := by
    rw [Algebra.trace_eq_matrix_trace basis24, Matrix.trace, Fin.sum_univ_two]
    simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, basis24_zero, basis24_one, mul_one, hww,
      map_smul, hrepr0, hrepr1]
    simp
  have htrww : Algebra.trace ℤ O24 (w * w) = -12 := by
    rw [hww, map_smul, htr1]; norm_num
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, basis24_zero, basis24_one, mul_one,
    one_mul, htr1, htrw, htrww]
  norm_num

/-! ## The ideals `𝔭₂`, `𝔭₃` -/

/-- `𝔭₂ = (2, √−6)`. -/
def p2 : Ideal O24 := Ideal.span {2, w}
/-- `𝔭₃ = (3, √−6)`. -/
def p3 : Ideal O24 := Ideal.span {3, w}

theorem two_mem_p2 : (2 : O24) ∈ p2 := Ideal.subset_span (by simp)
theorem w_mem_p2 : w ∈ p2 := Ideal.subset_span (by simp)
theorem three_mem_p3 : (3 : O24) ∈ p3 := Ideal.subset_span (by simp)
theorem w_mem_p3 : w ∈ p3 := Ideal.subset_span (by simp)

theorem p2_sq : p2 * p2 = Ideal.span {(2 : O24)} := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro r hr s hs
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hr
    obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.1 hs
    rw [Ideal.mem_span_singleton']
    exact ⟨2 * a * c + (a * d + b * c) * w - 3 * b * d, by linear_combination (-(b * d)) * w_mul⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have h1 : w * w ∈ p2 * p2 := Ideal.mul_mem_mul w_mem_p2 w_mem_p2
    have h2 : (2 : O24) * 2 ∈ p2 * p2 := Ideal.mul_mem_mul two_mem_p2 two_mem_p2
    have : (2 : O24) = -(w * w) - 2 * 2 := by rw [w_mul]; ring
    rw [this]; exact sub_mem (neg_mem h1) h2

theorem p3_sq : p3 * p3 = Ideal.span {(3 : O24)} := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro r hr s hs
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hr
    obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.1 hs
    rw [Ideal.mem_span_singleton']
    exact ⟨3 * a * c + (a * d + b * c) * w - 2 * b * d, by linear_combination (-(b * d)) * w_mul⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have h1 : w * w ∈ p3 * p3 := Ideal.mul_mem_mul w_mem_p3 w_mem_p3
    have h2 : (3 : O24) * 3 ∈ p3 * p3 := Ideal.mul_mem_mul three_mem_p3 three_mem_p3
    have : (3 : O24) = 3 * 3 + w * w := by rw [w_mul]; ring
    rw [this]; exact add_mem h2 h1

theorem p2_mul_p3 : p2 * p3 = Ideal.span {w} := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro r hr s hs
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hr
    obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.1 hs
    rw [Ideal.mem_span_singleton']
    exact ⟨-(a * c * w) + 2 * a * d + 3 * b * c + b * d * w, by
      linear_combination (a * c - b * d) * w_mul⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have h1 : w * 3 ∈ p2 * p3 := Ideal.mul_mem_mul w_mem_p2 three_mem_p3
    have h2 : (2 : O24) * w ∈ p2 * p3 := Ideal.mul_mem_mul two_mem_p2 w_mem_p3
    have : w = w * 3 - 2 * w := by ring
    rw [this]; exact sub_mem h1 h2

theorem absNorm_span_nat (m : ℕ) : Ideal.absNorm (Ideal.span {(m : O24)}) = m ^ 2 := by
  rw [Ideal.absNorm_span_natCast, finrank_O24]

theorem absNorm_p2 : Ideal.absNorm p2 = 2 := by
  have : Ideal.absNorm p2 ^ 2 = 2 ^ 2 := by
    rw [← map_pow, sq p2, p2_sq]
    exact_mod_cast absNorm_span_nat 2
  exact Nat.pow_left_injective two_ne_zero this

theorem absNorm_p3 : Ideal.absNorm p3 = 3 := by
  have : Ideal.absNorm p3 ^ 2 = 3 ^ 2 := by
    rw [← map_pow, sq p3, p3_sq]
    exact_mod_cast absNorm_span_nat 3
  exact Nat.pow_left_injective two_ne_zero this

/-- An ideal dividing another one of the same nonzero norm is equal to it (copy of Rédei's
`eq_of_dvd_of_absNorm_eq`, for `𝓞 K24`). -/
theorem eq_of_dvd_of_absNorm_eq {I J : Ideal O24} (hIJ : I ∣ J) (hN : Ideal.absNorm I = Ideal.absNorm J)
    (h0 : Ideal.absNorm J ≠ 0) : I = J := by
  obtain ⟨M, rfl⟩ := hIJ
  rw [map_mul] at hN h0
  have hM : Ideal.absNorm M = 1 := by
    have h1 : Ideal.absNorm I ≠ 0 := left_ne_zero_of_mul h0
    have : Ideal.absNorm I * Ideal.absNorm M = Ideal.absNorm I * 1 := by rw [mul_one]; exact hN.symm
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h1) this
  rw [Ideal.absNorm_eq_one_iff] at hM
  rw [hM, Ideal.mul_top]

/-- The only ideal of norm 2 is `𝔭₂`. -/
theorem eq_p2 {I : Ideal O24} (hI : Ideal.absNorm I = 2) : I = p2 := by
  have hP : I.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hI]; exact Nat.prime_two.irreducible)
  have h2 : (2 : O24) ∈ I := by have := Ideal.absNorm_mem I; rw [hI] at this; exact_mod_cast this
  have hw : w ∈ I := by
    have hww : w * w ∈ I := by
      rw [w_mul, show (-6 : O24) = -3 * 2 by ring]
      exact I.mul_mem_left _ h2
    rcases hP.mem_or_mem hww with h | h <;> exact h
  have hle : p2 ≤ I := by
    rw [p2, Ideal.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact h2
    · exact hw
  exact eq_of_dvd_of_absNorm_eq (Ideal.dvd_iff_le.2 hle) (by rw [hI, absNorm_p2])
    (by rw [absNorm_p2]; norm_num)

/-- The only ideal of norm 3 is `𝔭₃`. -/
theorem eq_p3 {I : Ideal O24} (hI : Ideal.absNorm I = 3) : I = p3 := by
  have hP : I.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hI]; exact Nat.prime_three.irreducible)
  have h3 : (3 : O24) ∈ I := by have := Ideal.absNorm_mem I; rw [hI] at this; exact_mod_cast this
  have hw : w ∈ I := by
    have hww : w * w ∈ I := by
      rw [w_mul, show (-6 : O24) = -2 * 3 by ring]
      exact I.mul_mem_left _ h3
    rcases hP.mem_or_mem hww with h | h <;> exact h
  have hle : p3 ≤ I := by
    rw [p3, Ideal.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact h3
    · exact hw
  exact eq_of_dvd_of_absNorm_eq (Ideal.dvd_iff_le.2 hle) (by rw [hI, absNorm_p3])
    (by rw [absNorm_p3]; norm_num)

/-! ## The class group has at most two elements -/

theorem p2_mem : p2 ∈ (Ideal O24)⁰ :=
  mem_nonZeroDivisors_of_ne_zero (fun h => by
    have := absNorm_p2; rw [h, Ideal.absNorm_bot] at this; norm_num at this)

theorem p3_mem : p3 ∈ (Ideal O24)⁰ :=
  mem_nonZeroDivisors_of_ne_zero (fun h => by
    have := absNorm_p3; rw [h, Ideal.absNorm_bot] at this; norm_num at this)

theorem mk0_p2_sq : ClassGroup.mk0 ⟨p2, p2_mem⟩ * ClassGroup.mk0 ⟨p2, p2_mem⟩ = 1 := by
  rw [← map_mul]
  have hm : (⟨p2, p2_mem⟩ * ⟨p2, p2_mem⟩ : (Ideal O24)⁰) = ⟨Ideal.span {(2 : O24)}, by
      rw [← p2_sq]; exact mul_mem p2_mem p2_mem⟩ := Subtype.ext p2_sq
  rw [hm, ClassGroup.mk0_eq_one_iff]
  exact ⟨⟨2, rfl⟩⟩

theorem mk0_p2_p3 : ClassGroup.mk0 ⟨p2, p2_mem⟩ * ClassGroup.mk0 ⟨p3, p3_mem⟩ = 1 := by
  rw [← map_mul]
  have hm : (⟨p2, p2_mem⟩ * ⟨p3, p3_mem⟩ : (Ideal O24)⁰) = ⟨Ideal.span {w}, by
      rw [← p2_mul_p3]; exact mul_mem p2_mem p3_mem⟩ := Subtype.ext p2_mul_p3
  rw [hm, ClassGroup.mk0_eq_one_iff]
  exact ⟨⟨w, rfl⟩⟩

theorem mk0_p3 : ClassGroup.mk0 ⟨p3, p3_mem⟩ = ClassGroup.mk0 ⟨p2, p2_mem⟩ := by
  have h1 := mk0_p2_sq
  have h2 := mk0_p2_p3
  rw [← h1] at h2
  exact mul_left_cancel h2

theorem nrComplexPlaces_K24 : InfinitePlace.nrComplexPlaces K24 = 1 := by
  have h := InfinitePlace.card_add_two_mul_card_eq_rank K24
  rw [IsTotallyComplex.nrRealPlaces_eq_zero, finrank_K24] at h
  omega

/-- Minkowski's bound for `K24` is `< 4`. -/
theorem minkowski_lt_four :
    (4 / π) ^ InfinitePlace.nrComplexPlaces K24 *
      ((finrank ℚ K24).factorial / (finrank ℚ K24 : ℝ) ^ (finrank ℚ K24) * √|(discr K24 : ℝ)|) < 4 := by
  rw [nrComplexPlaces_K24, finrank_K24, discr_K24]
  have hs : √(24 : ℝ) < 5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpi : 3 < π := Real.pi_gt_three
  have hpos : 0 < π := Real.pi_pos
  norm_num
  rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
  nlinarith [Real.sqrt_nonneg 24]

theorem classGroup_mem (C : ClassGroup O24) :
    C = 1 ∨ C = ClassGroup.mk0 ⟨p2, p2_mem⟩ := by
  obtain ⟨I, rfl, hI⟩ := exists_ideal_in_class_of_norm_le C
  have h4 : (Ideal.absNorm (I : Ideal O24) : ℝ) < 4 := lt_of_le_of_lt hI minkowski_lt_four
  have h4' : Ideal.absNorm (I : Ideal O24) < 4 := by exact_mod_cast h4
  have h0 : Ideal.absNorm (I : Ideal O24) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact nonZeroDivisors.coe_ne_zero I
  interval_cases hN : Ideal.absNorm (I : Ideal O24)
  · left
    rw [Ideal.absNorm_eq_one_iff] at hN
    rw [ClassGroup.mk0_eq_one_iff, hN]
    exact ⟨⟨1, by simp⟩⟩
  · right
    have := eq_p2 hN
    congr 1
    exact Subtype.ext this
  · right
    have := eq_p3 hN
    rw [← mk0_p3]
    congr 1
    exact Subtype.ext this

theorem card_classGroup_le_two : Fintype.card (ClassGroup O24) ≤ 2 := by
  classical
  have : (Finset.univ : Finset (ClassGroup O24)) ⊆ {1, ClassGroup.mk0 ⟨p2, p2_mem⟩} := by
    intro C _
    rcases classGroup_mem C with h | h <;> simp [h]
  calc Fintype.card (ClassGroup O24) = (Finset.univ : Finset (ClassGroup O24)).card := rfl
    _ ≤ ({1, ClassGroup.mk0 ⟨p2, p2_mem⟩} : Finset (ClassGroup O24)).card := Finset.card_le_card this
    _ ≤ 2 := Finset.card_le_two

/-! ## `Pic`, `inertCount6`, conductor of `R24 = 𝓞 K24` as a subring -/

/-- `R24 = 𝓞 ℚ(√−6)` as a subring. -/
abbrev R24 : Subring K24 := (integralClosure ℤ K24).toSubring

theorem card_pic_O24 : Nat.card (CommRing.Pic O24) = Fintype.card (ClassGroup O24) := by
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (ClassGroup.equivPic O24).toEquiv).symm

theorem pic_R24_le_two : Nat.card (CommRing.Pic R24) ≤ 2 := by
  have e : Nat.card (CommRing.Pic R24) = Nat.card (CommRing.Pic O24) := rfl
  rw [e, card_pic_O24]
  exact card_classGroup_le_two

theorem pic_R24_ne_zero : Nat.card (CommRing.Pic R24) ≠ 0 := by
  have e : Nat.card (CommRing.Pic R24) = Nat.card (CommRing.Pic O24) := rfl
  rw [e, card_pic_O24]
  exact Fintype.card_ne_zero

theorem conductor_R24 : LeafQM.AV.conductor R24 = 1 := AddSubgroup.relIndex_self _

theorem not_prime_span (p : ℕ) (hp : (p : O24) ∣ w * w) (hw : ¬ (p : O24) ∣ w) :
    ¬ (Ideal.span {(p : O24)}).IsPrime := by
  intro h
  have hww : w * w ∈ Ideal.span {(p : O24)} := Ideal.mem_span_singleton.2 hp
  rcases h.mem_or_mem hww with h' | h' <;> exact hw (Ideal.mem_span_singleton.1 h')

theorem not_dvd_w (p : ℕ) (hp : 2 ≤ p) : ¬ (p : O24) ∣ w := by
  rintro ⟨z, hz⟩
  obtain ⟨a, b, rfl⟩ := repr_w z
  have h : ((-(p * a) : ℤ) : O24) + ((1 - p * b : ℤ) : O24) * w = 0 := by
    push_cast
    linear_combination hz
  obtain ⟨-, h2⟩ := eq_zero_of_repr h
  have : (p : ℤ) * b = 1 := by linarith
  have h1 : (p : ℤ) ∣ 1 := ⟨b, this.symm⟩
  have : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
  omega

theorem inertCount6_K24 : LeafQM.AV.inertCount6 K24 = 0 := by
  unfold LeafQM.AV.inertCount6
  have h2 : ¬ (Ideal.span {(2 : O24)}).IsPrime := by
    have := not_prime_span 2 ⟨-3, by rw [w_mul]; push_cast; ring⟩ (not_dvd_w 2 le_rfl)
    exact_mod_cast this
  have h3 : ¬ (Ideal.span {(3 : O24)}).IsPrime := by
    have := not_prime_span 3 ⟨-2, by rw [w_mul]; push_cast; ring⟩ (not_dvd_w 3 (by norm_num))
    exact_mod_cast this
  simp [h2, h3]

end ElkiesC
