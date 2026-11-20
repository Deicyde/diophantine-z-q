import ZInQKernel.Contrib.OneProof.RC.CMField2.Cyclic
import ZInQKernel.Contrib.OneProof.RC.CMField2.Diagonal
import ZInQKernel.Contrib.OneProof.RC.CMField2.Lattices
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.LinearAlgebra.Unimodular

/-! Integrality of the singular modulus of a proper invertible ideal.
On-the-spot modular-polynomial proof (c). -/

noncomputable section

open NumberField Module TauCeti.GlobalNumberFields Matrix Polynomial
open scoped nonZeroDivisors

namespace ZInQ.Manuscript.RC.CMField2

/-- In the rank-two complex lattice, the index of a scaled sublattice is the squared
complex norm of the scalar. -/
theorem cast_sublatticeIndex_scale (L : PeriodPair) (u : ℂˣ)
    (h : (L.scale u).lattice ≤ L.lattice) :
    (L.sublatticeIndex (L.scale u) : ℝ) = Complex.normSq (u : ℂ) := by
  let M := L.scale u
  let b := L.latticeBasis
  let c := M.latticeBasis
  let v : Fin 2 → L.lattice := fun i => ⟨c i, h (c i).property⟩
  let e := basisOfLinearIndependentOfCardEqFinrank L.indep (by simp [Complex.finrank_real_complex])
  have he : ∀ i : Fin 2, e i = (b i : ℂ) := by
    have hfun : ⇑e = ![L.ω₁, L.ω₂] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
    intro i
    rw [show e i = (![L.ω₁, L.ω₂] : Fin 2 → ℂ) i from congrFun hfun i]
    fin_cases i <;> simp [b]
  have hv : ∀ i, (v i : ℂ) = (u : ℂ) * e i := by
    intro i
    rw [he]
    fin_cases i <;> simp [v, c, M, b]
  have hmat : (b.toMatrix v).map (Int.castRingHom ℝ) = Algebra.leftMulMatrix e (u : ℂ) := by
    ext i j
    change ((b.toMatrix v i j : ℤ) : ℝ) = _
    rw [Basis.toMatrix_apply, Algebra.leftMulMatrix_eq_repr_mul, ← hv]
    have hs := congrArg (fun x : L.lattice => (x : ℂ)) (b.sum_repr (v j)).symm
    rw [Fin.sum_univ_two] at hs
    simp only [Submodule.coe_add, Submodule.coe_smul, zsmul_eq_mul, ← he] at hs
    rw [hs]
    simp only [← Complex.ofReal_intCast, ← Complex.real_smul, map_add, map_smul,
      Finsupp.add_apply, Finsupp.smul_apply, Basis.repr_self]
    fin_cases i <;> simp
  have hdet : (↑(b.det v) : ℝ) = Complex.normSq (u : ℂ) := by
    rw [Basis.det_apply]
    change Int.castRingHom ℝ (b.toMatrix v).det = _
    rw [RingHom.map_det]
    change ((b.toMatrix v).map (Int.castRingHom ℝ)).det = _
    rw [hmat, ← Algebra.norm_eq_matrix_det, Algebra.norm_complex_apply]
  change (M.lattice.toAddSubgroup.relIndex L.lattice.toAddSubgroup : ℝ) = _
  have hi := AddSubgroup.relIndex_eq_natAbs_det M.lattice.toAddSubgroup L.lattice.toAddSubgroup
    (show M.lattice.toAddSubgroup ≤ L.lattice.toAddSubgroup from h) c b
  change M.lattice.toAddSubgroup.relIndex L.lattice.toAddSubgroup = (b.det v).natAbs at hi
  rw [hi, Nat.cast_natAbs, Int.cast_abs, hdet, abs_of_nonneg (Complex.normSq_nonneg _)]

variable {K : Type} [Field K] [NumberField K]

/-- In degree two, the order has a basis consisting of 1 and one further element. -/
theorem exists_order_basis_one (O : NumberFieldOrder K) (hk : finrank ℚ K = 2) :
    ∃ b : Basis (Fin 2) ℤ O.toSubalgebra, b 0 = 1 := by
  have hO : finrank ℤ O.toSubalgebra = 2 := by
    let b := Free.chooseBasis ℤ O.toSubalgebra
    rw [finrank_eq_card_basis b, ← finrank_eq_card_basis (b.localizationLocalization ℚ ℤ⁰ K), hk]
  exact IsUnimodular.exists_basis_zero_eq hO
    (Free.isUnimodular_one (R := ℤ) (A := O.toSubalgebra))

/-- The generator paired with 1 is nonreal in either embedding. -/
theorem orderBasis_im_ne_zero (O : NumberFieldOrder K)
    (hc : IsTotallyComplex K) (κ : K →+* ℂ)
    (b : Basis (Fin 2) ℤ O.toSubalgebra) (hb : b 0 = 1) :
    (κ (b 1 : K)).im ≠ 0 := by
  let := hc
  intro hz
  apply IsTotallyComplex.complexEmbedding_not_isReal κ
  rw [ComplexEmbedding.isReal_iff]
  let c := b.localizationLocalization ℚ ℤ⁰ K
  have hlin : (ComplexEmbedding.conjugate κ).toRatAlgHom.toLinearMap =
      κ.toRatAlgHom.toLinearMap := by
    apply c.ext
    intro i
    rw [show c i = (b i : K) from Basis.localizationLocalization_apply ℚ ℤ⁰ K b i]
    simp only [AlgHom.toLinearMap_apply, RingHom.toRatAlgHom_apply,
      ComplexEmbedding.conjugate_coe_eq]
    fin_cases i
    · change (starRingEnd ℂ) (κ (b 0 : K)) = κ (b 0 : K)
      rw [hb]
      simp
    · exact Complex.conj_eq_iff_im.mpr hz
  exact RingHom.ext fun x => LinearMap.congr_fun hlin x

/-- Basis coefficient one prevents a scalar stabilizing an invertible ideal from
being divisible by any rational integer greater than one in its multiplier ring. -/
private theorem primitive_scale_of_order_basis (O : NumberFieldOrder K)
    (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K) (κ : K →+* ℂ)
    (J : O.invertibleProperFractionalIdeals) (b : Basis (Fin 2) ℤ O.toSubalgebra)
    (hb : b 0 = 1) (n : ℤ) (u : ℂˣ)
    (hu : (u : ℂ) = κ ((n : K) + (b 1 : K))) :
    let L := idealPeriod O hk hc κ J
    ∀ k : ℕ, 1 < k → ¬ ∀ x ∈ (L.scale u).lattice, ∃ y ∈ L.lattice, x = (k : ℤ) • y := by
  dsimp only
  intro k hk₁ hd
  let α : K := (n : K) + (b 1 : K)
  have hk0 : (k : K) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hp := (O.isProperFractionalIdeal_iff J.val).mp (O.isProperFractionalIdeal_of_isUnit J.isUnit)
  have hmem : α / (k : K) ∈ O.toSubalgebra := by
    apply hp
    intro y hy
    let L := idealPeriod O hk hc κ J
    have hL : κ y ∈ L.lattice := by
      change κ y ∈ (L.lattice : Set ℂ)
      rw [idealPeriod_lattice]
      exact ⟨y, hy, rfl⟩
    have hsc : (u : ℂ) * κ y ∈ (L.scale u).lattice := by
      change _ ∈ ((L.scale u).lattice : Set ℂ)
      rw [lattice_scale]
      exact ⟨κ y, hL, rfl⟩
    obtain ⟨v, hv, he⟩ := hd _ hsc
    change v ∈ (L.lattice : Set ℂ) at hv
    rw [idealPeriod_lattice] at hv
    obtain ⟨z, hz, rfl⟩ := hv
    have he' : α * y = (k : K) * z := by
      apply κ.injective
      simpa only [map_mul, map_natCast, Int.cast_natCast, zsmul_eq_mul, hu] using he
    have hz' : α / (k : K) * y = z := by
      rw [div_mul_eq_mul_div, he', mul_div_cancel_left₀ _ hk0]
    rwa [hz']
  let a : O.toSubalgebra := ⟨α / (k : K), hmem⟩
  have he : (k : ℤ) • a = n • b 0 + b 1 := by
    apply (show Function.Injective O.toSubalgebra.val from Subtype.val_injective)
    rw [map_zsmul, map_add, map_zsmul]
    simp only [zsmul_eq_mul, Int.cast_natCast]
    change (k : K) * (α / (k : K)) = (n : K) * (b 0 : K) + (b 1 : K)
    rw [hb, mul_div_cancel₀ _ hk0]
    simp [α]
  have hh := congrArg (fun x => b.repr x 1) he
  change b.repr ((k : ℤ) • a) 1 = b.repr (n • b 0 + b 1) 1 at hh
  simp only [map_add, map_smul, Finsupp.smul_apply, Finsupp.add_apply, Basis.repr_self,
    smul_eq_mul] at hh
  simp at hh
  have hd' : (k : ℤ) ∣ (1 : ℤ) := ⟨_, hh.symm⟩
  have hd'' : k ∣ 1 := by simpa using Int.natCast_dvd.mp hd'
  exact (not_lt_of_ge (Nat.le_of_dvd (by decide : 0 < 1) hd'')) hk₁

/-- The j-value of any invertible fractional ideal of an imaginary quadratic order
is an algebraic integer. -/
theorem singularModulus_isIntegral (O : NumberFieldOrder K)
    (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K) (κ : K →+* ℂ)
    (J : O.invertibleProperFractionalIdeals) :
    IsIntegral ℤ (singularModulus O hk hc κ J) := by
  let := hc
  let L := idealPeriod O hk hc κ J
  obtain ⟨b, hb⟩ := exists_order_basis_one O hk
  let ω := (b 1 : K)
  let z := κ ω
  have hzi : z.im ≠ 0 := orderBasis_im_ne_zero O hc κ b hb
  have hn0 (n : ℤ) : (n : ℂ) + z ≠ 0 := by
    intro he
    apply hzi
    simpa using congrArg Complex.im he
  let σ (n : ℤ) : ℂˣ := Units.mk0 ((n : ℂ) + z) (hn0 n)
  have hσ (n : ℤ) : (σ n : ℂ) = κ ((n : K) + ω) := by simp [σ, z]
  have hsub (n : ℤ) : (L.scale (σ n)).lattice ≤ L.lattice := by
    intro x hx
    change x ∈ ((L.scale (σ n)).lattice : Set ℂ) at hx
    rw [lattice_scale, idealPeriod_lattice] at hx
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hx
    change (σ n : ℂ) * κ y ∈ (L.lattice : Set ℂ)
    rw [idealPeriod_lattice, hσ, ← map_mul]
    have hmem : (n : K) + ω ∈ O.toSubalgebra := O.toSubalgebra.add_mem
      (O.toSubalgebra.intCast_mem n) (b 1).property
    exact ⟨_, (O.mem_multiplierRing_iff J.val _).mp (O.order_le_multiplierRing J.val hmem) y hy, rfl⟩
  let idx (n : ℤ) := L.sublatticeIndex (L.scale (σ n))
  have hidx (n : ℤ) : (idx n : ℝ) = Complex.normSq ((n : ℂ) + z) :=
    cast_sublatticeIndex_scale L (σ n) (hsub n)
  let U : ℤ := idx 0
  let T : ℤ := (idx 1 : ℤ) - U - 1
  have hU : (U : ℝ) = z.re ^ 2 + z.im ^ 2 := by
    simpa [U, Complex.normSq_apply, pow_two] using hidx 0
  have hT : (T : ℝ) = 2 * z.re := by
    have h := hidx 1
    norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im] at h
    push_cast [T]
    nlinarith
  have hd : T ^ 2 < 4 * U := by
    have hzsq := sq_pos_of_ne_zero hzi
    exact_mod_cast (show (T : ℝ) ^ 2 < 4 * (U : ℝ) by rw [hT, hU]; nlinarith)
  obtain ⟨n, m, hm, hlo, hhi⟩ := exists_nonsquare_quadratic_value T U hd
  have he : (idx n : ℤ) = n ^ 2 + T * n + U := by
    have h := hidx n
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.intCast_re,
      Complex.intCast_im, zero_add] at h
    exact_mod_cast (show (idx n : ℝ) = (n : ℝ) ^ 2 + (T : ℝ) * (n : ℝ) + (U : ℝ) by
      rw [h, hT, hU]; ring)
  rw [← he] at hlo hhi
  have hzero : idx n ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hlo
    exact (not_lt_of_ge (sq_nonneg m)) hlo
  have hsq : ¬ IsSquare (idx n) := by
    rintro ⟨k, hk⟩
    have he' : (idx n : ℤ) = (k : ℤ)^2 := by exact_mod_cast (hk.trans (pow_two k).symm)
    rw [he'] at hlo hhi
    rcases le_or_gt (k : ℤ) m with hc | hc
    · nlinarith [mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ m + (k : ℤ) by omega)]
    · have hle : m + 1 ≤ (k : ℤ) := by omega
      nlinarith [mul_nonneg (sub_nonneg.mpr hle) (show 0 ≤ (k : ℤ) + (m + 1) by omega)]
  let : NeZero (idx n) := ⟨hzero⟩
  have hcyc := isAddCyclic_sublatticeQuotient_of_primitive L _ (hsub n)
    (primitive_scale_of_order_basis O hk hc κ J b hb n (σ n) (hσ n))
  exact isIntegral_jLattice_of_cyclicSelf (idx n) hsq L (L.scale (σ n))
    (hsub n) rfl hcyc (jLattice_scale L (σ n))

/-- For an imaginary quadratic field the ideal norm of a principal integral ideal
is the squared complex norm of the image of its generator. -/
theorem cast_absNorm_span_singleton_complex (hk : finrank ℚ K = 2)
    (hc : IsTotallyComplex K) (κ : K →+* ℂ) (β : 𝓞 K) :
    (Ideal.absNorm (Ideal.span {β}) : ℝ) = Complex.normSq (κ β) := by
  classical
  let := hc
  have hd := IsTotallyComplex.finrank K
  have hcard : Fintype.card (InfinitePlace K) ≤ 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add]
    omega
  let : Subsingleton (InfinitePlace K) := Fintype.card_le_one_iff_subsingleton.mp hcard
  let w := InfinitePlace.mk κ
  have hp : |(Algebra.norm ℚ (β : K) : ℝ)| = w (β : K) ^ 2 := by
    rw [← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm,
      Finset.prod_eq_single w (fun i _ hi => (hi (Subsingleton.elim i w)).elim)
        (fun hu => (hu (Finset.mem_univ w)).elim), IsTotallyComplex.mult_eq]
  rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, ← Rat.cast_intCast,
    Int.cast_abs, Algebra.coe_norm_int, Rat.cast_abs, hp, Complex.normSq_eq_norm_sq]
  rfl

/-- A nonzero order multiplier of prime complex norm gives the prime-level
diagonal equation at every proper ideal modulus. -/
theorem prime_diagonal_eq_of_order_multiplier (O : NumberFieldOrder K)
    (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K) (κ : K →+* ℂ)
    (J : O.invertibleProperFractionalIdeals) (p : ℕ) [Fact p.Prime]
    (P : ModularCurve.ModularPolynomialData p) (α : K) (hα : α ∈ O.toSubalgebra)
    (hp : Complex.normSq (κ α) = (p : ℝ)) :
    (P.Φ.eval₂ (RingHom.id ℤ[X]) Polynomial.X).eval₂
      (Int.castRingHom ℂ) (singularModulus O hk hc κ J) = 0 := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hα0 : κ α ≠ 0 := by
    intro he
    simp only [he, Complex.normSq_zero] at hp
    exact hp0 (by exact_mod_cast hp.symm)
  let L := idealPeriod O hk hc κ J
  let u := Units.mk0 (κ α) hα0
  have hsub : (L.scale u).lattice ≤ L.lattice := by
    intro x hx
    change x ∈ ((L.scale u).lattice : Set ℂ) at hx
    rw [lattice_scale, idealPeriod_lattice] at hx
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hx
    change κ α * κ y ∈ (L.lattice : Set ℂ)
    rw [idealPeriod_lattice, ← map_mul]
    exact ⟨_, (O.mem_multiplierRing_iff J.val _).mp (O.order_le_multiplierRing J.val hα) y hy, rfl⟩
  have hi : L.sublatticeIndex (L.scale u) = p := by
    exact_mod_cast ((cast_sublatticeIndex_scale L u hsub).trans hp)
  have hcyc : IsAddCyclic (L.sublatticeQuotient (L.scale u)) :=
    isAddCyclic_of_prime_card (by simpa only [PeriodPair.sublatticeIndex,
      AddSubgroup.index_eq_card] using hi)
  rw [singularModulus, eval_diagonal]
  have h := ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic
    p P L (L.scale u) hsub hi hcyc
  exact (jLattice_scale L u) ▸ h


end ZInQ.Manuscript.RC.CMField2
