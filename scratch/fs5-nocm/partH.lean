
/-! ## §H N1a-CM proved from T6 (`End_𝒪(A)` is an order of `ℚ(√d)` when `End⁰(A) ≅ M₂(ℚ(√d))`) -/

namespace FS5NoCM

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin PkgI3
open scoped Quaternion TensorProduct

section LinAlg

variable {K : Type} [Field K]

local notation "M2" => Matrix (Fin 2) (Fin 2) K

theorem quat_comm_I (I J : M2) (hI : I * I = (2 : K) • 1) (hJI : J * I = -(I * J))
    (a b c d : K) :
    I * (a • 1 + b • I + c • J + d • (I * J)) - (a • 1 + b • I + c • J + d • (I * J)) * I =
      (2 * c) • (I * J) + (4 * d) • J := by
  have r1 : I * (I * J) = (2 : K) • J := by rw [← mul_assoc, hI, smul_mul_assoc, one_mul]
  have r2 : (I * J) * I = -((2 : K) • J) := by
    rw [mul_assoc, hJI, mul_neg, ← mul_assoc, hI, smul_mul_assoc, one_mul]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hI, r1, r2, hJI]
  module

theorem quat_comm_J (I J : M2) (hI : I * I = (2 : K) • 1) (hJ : J * J = (-3 : K) • 1)
    (hJI : J * I = -(I * J)) (a b c d : K) :
    J * (a • 1 + b • I + c • J + d • (I * J)) - (a • 1 + b • I + c • J + d • (I * J)) * J =
      (-2 * b) • (I * J) + (6 * d) • I := by
  have r3 : (I * J) * J = (-3 : K) • I := by rw [mul_assoc, hJ, mul_smul_comm, mul_one]
  have r4 : J * (I * J) = (3 : K) • I := by
    rw [← mul_assoc, hJI, neg_mul, mul_assoc, hJ, mul_smul_comm, mul_one, neg_smul]; module
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hJ, r3, r4, hJI]
  module

/-- **A matrix commuting with `I` and `J` is scalar**, if `I² = 2`, `J² = −3`, `JI = −IJ` in
`M₂(K)`, `2, 3 ≠ 0` in `K` (then `1, I, J, IJ` is a `K`-basis of `M₂(K)`). -/
theorem commute_quat_scalar (I J : M2) (hI : I * I = (2 : K) • 1) (hJ : J * J = (-3 : K) • 1)
    (hJI : J * I = -(I * J)) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (Y : M2) (hYI : I * Y = Y * I) (hYJ : J * Y = Y * J) : ∃ a : K, Y = a • (1 : M2) := by
  have r3 : (I * J) * J = (-3 : K) • I := by rw [mul_assoc, hJ, mul_smul_comm, mul_one]
  have hinj : Function.Injective (fun x : K => x • (1 : M2)) := smul_left_injective K one_ne_zero
  have hIns : ∀ s : K, I ≠ s • (1 : M2) := by
    intro s hs
    have hc : I * J = J * I := by rw [hs, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [hJI] at hc
    have h0 : I * J = 0 := by
      have : (2 : K) • (I * J) = 0 := by
        rw [two_smul]; nth_rewrite 2 [hc]; exact add_neg_cancel _
      exact (smul_eq_zero.mp this).resolve_left h2
    have hI0 : I = 0 := by
      have := r3; rw [h0, zero_mul] at this
      exact (smul_eq_zero.mp this.symm).resolve_left (neg_ne_zero.mpr h3)
    apply h2; apply hinj; simp only; rw [← hI, hI0, mul_zero, zero_smul]
  -- `(2c)•IJ + (4d)•J = 0 → c = 0 ∧ d = 0`
  have kill : ∀ c d : K, (2 * c) • (I * J) + (4 * d) • J = 0 → c = 0 ∧ d = 0 := by
    intro c d h
    have h' := congrArg (· * J) h
    simp only [add_mul, smul_mul_assoc, r3, hJ, zero_mul] at h'
    have hc : c = 0 := by
      by_contra hc
      have h6 : (-6 * c : K) ≠ 0 := mul_ne_zero (by
        rw [show (-6 : K) = -(2 * 3) by norm_num]; exact neg_ne_zero.mpr (mul_ne_zero h2 h3)) hc
      apply hIns ((-6 * c)⁻¹ * (12 * d))
      have : (-6 * c) • I = (12 * d) • (1 : M2) := by
        have e : (-6 * c) • I - (12 * d) • (1 : M2) =
            (2 * c) • (-3 : K) • I + (4 * d) • (-3 : K) • (1 : M2) := by module
        rw [h'] at e; exact sub_eq_zero.mp e
      rw [mul_smul, ← this, smul_smul, inv_mul_cancel₀ h6, one_smul]
    subst hc
    refine ⟨rfl, ?_⟩
    have : (-12 * d) • (1 : M2) = 0 := by
      have e : (-12 * d) • (1 : M2) = ((2 : K) * 0) • (-3 : K) • I + (4 * d) • (-3 : K) • (1 : M2) := by
        module
      rw [e]; exact h'
    have h12 : (-12 * d : K) = 0 := hinj (by simpa using this)
    have : (12 : K) ≠ 0 := by
      have : (12 : K) = 2 * 2 * 3 := by norm_num
      rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) h3
    have := mul_eq_zero.mp (show (-12 : K) * d = 0 from h12)
    rcases this with h | h
    · exact absurd (neg_eq_zero.mp h) ‹(12 : K) ≠ 0›
    · exact h
  let v : Fin 4 → M2 := ![1, I, J, I * J]
  have hsum : ∀ g : Fin 4 → K, ∑ i, g i • v i = g 0 • 1 + g 1 • I + g 2 • J + g 3 • (I * J) := by
    intro g; simp [Fin.sum_univ_four, v]
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [hsum] at hg
    have hI0 := quat_comm_I I J hI hJI (g 0) (g 1) (g 2) (g 3)
    rw [hg, mul_zero, zero_mul, sub_zero] at hI0
    obtain ⟨hg2, hg3⟩ := kill _ _ hI0.symm
    rw [hg2, hg3, zero_smul, zero_smul, add_zero, add_zero] at hg
    have hg1 : g 1 = 0 := by
      by_contra hg1
      apply hIns (-(g 1)⁻¹ * g 0)
      have hb : g 1 • I = -(g 0 • (1 : M2)) := eq_neg_of_add_eq_zero_right hg
      calc I = (g 1)⁻¹ • (g 1 • I) := by rw [smul_smul, inv_mul_cancel₀ hg1, one_smul]
        _ = (-(g 1)⁻¹ * g 0) • 1 := by rw [hb]; module
    rw [hg1, zero_smul, add_zero] at hg
    have hg0 : g 0 = 0 := hinj (by simpa using hg)
    intro i; fin_cases i <;> assumption
  have hspan : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [Module.finrank_matrix])
  have hY : Y ∈ Submodule.span K (Set.range v) := hspan ▸ Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hY
  rw [hsum] at hg
  subst hg
  have hI0 := quat_comm_I I J hI hJI (g 0) (g 1) (g 2) (g 3)
  rw [hYI, sub_self] at hI0
  obtain ⟨hg2, hg3⟩ := kill _ _ hI0.symm
  have hJ0 := quat_comm_J I J hI hJ hJI (g 0) (g 1) (g 2) (g 3)
  rw [hYJ, sub_self, hg3, mul_zero, zero_smul, add_zero] at hJ0
  have hg1 : g 1 = 0 := by
    have h' := congrArg (· * J) hJ0
    simp only [smul_mul_assoc, r3, zero_mul, smul_smul] at h'
    by_contra hg1
    apply hIns 0
    have hne : (-2 * g 1 * -3 : K) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) hg1) (neg_ne_zero.mpr h3)
    rw [zero_smul]
    exact (smul_eq_zero.mp h'.symm).resolve_left hne
  refine ⟨g 0, ?_⟩
  rw [hg1, hg2, hg3]; simp

section AdjRoot

open Polynomial

variable (d : ℚ)

/-- `X² − d` is irreducible over `ℚ` for `d < 0`. -/
theorem irred_sq_sub (hd : d < 0) : Irreducible (X ^ 2 - C d : ℚ[X]) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => by nlinarith [sq_nonneg b])

theorem monic_sq_sub : (X ^ 2 - C d : ℚ[X]).Monic := monic_X_pow_sub_C _ two_ne_zero

theorem finrank_adjRoot : Module.finrank ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X])) = 2 := by
  rw [(AdjoinRoot.powerBasis' (monic_sq_sub d)).finrank]
  exact natDegree_X_pow_sub_C

theorem finite_adjRoot : Module.Finite ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X])) :=
  (AdjoinRoot.powerBasis' (monic_sq_sub d)).finite

theorem root_sq : (AdjoinRoot.root (X ^ 2 - C d : ℚ[X])) ^ 2 =
    algebraMap ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X])) d := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C d : ℚ[X])
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [AdjoinRoot.algebraMap_eq]
  exact sub_eq_zero.mp h

/-- For `d < 0`, `ℚ(√d)` (as `AdjoinRoot`, with its field structure) is a totally complex
quadratic number field. -/
theorem adjRoot_numberField (hd : d < 0) :
    letI : Fact (Irreducible (X ^ 2 - C d : ℚ[X])) := ⟨irred_sq_sub d hd⟩
    NumberField (AdjoinRoot (X ^ 2 - C d : ℚ[X])) ∧
      NumberField.IsTotallyComplex (AdjoinRoot (X ^ 2 - C d : ℚ[X])) := by
  let : Fact (Irreducible (X ^ 2 - C d : ℚ[X])) := ⟨irred_sq_sub d hd⟩
  have : CharZero (AdjoinRoot (X ^ 2 - C d : ℚ[X])) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X]))).injective
  have := finite_adjRoot d
  refine ⟨{}, ⟨fun v => ?_⟩⟩
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  rintro ⟨φ, hφ, -⟩
  have h2 : (hφ.embedding (AdjoinRoot.root (X ^ 2 - C d : ℚ[X]))) ^ 2 = (d : ℝ) := by
    have := congrArg hφ.embedding (root_sq d)
    rwa [map_pow, eq_ratCast (algebraMap ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X]))) d,
      map_ratCast] at this
  have hd' : (d : ℝ) < 0 := by exact_mod_cast hd
  nlinarith [sq_nonneg (hφ.embedding (AdjoinRoot.root (X ^ 2 - C d : ℚ[X])))]

end AdjRoot


end LinAlg

local notation "Kd[" d "]" => AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ)

/-- `root` is not rational: `x + y·√d = 0` with `x, y ∈ ℚ` forces `x = y = 0` (`d < 0`). -/
theorem root_lin_indep (d : ℚ) (hd : d < 0) (x y : ℚ)
    (h : algebraMap ℚ Kd[d] x + algebraMap ℚ Kd[d] y * AdjoinRoot.root _ = 0) : x = 0 ∧ y = 0 := by
  have : Nontrivial Kd[d] := AdjoinRoot.nontrivial _ (by
    rw [Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num)
  have hinj := (algebraMap ℚ Kd[d]).injective
  by_cases hy : y = 0
  · subst hy
    simp only [map_zero, zero_mul, add_zero] at h
    exact ⟨hinj (h.trans (map_zero _).symm), rfl⟩
  · exfalso
    have h1 : algebraMap ℚ Kd[d] y * AdjoinRoot.root _ = -algebraMap ℚ Kd[d] x := by
      linear_combination h
    have h2 : (algebraMap ℚ Kd[d] y * AdjoinRoot.root _) ^ 2 = (algebraMap ℚ Kd[d] x) ^ 2 := by
      rw [h1]; ring
    rw [mul_pow, root_sq, ← map_pow, ← map_mul, ← map_pow] at h2
    have h3 := hinj h2
    have hy2 : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg x]

/-- The same with integer coefficients. -/
theorem root_lin_indep_int (d : ℚ) (hd : d < 0) (a c : ℤ)
    (h : a • (1 : Kd[d]) + c • AdjoinRoot.root _ = 0) : a = 0 ∧ c = 0 := by
  have := root_lin_indep d hd a c (by
    rw [map_intCast, map_intCast]; rw [zsmul_eq_mul, zsmul_eq_mul, mul_one] at h; exact h)
  exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩

/-- **N1a-CM proved from T6.** If `End⁰(A) ≅ M₂(ℚ(√d))`, `d < 0`, then `End_𝒪(A)` is isomorphic
to a subring of finite index of `𝒪_k`, `k = ℚ(√d)`: `1 ⊗ φ` (`φ ∈ End_𝒪(A)`) commutes with the
images `I, J` of `i, j ∈ 𝒪` (`I² = 2`, `J² = −3`, `JI = −IJ`), hence is a scalar
(`commute_quat_scalar`); `φ ↦` that scalar is an injective ring map `ψ` (T6); its image `R`
consists of integral elements (T6: `End(A)` is finite over `ℤ`), and contains `1` and `s√d`,
`s ≠ 0` (FS4's localization step), so it has rank 2 in `𝒪_k` and finite index. -/
theorem comOfMatrixEnd0_of_homFree (hHF : PkgI3.HomFreeFinite) : ComOfMatrixEnd0 := by
  intro A q d hd hM
  obtain ⟨e⟩ := hM
  letI : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ)) :=
    ⟨irred_sq_sub d hd⟩
  obtain ⟨hNF, hTC⟩ := adjRoot_numberField d hd
  obtain ⟨hfree, hfin, -, -⟩ := hHF Qbar A A
  let g : LeafQM.O →+* AbVar.End0 A :=
    (Algebra.TensorProduct.includeRight : AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] AbVar.End A).toRingHom.comp
      q.iota
  have e1 : ∀ a b : AbVar.End A,
      (1 : ℚ) ⊗ₜ[ℤ] (a * b) = ((1 : ℚ) ⊗ₜ[ℤ] a) * ((1 : ℚ) ⊗ₜ[ℤ] b) := by
    intro a b; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  have hI : e (g oi) * e (g oi) = (2 : Kd[d]) • (1 : Matrix (Fin 2) (Fin 2) Kd[d]) := by
    rw [← map_mul, ← map_mul, oi_mul_oi, map_ofNat, map_ofNat, Algebra.smul_def, mul_one,
      map_ofNat]
  have hJ : e (g oj) * e (g oj) = (-3 : Kd[d]) • (1 : Matrix (Fin 2) (Fin 2) Kd[d]) := by
    rw [← map_mul, ← map_mul, oj_mul_oj, map_neg, map_neg, map_ofNat, map_ofNat,
      Algebra.smul_def, mul_one, map_neg, map_ofNat]
  have hJI : e (g oj) * e (g oi) = -(e (g oi) * e (g oj)) := by
    rw [← map_mul, ← map_mul, oj_mul_oi, map_neg, map_neg, map_mul, map_mul]
  have hcommφ : ∀ φ ∈ com q, ∀ a : LeafQM.O,
      ((1 : ℚ) ⊗ₜ[ℤ] φ) * g a = g a * ((1 : ℚ) ⊗ₜ[ℤ] φ) := by
    intro φ hφ a
    rw [com, Subring.mem_centralizer_iff] at hφ
    show ((1 : ℚ) ⊗ₜ[ℤ] φ) * ((1 : ℚ) ⊗ₜ[ℤ] q.iota a) = ((1 : ℚ) ⊗ₜ[ℤ] q.iota a) * _
    rw [← e1, ← e1, hφ _ ⟨a, rfl⟩]
  have hsc : ∀ φ ∈ com q, e ((1 : ℚ) ⊗ₜ[ℤ] φ) =
      (e ((1 : ℚ) ⊗ₜ[ℤ] φ) 0 0) • (1 : Matrix (Fin 2) (Fin 2) Kd[d]) := by
    intro φ hφ
    obtain ⟨a, ha⟩ := commute_quat_scalar (e (g oi)) (e (g oj)) hI hJ hJI two_ne_zero
      three_ne_zero (e ((1 : ℚ) ⊗ₜ[ℤ] φ))
      (by rw [← map_mul, ← map_mul, hcommφ φ hφ oi])
      (by rw [← map_mul, ← map_mul, hcommφ φ hφ oj])
    rw [ha]; simp
  -- the scalar map `ψ : End_𝒪(A) → ℚ(√d)`
  let ψ : com q →+* Kd[d] :=
    { toFun := fun φ => e ((1 : ℚ) ⊗ₜ[ℤ] (φ : AbVar.End A)) 0 0
      map_one' := by
        simp only [OneMemClass.coe_one]
        rw [← Algebra.TensorProduct.one_def, map_one, Matrix.one_apply_eq]
      map_mul' := fun φ φ' => by
        simp only [MulMemClass.coe_mul]
        rw [e1, map_mul, hsc φ φ.2, hsc φ' φ'.2, smul_mul_smul_comm, one_mul]
        simp
      map_zero' := by simp
      map_add' := fun φ φ' => by simp [TensorProduct.tmul_add] }
  have hψ : ∀ φ : com q, e ((1 : ℚ) ⊗ₜ[ℤ] (φ : AbVar.End A)) = ψ φ • 1 := fun φ => hsc φ φ.2
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ0
    have h0 : e ((1 : ℚ) ⊗ₜ[ℤ] (φ : AbVar.End A)) = 0 := by rw [hψ, hφ0, zero_smul]
    rw [← map_zero e] at h0
    exact Subtype.ext (tmul_one_injective hfree _ (e.injective h0))
  -- an element `s√d` in the image (FS4's localization step)
  set c' : AbVar.End0 A :=
    e.symm ((AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ)) •
      (1 : Matrix (Fin 2) (Fin 2) Kd[d])) with hc'
  have hcen : ∀ x : AbVar.End0 A, c' * x = x * c' := by
    intro x
    apply e.injective
    rw [map_mul, map_mul, hc', e.apply_symm_apply, smul_mul_assoc, one_mul, mul_smul_comm,
      mul_one]
  let f := TensorProduct.mk ℤ ℚ (AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ f).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := AbVar.End A) (S := ℚ))
  obtain ⟨⟨φ₀, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) f c'
  have hs' : (1 : ℚ) ⊗ₜ[ℤ] φ₀ = (s : ℤ) • c' := by
    rw [Submonoid.smul_def] at hs; exact hs.symm
  have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hφ₀ : φ₀ ∈ com q := by
    rw [com, Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    have key : (1 : ℚ) ⊗ₜ[ℤ] (q.iota a * φ₀ - φ₀ * q.iota a) = 0 := by
      rw [TensorProduct.tmul_sub, e1, e1, hs', mul_smul_comm, smul_mul_assoc, ← smul_sub,
        hcen, sub_self, smul_zero]
    exact sub_eq_zero.mp (tmul_one_injective hfree _ key)
  have hw : ψ ⟨φ₀, hφ₀⟩ = (s : ℤ) • AdjoinRoot.root _ := by
    change e ((1 : ℚ) ⊗ₜ[ℤ] φ₀) 0 0 = _
    rw [hs', map_zsmul, hc', e.apply_symm_apply]
    simp
  -- the order `R = ψ(End_𝒪(A))`
  have hRint : ψ.range ≤ (integralClosure ℤ Kd[d]).toSubring := by
    rintro _ ⟨φ, rfl⟩
    have h1 : IsIntegral ℤ (φ : AbVar.End A) := Algebra.IsIntegral.isIntegral _
    have h2 : IsIntegral ℤ φ :=
      (isIntegral_algHom_iff ((com q).subtype.toIntAlgHom) Subtype.val_injective).mp h1
    exact h2.map ψ.toIntAlgHom
  refine ⟨Kd[d], inferInstance, hNF, hTC, finrank_adjRoot d, ψ.range, hRint, ?_,
    ⟨RingEquiv.ofBijective ψ.rangeRestrict
      ⟨fun a b h => hψinj (congrArg Subtype.val h), ψ.rangeRestrict_surjective⟩⟩⟩
  -- finite index: `R ∩ 𝒪_k` has rank 2 (it contains `1` and `s√d`)
  let fO : NumberField.RingOfIntegers Kd[d] →+ Kd[d] :=
    (algebraMap (NumberField.RingOfIntegers Kd[d]) Kd[d]).toAddMonoidHom
  have hrange : (integralClosure ℤ Kd[d]).toSubring.toAddSubgroup =
      (⊤ : AddSubgroup (NumberField.RingOfIntegers Kd[d])).map fO := by
    ext x
    constructor
    · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
    · rintro ⟨y, -, rfl⟩; exact y.2
  unfold LeafQM.AV.conductor
  suffices hsuff : (ψ.range.toAddSubgroup.comap fO).index ≠ 0 by
    convert hsuff using 1
    rw [← AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_comap, ← hrange]
    rfl
  let N' : Submodule ℤ (NumberField.RingOfIntegers Kd[d]) :=
    (ψ.range.toAddSubgroup.comap fO).toIntSubmodule
  have hw' : IsIntegral ℤ ((s : ℤ) •
      AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ)) := by
    rw [← hw]; exact hRint ⟨_, rfl⟩
  let w' : NumberField.RingOfIntegers Kd[d] := ⟨_, hw'⟩
  have h1N : (1 : NumberField.RingOfIntegers Kd[d]) ∈ N' := by
    show fO 1 ∈ ψ.range
    rw [show fO 1 = 1 from map_one (algebraMap (NumberField.RingOfIntegers Kd[d]) Kd[d])]
    exact ψ.range.one_mem
  have hwN : w' ∈ N' := ⟨⟨φ₀, hφ₀⟩, hw⟩
  have hv : LinearIndependent ℤ ![(⟨1, h1N⟩ : N'), ⟨w', hwN⟩] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hK := congrArg (fun z : N' => fO (z : NumberField.RingOfIntegers Kd[d])) hab
    simp only [Submodule.coe_add, Submodule.coe_smul, map_add, map_zsmul, Submodule.coe_zero,
      map_zero] at hK
    have e1' : fO 1 = 1 := map_one (algebraMap (NumberField.RingOfIntegers Kd[d]) Kd[d])
    have e2' : fO w' = (s : ℤ) •
        AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ) := rfl
    rw [e1', e2', smul_smul] at hK
    obtain ⟨ha, hbs⟩ := root_lin_indep_int d hd _ _ hK
    exact ⟨ha, (mul_eq_zero.mp hbs).resolve_right hs0⟩
  have hfr : Module.finrank ℤ N' = Module.finrank ℤ (NumberField.RingOfIntegers Kd[d]) := by
    apply le_antisymm (Submodule.finrank_le N')
    rw [NumberField.RingOfIntegers.rank, finrank_adjRoot]
    simpa using hv.fintype_card_le_finrank
  have := Submodule.finiteQuotientOfFreeOfRankEq N' hfr
  exact AddSubgroup.index_ne_zero_of_finite (hH := this)

/-- **N1a proved from the leaves T27 (Yu) and T6.** -/
theorem comIntOrQuadOrder_of_leaves (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) :
    ComIntOrQuadOrder :=
  comIntOrQuadOrder_of t27 t6 (comOfMatrixEnd0_of_homFree t6)

/-- **FS5 with the repaired clauses, from the leaves and named glue**: the bundle, R5fpCount,
T27, T6 and N1b (leaves), and `MobiusGlue` and N2 (glue). -/
theorem fibreComTrivialFull_of_leaves' (hL : R1R2fpFull) (hM : MobiusGlue)
    (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) (hB : CMConductorCoprime6)
    (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialFull :=
  fibreComTrivialFull_of hL hM (comIntOrQuadOrder_of_leaves t27 t6) hB hK hC

end FS5NoCM

#print axioms FS5NoCM.commute_quat_scalar
#print axioms FS5NoCM.adjRoot_numberField
#print axioms FS5NoCM.comOfMatrixEnd0_of_homFree
#print axioms FS5NoCM.comIntOrQuadOrder_of_leaves
#print axioms FS5NoCM.fibreComTrivialFull_of_leaves'
