
/-! ## §4. Toward `CMPointEmbeddingCorrespondence`: linear algebra of `ρ` -/

namespace ZInQ.HeightGlue.QM

open LeafQM LeafQM.AV NumberField ZInQ.HeightSplit.R5 Matrix ComplexConjugate

/-- `√2 ∈ ℂ`. -/
noncomputable abbrev s2 : ℂ := (Real.sqrt 2 : ℂ)

theorem s2_ne_zero : s2 ≠ 0 := by
  simp [s2]

theorem conj_s2 : conj s2 = s2 := Complex.conj_ofReal _

/-- The explicit matrix of `ρ(b)`. -/
theorem rho_apply (b : B) : rho b =
    !![(b.re : ℂ) + b.imI * s2, -3 * (b.imJ : ℂ) - 3 * s2 * b.imK;
      (b.imJ : ℂ) - s2 * b.imK, (b.re : ℂ) - b.imI * s2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, rhoBasis, QuaternionAlgebra.Basis.lift, Matrix.mul_apply,
      Algebra.algebraMap_eq_smul_one, Rat.smul_def] <;> ring

/-- The entries of `ρ(b)` are real. -/
theorem conj_rho (b : B) (i j : Fin 2) : conj (rho b i j) = rho b i j := by
  rw [rho_apply]
  fin_cases i <;> fin_cases j <;> simp [map_add, map_sub, map_mul, map_ofNat]

/-- `ρ` is injective. -/
theorem rho_eq_zero {b : B} (h : rho b = 0) : b = 0 := by
  rw [rho_apply] at h
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp at e00 e01 e10 e11
  have hre : (b.re : ℂ) = 0 := by linear_combination (e00 + e11) / 2
  have hI : (b.imI : ℂ) * s2 = 0 := by linear_combination (e00 - e11) / 2
  have hJ : (b.imJ : ℂ) = 0 := by linear_combination (e10 * 3 - e01) / 6
  have hK : s2 * (b.imK : ℂ) = 0 := by linear_combination (-e10 * 3 - e01) / 6
  have hI' : (b.imI : ℂ) = 0 := (mul_eq_zero.mp hI).resolve_right s2_ne_zero
  have hK' : (b.imK : ℂ) = 0 := (mul_eq_zero.mp hK).resolve_left s2_ne_zero
  ext <;> simp_all

theorem rho_injective : Function.Injective rho := fun a b h =>
  sub_eq_zero.mp (rho_eq_zero (by rw [map_sub, h, sub_self]))

/-- The eigenvector equation for `(τ, 1)ᵀ`, coordinatewise. -/
theorem eig_iff (M : Matrix (Fin 2) (Fin 2) ℂ) (τ μ : ℂ) :
    M *ᵥ ![τ, 1] = μ • ![τ, 1] ↔ M 0 0 * τ + M 0 1 = μ * τ ∧ M 1 0 * τ + M 1 1 = μ := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, h0, h1]

/-- The complex conjugate eigenvector. -/
theorem eig_conj {b : B} {τ μ : ℂ} (h : rho b *ᵥ ![τ, 1] = μ • ![τ, 1]) :
    rho b *ᵥ ![conj τ, 1] = conj μ • ![conj τ, 1] := by
  rw [eig_iff] at h ⊢
  obtain ⟨h0, h1⟩ := h
  have c0 := congrArg conj h0
  have c1 := congrArg conj h1
  simp only [map_add, map_mul, conj_rho] at c0 c1
  exact ⟨c0, c1⟩

/-- A matrix killing `(τ, 1)ᵀ` and `(τ̄, 1)ᵀ`, `τ ∉ ℝ`, is zero. -/
theorem eq_zero_of_kill (N : Matrix (Fin 2) (Fin 2) ℂ) {τ : ℂ} (hτ : τ.im ≠ 0)
    (h1 : N *ᵥ ![τ, 1] = 0) (h2 : N *ᵥ ![conj τ, 1] = 0) : N = 0 := by
  have h1' : N *ᵥ ![τ, 1] = (0 : ℂ) • ![τ, 1] := by rw [h1, zero_smul]
  have h2' : N *ᵥ ![conj τ, 1] = (0 : ℂ) • ![conj τ, 1] := by rw [h2, zero_smul]
  rw [eig_iff] at h1' h2'
  have hne : τ - conj τ ≠ 0 := by
    intro h
    apply hτ
    have := congrArg Complex.im h
    simp [Complex.sub_im, Complex.conj_im] at this
    linarith
  have a00 : N 0 0 = 0 := by
    have : N 0 0 * (τ - conj τ) = 0 := by linear_combination h1'.1 - h2'.1
    exact (mul_eq_zero.mp this).resolve_right hne
  have a10 : N 1 0 = 0 := by
    have : N 1 0 * (τ - conj τ) = 0 := by linear_combination h1'.2 - h2'.2
    exact (mul_eq_zero.mp this).resolve_right hne
  have a01 : N 0 1 = 0 := by linear_combination h1'.1 - τ * a00
  have a11 : N 1 1 = 0 := by linear_combination h1'.2 - τ * a10
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a00, a01, a10, a11]

/-- **Same eigenvalue at `(τ, 1)ᵀ`, `τ ∉ ℝ`, means equal.** -/
theorem eq_of_eig {a b : B} {τ μ : ℂ} (hτ : τ.im ≠ 0) (ha : rho a *ᵥ ![τ, 1] = μ • ![τ, 1])
    (hb : rho b *ᵥ ![τ, 1] = μ • ![τ, 1]) : a = b := by
  apply sub_eq_zero.mp
  apply rho_eq_zero
  apply eq_zero_of_kill _ hτ
  · rw [map_sub, sub_mulVec, ha, hb, sub_self]
  · rw [map_sub, sub_mulVec, eig_conj ha, eig_conj hb, sub_self]

/-- Two elements with `(τ, 1)ᵀ` as common eigenvector commute (`τ ∉ ℝ`). -/
theorem commute_of_eig {a b : B} {τ μ ν : ℂ} (hτ : τ.im ≠ 0)
    (ha : rho a *ᵥ ![τ, 1] = μ • ![τ, 1]) (hb : rho b *ᵥ ![τ, 1] = ν • ![τ, 1]) :
    a * b = b * a := by
  have hab : rho (a * b) *ᵥ ![τ, 1] = (ν * μ) • ![τ, 1] := by
    rw [map_mul, ← mulVec_mulVec, hb, mulVec_smul, ha, smul_smul]
  have hba : rho (b * a) *ᵥ ![τ, 1] = (ν * μ) • ![τ, 1] := by
    rw [map_mul, ← mulVec_mulVec, ha, mulVec_smul, hb, smul_smul, mul_comm]
  exact eq_of_eig hτ hab hba

/-- **The centralizer of a non-scalar element `β` of `B` is `ℚ + ℚβ`.** -/
theorem exists_eq_of_commute {β b : B} (hβ : ∀ r : ℚ, β ≠ (r : B)) (h : b * β = β * b) :
    ∃ r t : ℚ, b = (r : B) + t • β := by
  have e := congrArg (fun x : B => (x.imI, x.imJ, x.imK)) h
  simp only [QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul,
    Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3⟩ := e
  -- the pure parts are parallel: `b.imJ β.imK = b.imK β.imJ` etc.
  have p1 : b.imJ * β.imK = b.imK * β.imJ := by nlinarith
  have p2 : b.imI * β.imK = b.imK * β.imI := by nlinarith
  have p3 : b.imI * β.imJ = b.imJ * β.imI := by nlinarith
  have hpure : β.imI ≠ 0 ∨ β.imJ ≠ 0 ∨ β.imK ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hβ β.re
    ext <;> simp [hc.1, hc.2.1, hc.2.2]
  rcases hpure with h1 | h1 | h1
  · refine ⟨b.re - b.imI / β.imI * β.re, b.imI / β.imI, ?_⟩
    ext <;> simp <;> field_simp <;> linarith
  · refine ⟨b.re - b.imJ / β.imJ * β.re, b.imJ / β.imJ, ?_⟩
    ext <;> simp <;> field_simp <;> linarith
  · refine ⟨b.re - b.imK / β.imK * β.re, b.imK / β.imK, ?_⟩
    ext <;> simp <;> field_simp <;> linarith

end ZInQ.HeightGlue.QM
