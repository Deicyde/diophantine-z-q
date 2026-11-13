import PNBase

/-! ## period-num: `S8WeightExact` from `ThetaModularity` and `NormalizerDecomp`

For `γ = ι(x) ∈ Γ*` write `x = r·w·u` (`NormalizerDecomp`: `r ∈ ℚ^×`, `w ∈ {1, i, j + ij, μ}`,
`u ∈ 𝒪^×`) and put `z = r⁻¹w⁻¹`. The map `b ↦ z b x = w⁻¹ b w u` preserves `𝒪` and the Riemann form
`E(a, b) = Trd(μ⁻¹ a b̄)` (`Bf`). The `ℂ`-linear map `Ψ = j(γ, τ)·ι(z)` carries `Λ_{γτ}` onto `Λ_τ`
(`ι(z)ι(b)ι(x)(τ, 1)ᵀ = j(γ, τ)ι(z)ι(b)(γτ, 1)ᵀ`), so in the symplectic basis `sB` of `𝒪` its matrix
`N ∈ M₄(ℤ)` satisfies `NᵀGN = G` and `Ω(γτ) = Nᵀ·Ω(τ)` (`omega_transform`), with
`det(CΩ + D) = j(γ, τ)² nrd(z) dF(γτ)/dF(τ)`. Igusa's `ThetaModularity` then gives
`G8(γτ)·det(γ)⁴ = j(γ, τ)⁸ G8(τ)` (`s8WeightExact_of`). -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodNum

open Complex Matrix
open HSyn.G0Split.FibreQM.PeriodMap
open UpperHalfPlane (num denom denom_ne_zero)

/-! ### Reduced norm and the Riemann form -/

/-- The reduced norm of `B = (2, −3)`. -/
def nrd (a : PkgI1.B) : ℚ := a.re ^ 2 - 2 * a.imI ^ 2 + 3 * a.imJ ^ 2 - 6 * a.imK ^ 2

theorem nrd_mul (a b : PkgI1.B) : nrd (a * b) = nrd a * nrd b := by
  simp only [nrd, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]
  ring

theorem nrd_one : nrd 1 = 1 := by simp [nrd]

theorem det_iota_eq (a : PkgI1.B) : (PkgI1.iota a).det = (nrd a : ℝ) := by
  rw [det_iota, nrd]; push_cast; ring

/-- The Riemann form `E(a, b) = Trd(μ⁻¹ a b̄)` on `B`. -/
def Bf (a b : PkgI1.B) : ℚ := PkgI1.trd (PkgI1.muInv * a * star b)

theorem Bf_mul_right (a b u : PkgI1.B) : Bf (a * u) (b * u) = nrd u * Bf a b := by
  simp only [Bf, PkgI1.trd, PkgI1.muInv, nrd, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_star,
    QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star]
  ring

/-! ### The symplectic basis `sB` of `𝒪` and coordinates -/

/-- `f₀ = −2·(1+j)/2 − (i+ij)/2`. -/
def sf0 : PkgI1.B := ⟨-1, -1/2, -1, -1/2⟩
/-- `f₁ = −(1+j)/2 − (i+ij)/2`. -/
def sf1 : PkgI1.B := ⟨-1/2, -1/2, -1/2, -1/2⟩

/-- The symplectic basis `(e₀, e₁, f₀, f₁) = (1, i, f₀, f₁)` of `𝒪` (`(f₀, f₁) = (b₂, b₃)P⁻¹`). -/
def sB : Fin 2 ⊕ Fin 2 → PkgI1.B := Sum.elim ![PkgI1.oBasis 0, PkgI1.oBasis 1] ![sf0, sf1]

/-- Coordinates in `sB`. -/
def kap (a : PkgI1.B) : Fin 2 ⊕ Fin 2 → ℚ :=
  Sum.elim ![a.re - a.imJ, a.imI - a.imK] ![2 * a.imK - 2 * a.imJ, 2 * a.imJ - 4 * a.imK]

theorem sum_kap (a : PkgI1.B) : ∑ k, kap a k • sB k = a := by
  ext <;> simp [Fintype.sum_sum_type, Fin.sum_univ_two, kap, sB, sf0, sf1, PkgI1.oBasis] <;> ring

theorem kap_int {a : PkgI1.B} (h : PkgI1.InO a) (k : Fin 2 ⊕ Fin 2) : ∃ n : ℤ, kap a k = n := by
  obtain ⟨n, rfl⟩ := h
  rcases k with k | k <;> fin_cases k
  · exact ⟨n 0, by simp [kap, PkgI1.oBasis, Fin.sum_univ_four]⟩
  · exact ⟨n 1, by simp [kap, PkgI1.oBasis, Fin.sum_univ_four]⟩
  · exact ⟨n 3 - n 2, by simp [kap, PkgI1.oBasis, Fin.sum_univ_four]; ring⟩
  · exact ⟨n 2 - 2 * n 3, by simp [kap, PkgI1.oBasis, Fin.sum_univ_four]; ring⟩

theorem kap_sB (k l : Fin 2 ⊕ Fin 2) : kap (sB k) l = if k = l then 1 else 0 := by
  rcases k with k | k <;> rcases l with l | l <;> fin_cases k <;> fin_cases l <;>
    simp [kap, sB, sf0, sf1, PkgI1.oBasis] <;> norm_num

/-- The Gram matrix of `E` in `sB`: `[[0, 1], [−1, 0]] = −J`. -/
def Gm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ := fromBlocks 0 1 (-1) 0

theorem Bf_expand (a b : PkgI1.B) : Bf a b = ∑ l, ∑ m, kap a l * Gm l m * kap b m := by
  simp only [Bf, PkgI1.trd, PkgI1.muInv, kap, Gm, Fintype.sum_sum_type, Fin.sum_univ_two,
    QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply]
  simp
  ring

/-! ### Lattice vectors -/

theorem latVec_eq (a : PkgI1.B) (τ : ℂ) : PkgI1.latVec a τ =
    ![(((a.re : ℝ) + a.imI * √2 : ℝ) : ℂ) * τ + ((-3 * (a.imJ : ℝ) - 3 * √2 * a.imK : ℝ) : ℂ),
      (((a.imJ : ℝ) - √2 * a.imK : ℝ) : ℂ) * τ + (((a.re : ℝ) - a.imI * √2 : ℝ) : ℂ)] := by
  funext r
  rw [latVec_apply, iota_apply]
  fin_cases r <;> simp

theorem latVec_lin (c : Fin 2 ⊕ Fin 2 → ℚ) (τ : ℂ) :
    PkgI1.latVec (∑ k, c k • sB k) τ = ∑ k, ((c k : ℚ) : ℂ) • PkgI1.latVec (sB k) τ := by
  funext r
  simp only [latVec_eq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases r <;>
    simp [Fintype.sum_sum_type, Fin.sum_univ_two, sB, sf0, sf1, PkgI1.oBasis] <;> ring

theorem latVec_mul (a b : PkgI1.B) (τ : ℂ) :
    PkgI1.latVec (a * b) τ = (PkgI1.iota a).map (fun r : ℝ => (r : ℂ)) *ᵥ PkgI1.latVec b τ := by
  unfold PkgI1.latVec
  rw [iota_mul, Matrix.mulVec_mulVec]
  congr 1
  exact Matrix.map_mul (f := Complex.ofRealHom)

/-- `ι(x)(τ, 1)ᵀ = j(γ, τ)(γτ, 1)ᵀ`. -/
theorem iota_v {x : PkgI1.B} {γ : GL (Fin 2) ℝ} (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x)
    (hdet : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) (τ : UpperHalfPlane) :
    (PkgI1.iota x).map (fun r : ℝ => (r : ℂ)) *ᵥ ![(τ : ℂ), 1] =
      denom γ τ • ![((γ • τ : UpperHalfPlane) : ℂ), 1] := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (by simpa using hdet)]
  have hd := denom_ne_zero γ τ
  have hd' : ((τ : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℝ) +
      ((γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℝ)) ≠ 0 := by rw [mul_comm]; exact hd
  funext r
  fin_cases r <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, num, denom, ← hγ] <;>
    field_simp

theorem latVec_smul_tau {x : PkgI1.B} {γ : GL (Fin 2) ℝ}
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x)
    (hdet : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) (τ : UpperHalfPlane) (b : PkgI1.B) :
    PkgI1.latVec (b * x) τ = denom γ τ • PkgI1.latVec b ((γ • τ : UpperHalfPlane) : ℂ) := by
  rw [latVec_mul]
  unfold PkgI1.latVec
  rw [iota_v hγ hdet, Matrix.mulVec_smul]

theorem Emat_eq (τ : ℂ) : PkgI1.Emat τ = Matrix.of fun r c => PkgI1.latVec (sB (Sum.inl c)) τ r := by
  ext r c; fin_cases c <;> rfl

theorem Fm_eq (τ : ℂ) :
    PkgI1.F0mat τ * PkgI1.Pinv = Matrix.of fun r c => PkgI1.latVec (sB (Sum.inr c)) τ r := by
  ext r c
  simp only [Matrix.mul_apply, Fin.sum_univ_two, PkgI1.F0mat, PkgI1.Pinv, Matrix.of_apply, latVec_eq]
  fin_cases r <;> fin_cases c <;> simp [sB, sf0, sf1, PkgI1.oBasis] <;> ring

theorem sB_inO (k : Fin 2 ⊕ Fin 2) : PkgI1.InO (sB k) := by
  rcases k with k | k <;> fin_cases k
  · exact ⟨![1, 0, 0, 0], by ext <;> simp [sB, PkgI1.oBasis, Fin.sum_univ_four]⟩
  · exact ⟨![0, 1, 0, 0], by ext <;> simp [sB, PkgI1.oBasis, Fin.sum_univ_four]⟩
  · exact ⟨![0, 0, -2, -1], by ext <;> simp [sB, sf0, PkgI1.oBasis, Fin.sum_univ_four] <;> norm_num⟩
  · exact ⟨![0, 0, -1, -1], by ext <;> simp [sB, sf1, PkgI1.oBasis, Fin.sum_univ_four] <;> norm_num⟩

/-! ### The integer matrix `N` and the transformation of `Ω` -/

/-- The integer matrix of `b ↦ z b x` in the basis `sB` (column `k` = coordinates of `z·sB_k·x`). -/
def Nmat {x z : PkgI1.B} (hO : ∀ b, PkgI1.InO b → PkgI1.InO (z * b * x)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ :=
  fun l k => Classical.choose (kap_int (hO (sB k) (sB_inO k)) l)

theorem Nmat_spec {x z : PkgI1.B} (hO : ∀ b, PkgI1.InO b → PkgI1.InO (z * b * x))
    (l k : Fin 2 ⊕ Fin 2) : ((Nmat hO l k : ℤ) : ℚ) = kap (z * sB k * x) l :=
  (Classical.choose_spec (kap_int (hO (sB k) (sB_inO k)) l)).symm

theorem J_cast (l m : Fin 2 ⊕ Fin 2) : ((Matrix.J (Fin 2) ℤ l m : ℤ) : ℚ) = -Gm l m := by
  rcases l with l | l <;> rcases m with m | m <;>
    simp [Matrix.J, Gm, Matrix.one_apply]

/-- `Nᵀ ∈ Sp₄(ℤ)` when `b ↦ z b x` preserves the Riemann form. -/
theorem Nmat_symp {x z : PkgI1.B} (hO : ∀ b, PkgI1.InO b → PkgI1.InO (z * b * x))
    (hB : ∀ a b, Bf (z * a * x) (z * b * x) = Bf a b) :
    (Nmat hO)ᵀ ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  rw [SymplecticGroup.mem_iff, Matrix.transpose_transpose]
  set N := Nmat hO
  have hG : ∀ k k', ∑ l, ∑ m, (N l k : ℚ) * Gm l m * (N m k' : ℚ) = Gm k k' := by
    intro k k'
    simp_rw [N, Nmat_spec]
    rw [← Bf_expand, hB, Bf_expand]
    simp [kap_sB]
  ext k k'
  apply Int.cast_injective (α := ℚ)
  calc ((Nᵀ * Matrix.J (Fin 2) ℤ * N) k k' : ℚ)
      = ∑ m, ∑ l, (N l k : ℚ) * (Matrix.J (Fin 2) ℤ l m : ℚ) * (N m k' : ℚ) := by
        simp [Matrix.mul_apply]; ring
    _ = -∑ l, ∑ m, (N l k : ℚ) * Gm l m * (N m k' : ℚ) := by
        rw [Finset.sum_comm]; simp [J_cast, Finset.sum_neg_distrib]; ring
    _ = ((Matrix.J (Fin 2) ℤ k k' : ℤ) : ℚ) := by rw [hG, J_cast]

/-- `Ψ = j(γ, τ)·ι(z)`. -/
def Psi (z : PkgI1.B) (γ : GL (Fin 2) ℝ) (τ : UpperHalfPlane) : Matrix (Fin 2) (Fin 2) ℂ :=
  denom γ τ • (PkgI1.iota z).map (fun r : ℝ => (r : ℂ))

theorem det_Psi (z : PkgI1.B) (γ : GL (Fin 2) ℝ) (τ : UpperHalfPlane) :
    (Psi z γ τ).det = denom γ τ ^ 2 * ((PkgI1.iota z).det : ℂ) := by
  rw [Psi, Matrix.det_smul, Fintype.card_fin, Matrix.det_fin_two, Matrix.det_fin_two]
  simp

theorem psi_latVec {x z : PkgI1.B} {γ : GL (Fin 2) ℝ} (hO : ∀ b, PkgI1.InO b → PkgI1.InO (z * b * x))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x)
    (hdet : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) (τ : UpperHalfPlane) (k : Fin 2 ⊕ Fin 2) :
    Psi z γ τ *ᵥ PkgI1.latVec (sB k) ((γ • τ : UpperHalfPlane) : ℂ) =
      ∑ l, ((Nmat hO l k : ℤ) : ℂ) • PkgI1.latVec (sB l) τ := by
  have h1 : ∑ l, ((Nmat hO l k : ℤ) : ℂ) • PkgI1.latVec (sB l) τ =
      PkgI1.latVec (z * sB k * x) τ := by
    rw [← sum_kap (z * sB k * x), latVec_lin]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Nmat_spec hO l k]; push_cast; rfl
  rw [h1, mul_assoc, latVec_mul, latVec_smul_tau hγ hdet τ, Psi, Matrix.smul_mulVec,
    Matrix.mulVec_smul]

/-- The two block equations `Ψ E' = E N₁₁ + F N₂₁`, `Ψ F' = E N₁₂ + F N₂₂`. -/
theorem blocks {x z : PkgI1.B} {γ : GL (Fin 2) ℝ} (hO : ∀ b, PkgI1.InO b → PkgI1.InO (z * b * x))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x)
    (hdet : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) (τ : UpperHalfPlane) :
    Psi z γ τ * PkgI1.Emat ((γ • τ : UpperHalfPlane) : ℂ) =
        PkgI1.Emat τ * ((Nmat hO).map (Int.cast : ℤ → ℂ)).toBlocks₁₁ +
          (PkgI1.F0mat τ * PkgI1.Pinv) * ((Nmat hO).map (Int.cast : ℤ → ℂ)).toBlocks₂₁ ∧
    Psi z γ τ * (PkgI1.F0mat ((γ • τ : UpperHalfPlane) : ℂ) * PkgI1.Pinv) =
        PkgI1.Emat τ * ((Nmat hO).map (Int.cast : ℤ → ℂ)).toBlocks₁₂ +
          (PkgI1.F0mat τ * PkgI1.Pinv) * ((Nmat hO).map (Int.cast : ℤ → ℂ)).toBlocks₂₂ := by
  rw [Emat_eq, Emat_eq, Fm_eq, Fm_eq]
  constructor
  · ext r c
    have := congrFun (psi_latVec hO hγ hdet τ (Sum.inl c)) r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_sum_type] at this
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₁, Matrix.map_apply]
    rw [this]; simp only [Fin.sum_univ_two]; ring
  · ext r c
    have := congrFun (psi_latVec hO hγ hdet τ (Sum.inr c)) r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_sum_type] at this
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₂, Matrix.map_apply]
    rw [this]; simp only [Fin.sum_univ_two]; ring

/-- Linear algebra: the block equations give `Ω' = Nᵀ·Ω` and the automorphy factor. -/
theorem spAct_of_blocks {Ω Ω' E F E' F' Ψ : Matrix (Fin 2) (Fin 2) ℂ}
    {N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ}
    (hF : IsUnit F.det) (hF' : IsUnit F'.det) (hΨ : IsUnit Ψ.det) (hΩ : Ω = F⁻¹ * E)
    (hΩ' : Ω' = F'⁻¹ * E') (hs : Ωᵀ = Ω) (hs' : Ω'ᵀ = Ω')
    (h1 : Ψ * E' = E * (N.map (Int.cast : ℤ → ℂ)).toBlocks₁₁ + F * (N.map (Int.cast : ℤ → ℂ)).toBlocks₂₁)
    (h2 : Ψ * F' = E * (N.map (Int.cast : ℤ → ℂ)).toBlocks₁₂ + F * (N.map (Int.cast : ℤ → ℂ)).toBlocks₂₂) :
    Ω' = PkgI1.spAct Nᵀ Ω ∧ PkgI1.spFactor Nᵀ Ω * F.det = Ψ.det * F'.det := by
  set Nc := N.map (Int.cast : ℤ → ℂ) with hNc
  set X := Ω * Nc.toBlocks₁₂ + Nc.toBlocks₂₂ with hXdef
  have hFΩ : F * Ω = E := by rw [hΩ, ← mul_assoc, mul_nonsing_inv _ hF, one_mul]
  have hF'Ω : F' * Ω' = E' := by rw [hΩ', ← mul_assoc, mul_nonsing_inv _ hF', one_mul]
  have hFX : F * X = Ψ * F' := by rw [h2, hXdef, mul_add, ← mul_assoc, hFΩ]
  have hdetX : F.det * X.det = Ψ.det * F'.det := by rw [← det_mul, hFX, det_mul]
  have hX : IsUnit X.det := by
    have : IsUnit (F.det * X.det) := by rw [hdetX]; exact hΨ.mul hF'
    exact isUnit_of_mul_isUnit_right this
  have hXΩ : X * Ω' = Ω * Nc.toBlocks₁₁ + Nc.toBlocks₂₁ := by
    have e : F * (X * Ω') = F * (Ω * Nc.toBlocks₁₁ + Nc.toBlocks₂₁) := by
      rw [← mul_assoc, hFX, mul_assoc, hF'Ω, h1, mul_add, ← mul_assoc, hFΩ]
    have e2 := congrArg (F⁻¹ * ·) e
    simp only [← mul_assoc, nonsing_inv_mul _ hF, one_mul] at e2
    exact e2
  have hΩ'X : Ω' = X⁻¹ * (Ω * Nc.toBlocks₁₁ + Nc.toBlocks₂₁) := by
    rw [← hXΩ, ← mul_assoc, nonsing_inv_mul _ hX, one_mul]
  have hb11 : (Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₁₁ = Nc.toBlocks₁₁ᵀ := by ext; rfl
  have hb12 : (Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₁₂ = Nc.toBlocks₂₁ᵀ := by ext; rfl
  have hb21 : (Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₂₁ = Nc.toBlocks₁₂ᵀ := by ext; rfl
  have hb22 : (Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₂₂ = Nc.toBlocks₂₂ᵀ := by ext; rfl
  have hXT : Xᵀ = Nc.toBlocks₁₂ᵀ * Ω + Nc.toBlocks₂₂ᵀ := by
    rw [hXdef, transpose_add, transpose_mul, hs]
  constructor
  · show Ω' = (((Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₁₁ * Ω + (Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₁₂) *
      ((Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₂₁ * Ω + (Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₂₂)⁻¹)
    rw [hb11, hb12, hb21, hb22, ← hXT]
    calc Ω' = Ω'ᵀ := hs'.symm
      _ = (Ω * Nc.toBlocks₁₁ + Nc.toBlocks₂₁)ᵀ * X⁻¹ᵀ := by rw [hΩ'X, transpose_mul]
      _ = (Nc.toBlocks₁₁ᵀ * Ω + Nc.toBlocks₂₁ᵀ) * Xᵀ⁻¹ := by
        rw [transpose_nonsing_inv, transpose_add, transpose_mul, hs]
  · show ((Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₂₁ * Ω + (Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₂₂).det * F.det = _
    rw [hb21, hb22, ← hXT, det_transpose, mul_comm]
    exact hdetX

end HSyn.G0Split.FibreQM.PeriodNum

end
