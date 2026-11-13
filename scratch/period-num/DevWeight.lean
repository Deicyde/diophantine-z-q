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

end HSyn.G0Split.FibreQM.PeriodNum

end
