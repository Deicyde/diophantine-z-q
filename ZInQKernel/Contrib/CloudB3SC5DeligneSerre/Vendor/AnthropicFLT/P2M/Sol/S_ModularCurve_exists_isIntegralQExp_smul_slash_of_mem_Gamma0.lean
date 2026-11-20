/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0 (git blob dbd697d0c6f738ec4ef6b31437dad693beedc6b0, sha256 df4221865bf6c2c5365d4117bc61aa7b47eadfa2399dc0fef721750abbbd5f84).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup Function ModularCurve
open scoped MatrixGroups ModularForm Manifold

namespace X1DiamondIntegral



variable {M : ℕ} {k : ℤ}

theorem conj_mem_Gamma1 {γ A : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hA : A ∈ Gamma1 M) :
    γ * A * γ⁻¹ ∈ Gamma1 M := by
  have hA0 : A ∈ Gamma0 M := Gamma1_in_Gamma0 M hA
  set A₀ : Gamma0 M := ⟨A, hA0⟩
  set γ₀ : Gamma0 M := ⟨γ, hγ⟩
  have hA1 : A₀ ∈ Gamma1' M := by
    rw [Gamma1_to_Gamma0_mem]
    exact (Gamma1_mem M A).mp hA
  haveI : (Gamma1' M).Normal := by
    change ((Gamma0Map M).ker).Normal
    infer_instance
  have hconj : γ₀ * A₀ * γ₀⁻¹ ∈ Gamma1' M := Subgroup.Normal.conj_mem inferInstance A₀ hA1 γ₀
  rw [Gamma1_to_Gamma0_mem] at hconj
  rw [Gamma1_mem]
  exact hconj

def diamondSlash [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)
  slash_action_eq' := by
    intro A hA
    obtain ⟨A, hA, rfl⟩ := hA
    have hconj : γ * A * γ⁻¹ ∈ Gamma1 M := conj_mem_Gamma1 hγ hA
    have hGL : (γ : GL (Fin 2) ℝ) * (A : GL (Fin 2) ℝ)
        = ((γ * A * γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * (γ : GL (Fin 2) ℝ) := by
      simp only [map_mul, map_inv, inv_mul_cancel_right]
    change ((⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) ∣[k] (A : GL (Fin 2) ℝ)
      = (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)
    rw [← SlashAction.slash_mul, hGL, SlashAction.slash_mul]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hconj)
  holo' := f.holo'.slash k _
  bdd_at_cusps' := by
    intro c hc
    have hcSL : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).mp hc
    have hc' : IsCusp ((γ : GL (Fin 2) ℝ) • c) ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
      exact hcSL.smul_of_mem ⟨γ, rfl⟩
    exact OnePoint.IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' hc')

theorem coe_diamondSlash [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    (⇑(diamondSlash γ hγ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] γ := by
  rw [ModularForm.SL_slash]; rfl

theorem rat_of_isIntegralQExp {f : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp f p) (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 f).coeff n = (r : ℂ) :=
  ⟨(PowerSeries.coeff n p : ℤ), by rw [← h.coeff n]; push_cast; rfl⟩

end X1DiamondIntegral

open X1DiamondIntegral in
theorem solution (M : ℕ) [NeZero M] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    {p : PowerSeries ℤ} (hp : ModularCurve.IsIntegralQExp f p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    ∃ (D : ℤ) (f₁ : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
      (p₁ : PowerSeries ℤ), D ≠ 0 ∧ ModularCurve.IsIntegralQExp f₁ p₁ ∧
        (⇑f₁ : UpperHalfPlane → ℂ) = (D : ℂ) • ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) := by

  have hrat := ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0 M f
    (rat_of_isIntegralQExp hp) γ hγ

  set g : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k := diamondSlash γ hγ f
    with hg
  have hcoe : (⇑g : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] γ := coe_diamondSlash γ hγ f
  have hrat' : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 g).coeff n = (r : ℂ) := by
    rw [hcoe]; exact hrat

  obtain ⟨D, p₁, hD, hint⟩ := ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion M g hrat'
  refine ⟨D, (D : ℂ) • g, p₁, hD, ?_, ?_⟩
  · rw [IsGLPos.coe_smul]; exact hint
  · rw [IsGLPos.coe_smul, hcoe]
