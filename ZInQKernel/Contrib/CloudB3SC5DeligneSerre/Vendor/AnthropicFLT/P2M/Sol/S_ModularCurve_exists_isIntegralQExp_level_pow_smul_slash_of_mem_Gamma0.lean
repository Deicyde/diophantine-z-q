/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0 (git blob efbadb81da5acb762009ea49dfc37e233638dc61, sha256 c318f9da75142f614bd714d5026233cdbefe07139a284dcc40dbd4450842b8c8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_UpperHalfPlane_qExpansion_coeff_nat_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0

set_option autoImplicit false

open UpperHalfPlane in
open scoped MatrixGroups ModularForm Manifold in
set_option maxHeartbeats 3200000 in
theorem solution (M : ℕ) [NeZero M] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    {p : PowerSeries ℤ} (hp : ModularCurve.IsIntegralQExp f p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    ∃ (a : ℕ) (f₁ : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
      (p₁ : PowerSeries ℤ), ModularCurve.IsIntegralQExp f₁ p₁ ∧
        (⇑f₁ : UpperHalfPlane → ℂ) = ((M : ℂ) ^ a) • ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) := by
  classical
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h1per : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples 1

  obtain ⟨D, f₁', p₁', hD, hp₁', hf₁'⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 M f hp γ hγ
  have hDC : (D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hD

  set g : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k := ((D : ℂ)⁻¹) • f₁' with hgdef
  have hg : (⇑g : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) := by
    rw [hgdef, ModularForm.IsGLPos.coe_smul, hf₁', smul_smul, inv_mul_cancel₀ hDC, one_smul]
  have hqg : ∀ n : ℕ, (qExpansion 1 (⇑g : UpperHalfPlane → ℂ)).coeff n =
      ((D : ℂ)⁻¹) * ((PowerSeries.coeff n p₁' : ℤ) : ℂ) := by
    intro n
    rw [hgdef, ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos h1per, map_smul,
      smul_eq_mul, ← hp₁'.coeff n]

  have hper : Function.Periodic ((⇑g : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex g h1per
  haveI : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1per⟩
  have hbdd : IsBoundedAtImInfty (⇑g : UpperHalfPlane → ℂ) := ModularFormClass.bdd_at_infty g
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑g : UpperHalfPlane → ℂ) := ModularFormClass.holo g
  have hPC : ∀ n : ℕ, (qExpansion (M : ℝ) ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ)).coeff (M * n) =
      (qExpansion 1 (⇑g : UpperHalfPlane → ℂ)).coeff n := by
    intro n
    have h := UpperHalfPlane.qExpansion_coeff_nat_mul one_pos hper hhol hbdd hMpos (M * n)
    rw [mul_one, if_pos (dvd_mul_right M n), Nat.mul_div_cancel_left n hMpos] at h
    rw [← hg]
    exact h

  obtain ⟨a, ha⟩ := ModularCurve.exists_isIntegral_level_pow_mul_qExpansion_slash_coeff M f hp γ

  set r : ℕ → ℚ := fun n => (M : ℚ) ^ a * ((D : ℚ)⁻¹ * ((PowerSeries.coeff n p₁' : ℤ) : ℚ)) with hrdef
  have hrC : ∀ n : ℕ, algebraMap ℚ ℂ (r n) = (M : ℂ) ^ a * (qExpansion 1 (⇑g : UpperHalfPlane → ℂ)).coeff n := by
    intro n
    rw [hqg n, hrdef]
    simp only [eq_ratCast]
    push_cast
    ring
  have hrint : ∀ n : ℕ, IsIntegral ℤ (r n) := by
    intro n
    have h := ha (M * n)
    rw [hPC n, ← hrC n] at h
    exact isIntegral_algebraMap_iff.mp h
  have hrZ : ∀ n : ℕ, ∃ m : ℤ, (m : ℚ) = r n := by
    intro n
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hrint n)
    exact ⟨y, by simpa using hy⟩
  choose m hm using hrZ

  refine ⟨a, ((M : ℂ) ^ a) • g, PowerSeries.mk m, ?_, ?_⟩
  · unfold ModularCurve.IsIntegralQExp
    rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos h1per]
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, map_smul, smul_eq_mul, eq_intCast, ← hrC n,
      ← hm n, eq_ratCast, Rat.cast_intCast]
  · rw [ModularForm.IsGLPos.coe_smul, hg]
