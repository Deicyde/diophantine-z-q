/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_isHeckeCosetEigenfunctionAt_weightOneLift (git blob a55372346dbd25f95295c72d5361dbad5758da61, sha256 7142e6eb928a2f0e00ac27e9f5460982f03e081d650733fe65f447327cf1489f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_isHeckeCosetEigenfunctionAt_weightOneLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne
open IsDedekindDomain AutomorphicForm.SmoothCusp
open scoped ModularForm MatrixGroups

theorem LanglandsTunnell.isHeckeCosetEigenfunctionAt_weightOneLift
    {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (Φ : HeckeEigensystem ℚ ℂ) (hΦ : Φ.level = Ideal.span {(n : 𝓞 ℚ)})
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)})
    (hT : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ModularForm.heckeU 1 (Ideal.absNorm v.asIdeal) f
          + χ ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) •
              (f ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix (Ideal.absNorm v.asIdeal))
        = Φ.a v • f) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      IsHeckeCosetEigenfunctionAt ℚ ((productionPinsCompact ℚ).U Φ.level)
        ((productionPinsCompact ℚ).gen v) v (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) (Φ.a v) := by
  revert n hn f hf χ hχ Φ hΦ S hS hT
  exact @_root_.P2MW.S_LanglandsTunnell_isHeckeCosetEigenfunctionAt_weightOneLift.solution
