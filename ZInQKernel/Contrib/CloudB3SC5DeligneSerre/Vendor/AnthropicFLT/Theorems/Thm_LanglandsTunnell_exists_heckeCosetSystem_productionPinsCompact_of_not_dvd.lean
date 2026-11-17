/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_exists_heckeCosetSystem_productionPinsCompact_of_not_dvd (git blob 13467890a1f80a8792990a30e73667cf9beaa2d1, sha256 5d94603850ac53c446d48e82550077f4759422f698981f717d9978d23033a22b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalLanglands_HeckeCosetSystem
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_exists_heckeCosetSystem_productionPinsCompact_of_not_dvd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
theorem LanglandsTunnell.exists_heckeCosetSystem_productionPinsCompact_of_not_dvd
    (N : Ideal (𝓞 ℚ)) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ v.asIdeal ∣ N) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 ℚ) ℚ,
      HeckeIntegralSeam.IsHeckeCosetSystem ((productionPinsCompact ℚ).U N)
        ((productionPinsCompact ℚ).gen v) reps := by
  revert N v hv
  exact @_root_.P2MW.S_LanglandsTunnell_exists_heckeCosetSystem_productionPinsCompact_of_not_dvd.solution
