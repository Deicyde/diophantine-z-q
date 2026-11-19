/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine (git blob 58743b128630552d6ec0a6b838150a70c78cd965, sha256 1a50f8158c1cc9c7ed3a376cc3db2c3ea9c5d05b92623463621d3ddb32c8eb02).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_HeckeCharacter_FiniteOrder
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open IsDedekindDomain NumberField
theorem AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        gen B) Φ) :
    IsIdeleClassChar (𝓞 F) F (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) ∧
      HeckeCharacter.AdmitsModulus F (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) Φ.level ∧
      (IsGenuineCuspRealizationAt F
          (productionPinsOf F D (fun N => NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
            gen B) Φ R →
        Continuous (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom)) := by
  revert F D gen B Φ R
  exact @_root_.P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine.solution
