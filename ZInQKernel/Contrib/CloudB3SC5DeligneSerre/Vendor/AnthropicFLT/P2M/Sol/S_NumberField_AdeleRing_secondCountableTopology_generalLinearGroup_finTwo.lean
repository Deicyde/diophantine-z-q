/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo (git blob fd657514db123331e1b1c0f7e7293a23fd59693b, sha256 b973c786bd82f3959086cef1eed85dcb1218e88c0294e13fdf08d6196aa583b1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.AdeleRing
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdeleRing_secondCountableTopology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo

set_option autoImplicit false

section

open NumberField
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

private scoped instance scAdele_secondCountableGL2 :
    SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 K) K)) := by
  haveI := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

end

theorem solution (K : Type*) [Field K]
    [NumberField K] :
    SecondCountableTopology
      (Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)) :=
  scAdele_secondCountableGL2 K
