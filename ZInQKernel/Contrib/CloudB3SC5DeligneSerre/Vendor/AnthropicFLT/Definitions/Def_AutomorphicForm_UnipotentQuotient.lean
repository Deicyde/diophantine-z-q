/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_UnipotentQuotient (git blob b47457f51e06708b7ddb967febfbfe00f23b8b6d, sha256 5cf2ceee6dd7faae61a073f4fbe22f60b5978679242724342081abc3d4d805a4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicLsXi
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K : Type*) [Field K] [NumberField K]

abbrev adelicUnipotent : Subgroup (AdelicGL2 (𝓞 K) K) :=
  (unipotentGL2Hom (R := AdeleRing (𝓞 K) K)).range

abbrev UnipotentQuotient : Type _ :=
  MulAction.orbitRel.Quotient (adelicUnipotent K) (AdelicGL2 (𝓞 K) K)

def toAdelicUnipotent (x : AdeleRing (𝓞 K) K) : adelicUnipotent K :=
  (unipotentGL2Hom (R := AdeleRing (𝓞 K) K)).rangeRestrict (Multiplicative.ofAdd x)

def unipotentHaar : Measure (adelicUnipotent K) :=
  Measure.map (toAdelicUnipotent K)
    (((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K)

def unipotentQuotientMeasure : Measure (UnipotentQuotient K) :=
  HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (adelicUnipotent K) (unipotentHaar K)

end AutomorphicForm

end
