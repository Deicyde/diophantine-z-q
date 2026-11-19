/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient (git blob 8445eacc3ed8d3908fad27ab1477e371b92a95e5, sha256 54bc7bf91e5902d468b0d55c99bfa59e837a59c30c39cebf9c5408589a443c8c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K : Type*) [Field K] [NumberField K]

abbrev rationalDiagOne : Subgroup (AdelicGL2 (𝓞 K) K) :=
  ((globalPoints (𝓞 K) K).comp (diagOne (A := K))).range

abbrev rationalTorus : Subgroup (AdelicGL2 (𝓞 K) K) :=
  rationalCentre K ⊔ rationalDiagOne K

abbrev rationalTorusUnipotent : Subgroup (AdelicGL2 (𝓞 K) K) :=
  rationalTorus K ⊔ adelicUnipotent K

abbrev RationalTorusUnipotentQuotient : Type _ :=
  MulAction.orbitRel.Quotient (rationalTorusUnipotent K) (AdelicGL2 (𝓞 K) K)

def rationalTorusUnipotentHaar : Measure (rationalTorusUnipotent K) :=
  Measure.sum fun za : Kˣ × Kˣ =>
    Measure.map
      (fun n : adelicUnipotent K =>
        (⟨globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom za.1)
            * globalPoints (𝓞 K) K (diagOne za.2) * (n : AdelicGL2 (𝓞 K) K),
          Subgroup.mul_mem_sup
            (Subgroup.mul_mem_sup ⟨za.1, rfl⟩ ⟨za.2, rfl⟩) n.2⟩ : rationalTorusUnipotent K))
      (unipotentHaar K)

def rationalTorusUnipotentQuotientMeasure : Measure (RationalTorusUnipotentQuotient K) :=
  HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalTorusUnipotent K)
    (rationalTorusUnipotentHaar K)

end AutomorphicForm

end
