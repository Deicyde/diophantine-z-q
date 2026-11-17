/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_DihedralWeightOneLift (git blob 771e37bc4926e36f9f920e3ecbffa72ebf4808d2, sha256 b1b3a0f54c5ac9fcccf126864d6df223cb263efa6af55ca1a09ed0bcbc0c496b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_DeltaLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix AutomorphicForm
open scoped ModularForm MatrixGroups

namespace DihedralWeightOne

def weightOneArchLift (f : UpperHalfPlane → ℂ) (h : GL (Fin 2) ℝ) : ℂ :=
  (f ∣[(1 : ℤ)] h) UpperHalfPlane.I * ((h.det.val : ℝ) : ℂ) ^ (1 : ℤ)

def HasWeightOneDecomp (N : Ideal (𝓞 ℚ)) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Prop :=
  ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)),
    u ∈ (productionPinsCompact ℚ).U N ∧ AdelicLevel.glFin (𝓞 ℚ) ℚ h = 1 ∧
    LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ ∧
    g = AutomorphicForm.globalPoints (𝓞 ℚ) ℚ γ * h * u

open scoped Classical in

def weightOneLift (N : Ideal (𝓞 ℚ)) (f : UpperHalfPlane → ℂ)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ℂ :=
  if H : HasWeightOneDecomp N g then
    weightOneArchLift f (LanglandsTunnell.ratArchGL2 H.choose_spec.choose) else 0

end DihedralWeightOne

end
