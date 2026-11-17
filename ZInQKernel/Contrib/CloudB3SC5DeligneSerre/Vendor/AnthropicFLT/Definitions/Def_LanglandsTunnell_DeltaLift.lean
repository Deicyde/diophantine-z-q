/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_LanglandsTunnell_DeltaLift (git blob f50e7d37418bf5e6d59575a4223fbac4130bc0c5, sha256 9f95bcbc1f2dce0fd85125490b97af38802446b066c5f710a6839ecde4b552cd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArithCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix AutomorphicForm AutomorphicForm.HeckeEigensystem
open scoped ModularForm MatrixGroups

namespace LanglandsTunnell

def deltaArchLift (h : GL (Fin 2) ℝ) : ℂ :=
  ((⇑CuspForm.discriminant) ∣[(12 : ℤ)] h) UpperHalfPlane.I * ((h.det.val : ℝ) : ℂ) ^ (-5 : ℤ)

def ratArchGL2 (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom
    (AdelicLevel.archComponent ℚ default (AdelicLevel.glArch (𝓞 ℚ) ℚ g))

def HasDeltaDecomp (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Prop :=
  ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)),
    u ∈ (productionPinsCompact ℚ).U ⊤ ∧ AdelicLevel.glFin (𝓞 ℚ) ℚ h = 1 ∧
    ratArchGL2 h ∈ GLPos (Fin 2) ℝ ∧ g = globalPoints (𝓞 ℚ) ℚ γ * h * u

open scoped Classical in

def deltaLift (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ℂ :=
  if H : HasDeltaDecomp g then deltaArchLift (ratArchGL2 H.choose_spec.choose) else 0

def deltaRawTable : HeckeEigensystem ℚ ℂ where
  level := ⊤
  level_ne_bot := top_ne_bot
  a := fun v => (UpperHalfPlane.qExpansion 1 (⇑CuspForm.discriminant)).coeff
      (Ideal.absNorm v.asIdeal) * (cNorm v) ^ (-5 : ℤ)
  b := fun _ => 1

def deltaLiftSystem : HeckeEigensystem ℚ ℂ := ofRawCentral deltaRawTable

@[simp] theorem deltaLiftSystem_level : deltaLiftSystem.level = ⊤ := rfl

@[simp] theorem deltaLiftSystem_toRawCentral : deltaLiftSystem.toRawCentral = deltaRawTable :=
  HeckeEigensystem.toRawCentral_ofRawCentral deltaRawTable

end LanglandsTunnell
