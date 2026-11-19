/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_ArchSpherical (git blob 8fafb052471ce6189d59b3ee2751ddb17787a598, sha256 1b73dae1a8540b8edee07f2d11a8cb355793b5bfe62d2e56ca5935708511209b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def IsArchSphericalOfType (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) : Prop :=
  IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
    ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x

theorem isArchSphericalOfType_iff (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :
    IsArchSphericalOfType F tys fa ↔
      IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
          fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x := Iff.rfl

theorem isArchSphericalOfType_zero (tys : ArchTypeFamily F) : IsArchSphericalOfType F tys (fun _ => 0) :=
  ⟨isArchTestFactor_zero F, isArchFactorBiFinite_zero F tys, fun _ _ _ => rfl⟩

def IsLevelSphericalOfType (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
    IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
    (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
    ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (AdelicLevel.glArch (𝓞 F) F g) *
      Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)))
        (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F g)

theorem isLevelSphericalOfType_iff (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) :
    IsLevelSphericalOfType F tys U f ↔
      ∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
        IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
          fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
        ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (AdelicLevel.glArch (𝓞 F) F g) *
          Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)))
            (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F g) := Iff.rfl

theorem isLevelSphericalOfType_iff' (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) :
    IsLevelSphericalOfType F tys U f ↔
      ∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchSphericalOfType F tys fa ∧
        ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (AdelicLevel.glArch (𝓞 F) F g) *
          Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)))
            (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F g) :=
  ⟨fun ⟨fa, h1, h2, h3, h4⟩ => ⟨fa, ⟨h1, h2, h3⟩, h4⟩, fun ⟨fa, ⟨h1, h2, h3⟩, h4⟩ => ⟨fa, h1, h2, h3, h4⟩⟩

theorem isLevelSphericalOfType_zero (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F)) :
    IsLevelSphericalOfType F tys U (fun _ => 0) :=
  ⟨fun _ => 0, isArchTestFactor_zero F, isArchFactorBiFinite_zero F tys, fun _ _ _ => rfl,
    fun _ => (zero_mul _).symm⟩

end AutomorphicForm

end
