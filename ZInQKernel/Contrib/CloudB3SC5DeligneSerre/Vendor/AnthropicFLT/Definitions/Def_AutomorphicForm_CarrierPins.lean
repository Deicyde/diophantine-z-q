/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_CarrierPins (git blob 0656de05b65efecc6fc653aa8a0ce5c06c24e7eb, sha256 b4825a56492e333a3f5b1c0204c126cbd4e3c96cc3b5dc1f0d94f22b050e874c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicHaar MeasureTheory

noncomputable section

namespace AutomorphicForm

structure CarrierPins (F : Type*) [Field F] [NumberField F] where
  mS : MeasurableSpace (AdelicGL2 (𝓞 F) F)
  μ : @Measure (AdelicGL2 (𝓞 F) F) mS
  D : Set (AdelicGL2 (𝓞 F) F)
  Z : Subgroup (AdeleRing (𝓞 F) F)ˣ
  U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)
  gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F
  nS : MeasurableSpace (AdeleRing (𝓞 F) F)
  ν : @Measure (AdeleRing (𝓞 F) F) nS

def productionPinsOf (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) :
    CarrierPins F where
  mS := glBorel (Fin 2) (𝓞 F) F
  μ := adelicGLHaar (Fin 2) (𝓞 F) F
  D := D
  Z := ⊤
  U := U
  gen := gen
  nS := adeleBorel (𝓞 F) F
  ν := @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) B

theorem productionPinsOf_mS (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).mS = glBorel (Fin 2) (𝓞 F) F := rfl

theorem productionPinsOf_μ (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).μ = adelicGLHaar (Fin 2) (𝓞 F) F := rfl

theorem productionPinsOf_Z (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).Z = ⊤ := rfl

theorem productionPinsOf_nS (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).nS = adeleBorel (𝓞 F) F := rfl

theorem productionPinsOf_D (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).D = D := rfl

theorem productionPinsOf_U (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).U = U := rfl

theorem productionPinsOf_gen (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).gen = gen := rfl

theorem productionPinsOf_ν (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).ν
      = @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) B := rfl

theorem isHaarMeasure_productionPinsOf_μ (F : Type) [Field F] [NumberField F] (D U gen B) :
    @Measure.IsHaarMeasure _ _ _ (productionPinsOf F D U gen B).mS
      (productionPinsOf F D U gen B).μ :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

theorem isProbabilityMeasure_productionPinsOf_ν (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (hB0 : adelicAddHaar (𝓞 F) F B ≠ 0) (hBtop : adelicAddHaar (𝓞 F) F B ≠ ⊤) :
    @IsProbabilityMeasure _ (productionPinsOf F D U gen B).nS
      (productionPinsOf F D U gen B).ν := by
  letI := adeleBorel (𝓞 F) F
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite hB0 hBtop

end AutomorphicForm

end
