/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalConstituent_isCuspConstituent_productionPinsOf_mono (git blob 44a710f280c3e154660467a1bd1cd61d341a31c3, sha256 8a471e944bf7770555ec9965e1d0fad937415a996c26945dd236929344037a56).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_isCuspConstituent_productionPinsOf_mono

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open _root_.AutomorphicForm
namespace AutomorphicForm
end AutomorphicForm
open _root_.P2MW.S_AutomorphicForm_CuspidalConstituent_isCuspConstituent_productionPinsOf_mono.AutomorphicForm
open _root_.AutomorphicForm.WindowedSiegel
open _root_.AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open _root_.AutomorphicForm.CuspidalConstituent
namespace AutomorphicForm.CuspidalConstituent
end AutomorphicForm.CuspidalConstituent
open _root_.P2MW.S_AutomorphicForm_CuspidalConstituent_isCuspConstituent_productionPinsOf_mono.AutomorphicForm.CuspidalConstituent

namespace AutomorphicForm
export _root_.AutomorphicForm (CarrierPins productionPinsOf AdelicGL2 finiteAdelicGL2Subgroup IsSmoothCuspAutomorphicFnAt lsXiMemberAt_iff)
namespace CuspidalConstituent
export _root_.AutomorphicForm.CuspidalConstituent (cuspKFiniteSubmodule IsCuspSubrep IsCuspConstituent)
namespace C8Mono
open _root_.AutomorphicForm.CuspidalConstituent
open _root_.AutomorphicForm

variable {F : Type} [Field F] [NumberField F]

noncomputable abbrev stdPins (D : Set (AdelicGL2 (𝓞 F) F)) (B : Set (AdeleRing (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) B

theorem isSmoothCuspAutomorphicFnAt_mono {D D' : Set (AdelicGL2 (𝓞 F) F)} (hD : D' ⊆ D)
    (B : Set (AdeleRing (𝓞 F) F)) {ξ : (stdPins D B).Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsSmoothCuspAutomorphicFnAt F (stdPins D B) ξ φ) :
    IsSmoothCuspAutomorphicFnAt F (stdPins D' B) ξ φ := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  obtain ⟨⟨hA, hcusp⟩, hsm⟩ := h
  have hA' := (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) (stdPins D B).Z ξ D φ).mp hA
  refine ⟨⟨(lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) (stdPins D B).Z ξ D' φ).mpr
    ⟨hA'.1, hA'.2.mono_measure (Measure.restrict_mono hD le_rfl)⟩, hcusp⟩, hsm⟩

theorem cuspKFiniteSubmodule_antitone {D D' : Set (AdelicGL2 (𝓞 F) F)} (hD : D' ⊆ D)
    (B : Set (AdeleRing (𝓞 F) F)) (ξ : (stdPins D B).Z →* ℂˣ) :
    cuspKFiniteSubmodule F (stdPins D B) ξ ≤ cuspKFiniteSubmodule F (stdPins D' B) ξ := by
  refine Submodule.span_mono ?_
  rintro φ ⟨hsat, hcont, tys, htys⟩
  exact ⟨fun g => isSmoothCuspAutomorphicFnAt_mono hD B (hsat g), hcont, tys, htys⟩

theorem isCuspSubrep_mono {D D' : Set (AdelicGL2 (𝓞 F) F)} (hD : D' ⊆ D)
    (B : Set (AdeleRing (𝓞 F) F)) {ξ : (stdPins D B).Z →* ℂˣ} {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (h : IsCuspSubrep F (stdPins D B) ξ V) : IsCuspSubrep F (stdPins D' B) ξ V :=
  ⟨h.le.trans (cuspKFiniteSubmodule_antitone hD B ξ), h.rightTranslate_fin_mem, h.rightTranslate_arch_mem,
    h.rightConv_mem⟩

end AutomorphicForm.CuspidalConstituent.C8Mono

open AutomorphicForm.CuspidalConstituent.C8Mono in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (D D' : Set (AdelicGL2 (𝓞 F) F)) (hD : D' ⊆ D) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ V) :
    IsCuspConstituent F (productionPinsOf F D' (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ V := by
  refine ⟨isCuspSubrep_mono hD B hV.1, hV.2.1, fun W hW hWV => hV.2.2 W ?_ hWV⟩
  exact ⟨hWV.trans hV.1.le, hW.rightTranslate_fin_mem, hW.rightTranslate_arch_mem, hW.rightConv_mem⟩
