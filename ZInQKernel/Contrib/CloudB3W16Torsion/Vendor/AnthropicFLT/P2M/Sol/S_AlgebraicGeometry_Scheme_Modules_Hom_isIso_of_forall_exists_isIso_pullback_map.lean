/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
-- Source P2M scope referred to a not-yet-declared local namespace; root scope retained.
open Opposite
open TopologicalSpace

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Modules.pullback Scheme.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Modules Scheme.Opens Scheme.Opens.opensRange_ι)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Modules.pullback Hom Hom.image_preimage_eq_opensRange_inf restrictFunctor Modules Opens Opens.opensRange_ι)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (pullback Hom restrictFunctor restrictFunctorIsoPullback Hom.isIso_iff_isIso_app Hom.isIso_of_isIso_app_of_iSup_eq_top)
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme
open AlgebraicGeometry

variable {X : Scheme.{u}}

lemma restrictFunctor_map_app' {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (W : (U : Scheme.{u}).Opens) :
    ((restrictFunctor U.ι).map φ).app W = φ.app (U.ι ''ᵁ W) := rfl

lemma isIso_app_of_isIso_pullback_ι_map {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (hU : IsIso ((Scheme.Modules.pullback U.ι).map φ)) (W : X.Opens) (hWU : W ≤ U) :
    IsIso (φ.app W) := by
  have h1 : IsIso ((restrictFunctor U.ι).map φ) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback U.ι) φ).2 hU
  have h2 := Hom.isIso_iff_isIso_app.1 h1 (U.ι ⁻¹ᵁ W)
  rw [restrictFunctor_map_app'] at h2
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.2 hWU]
  rw [← e]
  exact h2

theorem _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map.solution {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIso ((Scheme.Modules.pullback U.ι).map φ)) :
    IsIso φ := by
  choose U hxU hU using h
  refine Hom.isIso_of_isIso_app_of_iSup_eq_top φ U ?_ (fun x V hV => ?_)
  · exact top_le_iff.mp fun x _ => Opens.mem_iSup.2 ⟨x, hxU x⟩
  · exact isIso_app_of_isIso_pullback_ι_map φ (U x) (hU x) V hV

#print axioms solution

end AlgebraicGeometry.Scheme.Modules
