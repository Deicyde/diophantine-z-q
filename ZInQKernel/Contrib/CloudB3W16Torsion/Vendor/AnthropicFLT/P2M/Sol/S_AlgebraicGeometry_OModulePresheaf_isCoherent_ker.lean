/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isCoherent_ker. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_ker

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
open AlgebraicGeometry
-- Source P2M scope referred to a not-yet-declared local namespace; root scope retained.
open CategoryTheory
open TopologicalSpace
open Opposite

noncomputable section

namespace AlgebraicGeometry
export AlgebraicGeometry (IsLocallyNoetherian Spec Scheme IsLocallyNoetherian.component_noetherian IsNoetherian OModulePresheaf.ker OModulePresheaf.kerImSES OModulePresheaf.Hom OModulePresheaf OModulePresheaf.IsCoherent)
namespace OModulePresheaf
export AlgebraicGeometry.OModulePresheaf (ker kerImSES Hom IsCoherent obj)
namespace G4T
open AlgebraicGeometry.OModulePresheaf
open AlgebraicGeometry

universe u

section PModAlg
variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G)
variable [IsLocallyNoetherian V]

theorem isCoherent_ker (hF : OModulePresheaf.IsCoherent F) :
    OModulePresheaf.IsCoherent (OModulePresheaf.ker φ) := fun U => by
  haveI := hF U
  haveI : IsNoetherianRing Γ(V, U.1) := IsLocallyNoetherian.component_noetherian U
  haveI : _root_.IsNoetherian (Γ(V, U.1)) (F.obj U.1) := isNoetherian_of_isNoetherianRing_of_finite _ _
  exact Module.Finite.of_injective ((OModulePresheaf.kerImSES φ).inc.appSections U.1)
    ((OModulePresheaf.kerImSES φ).injective U.1)

end PModAlg

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_ker.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsLocallyNoetherian V] {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G) (hF : F.IsCoherent) : (OModulePresheaf.ker φ).IsCoherent :=
  AlgebraicGeometry.OModulePresheaf.G4T.isCoherent_ker φ hF
