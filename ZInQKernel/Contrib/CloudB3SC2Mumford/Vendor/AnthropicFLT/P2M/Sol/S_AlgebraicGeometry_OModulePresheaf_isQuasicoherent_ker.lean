/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ker
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ker

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

-- [port] was: p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ker.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"
open _root_.AlgebraicGeometry
-- [port] `p2m_open` accepts a namespace before it is declared; it is declared (empty) here first
namespace AlgebraicGeometry
end AlgebraicGeometry
open _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ker.AlgebraicGeometry
open _root_.CategoryTheory
open _root_.TopologicalSpace
open _root_.Opposite

noncomputable section

namespace AlgebraicGeometry
-- [port] was: p2m_export "AlgebraicGeometry" "Spec Scheme OModulePresheaf.ker OModulePresheaf.Hom OModulePresheaf OModulePresheaf.IsQuasicoherent"
export _root_.AlgebraicGeometry (Spec Scheme OModulePresheaf.ker OModulePresheaf.Hom OModulePresheaf OModulePresheaf.IsQuasicoherent)
namespace OModulePresheaf
-- [port] was: p2m_export "AlgebraicGeometry.OModulePresheaf" "ker Hom IsQuasicoherent res res_smul"
export _root_.AlgebraicGeometry.OModulePresheaf (ker Hom IsQuasicoherent res res_smul)
namespace G4T
-- [port] was: p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

universe u

section PModQC
variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G)

theorem isQuasicoherent_ker (hF : OModulePresheaf.IsQuasicoherent F)
    (hG : OModulePresheaf.IsQuasicoherent G) :
    OModulePresheaf.IsQuasicoherent (OModulePresheaf.ker φ) := fun U f => by
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  ·
    obtain ⟨n, y', hy'⟩ := (hF U f).1 x.1
    have h1 : G.res (V.basicOpen_le f) (φ.app U.1 y') = 0 := by
      have hnat := LinearMap.congr_fun (φ.naturality (V.basicOpen_le f)) y'
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hy', φ.app_smul,
        LinearMap.mem_ker.mp x.2, smul_zero] at hnat
      exact hnat.symm
    obtain ⟨m, hm⟩ := (hG U f).2 _ h1
    refine ⟨m + n, ⟨(f ^ m : Γ(V, U.1)) • y',
      LinearMap.mem_ker.mpr ((φ.app_smul U.1 _ _).trans hm)⟩, Subtype.ext ?_⟩
    show F.res (V.basicOpen_le f) ((f ^ m : Γ(V, U.1)) • y')
      = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ (m + n)) • x.1
    rw [F.res_smul, hy', smul_smul, ← map_mul, ← pow_add]
  · exact ((hF U f).2 y.1 (congrArg Subtype.val hy)).imp fun n hn => Subtype.ext hn

end PModQC

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ker.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G) (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) : (OModulePresheaf.ker φ).IsQuasicoherent :=
  AlgebraicGeometry.OModulePresheaf.G4T.isQuasicoherent_ker φ hF hG
