/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow
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

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

-- [port] was: p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"
open _root_.AlgebraicGeometry
-- [port] `p2m_open` accepts a namespace before it is declared; it is declared (empty) here first
namespace AlgebraicGeometry
end AlgebraicGeometry
open _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow.AlgebraicGeometry
open _root_.CategoryTheory
open _root_.TopologicalSpace
open _root_.Opposite

noncomputable section

namespace AlgebraicGeometry
-- [port] was: p2m_export "AlgebraicGeometry" "Spec Scheme OModulePresheaf.pow OModulePresheaf.Hom OModulePresheaf OModulePresheaf.IsQuasicoherent"
export _root_.AlgebraicGeometry (Spec Scheme OModulePresheaf.pow OModulePresheaf.Hom OModulePresheaf OModulePresheaf.IsQuasicoherent)
namespace OModulePresheaf
-- [port] was: p2m_export "AlgebraicGeometry.OModulePresheaf" "pow Hom IsQuasicoherent res res_smul"
export _root_.AlgebraicGeometry.OModulePresheaf (pow Hom IsQuasicoherent res res_smul)
namespace G4T
-- [port] was: p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

universe u

section PModQC
variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G)

theorem isQuasicoherent_pow {F : OModulePresheaf π} (n : ℕ)
    (hF : OModulePresheaf.IsQuasicoherent F) :
    OModulePresheaf.IsQuasicoherent (OModulePresheaf.pow F n) := fun U f => by
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · choose m y' hy' using fun i => (hF U f).1 (x i)
    refine ⟨∑ i, m i, fun i => (f ^ ((∑ j, m j) - m i) : Γ(V, U.1)) • y' i, funext fun i => ?_⟩
    show F.res _ ((f ^ ((∑ j, m j) - m i) : Γ(V, U.1)) • y' i)
      = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ ∑ j, m j) • x i
    rw [F.res_smul, hy' i, smul_smul, ← map_mul, ← pow_add,
      Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))]
  · choose m hm using fun i => (hF U f).2 (y i) (congrFun hy i)
    refine ⟨∑ i, m i, funext fun i => show (f ^ ∑ j, m j : Γ(V, U.1)) • y i = 0 from ?_⟩
    rw [show (∑ j, m j) = ((∑ j, m j) - m i) + m i from (Nat.sub_add_cancel
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))).symm,
      pow_add, mul_smul, hm i, smul_zero]

end PModQC

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F : OModulePresheaf π} (n : ℕ) (hF : F.IsQuasicoherent) : (F.pow n).IsQuasicoherent :=
  AlgebraicGeometry.OModulePresheaf.G4T.isQuasicoherent_pow n hF
