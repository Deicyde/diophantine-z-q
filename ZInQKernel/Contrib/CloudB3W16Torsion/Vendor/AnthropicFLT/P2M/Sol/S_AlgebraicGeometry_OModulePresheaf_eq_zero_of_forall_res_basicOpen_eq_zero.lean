/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero. Apache-2.0.
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

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero

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
export AlgebraicGeometry (Spec Scheme OModulePresheaf.Hom OModulePresheaf OModulePresheaf.IsQuasicoherent)
namespace OModulePresheaf
export AlgebraicGeometry.OModulePresheaf (Hom IsQuasicoherent res obj)
namespace G4T
open AlgebraicGeometry.OModulePresheaf
open AlgebraicGeometry

universe u

section PModQC
variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G)

theorem eq_zero_of_forall_res_basicOpen_eq_zero {F : OModulePresheaf π} (hF : OModulePresheaf.IsQuasicoherent F)
    (U : V.affineOpens) {ι : Type*} [Fintype ι] (h : ι → Γ(V, U.1))
    (hcov : U.1 ≤ ⨆ j, V.basicOpen (h j)) (x : F.obj U.1)
    (hx : ∀ j, F.res (V.basicOpen_le (h j)) x = 0) : x = 0 := by
  choose n hn using fun j => (hF U (h j)).2 x (hx j)

  have hspan : Ideal.span (Set.range fun j => (h j) ^ (n j + 1)) = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    exact (hcov.trans (iSup_mono fun j =>
        (V.basicOpen_pow (h j) (n j).succ_pos).ge)).trans
      (iSup_le fun j => le_iSup_of_le ⟨_, j, rfl⟩ le_rfl)
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (show (1 : Γ(V, U.1)) ∈ Ideal.span _ from hspan ▸ Submodule.mem_top)
  calc x = (1 : Γ(V, U.1)) • x := (one_smul _ x).symm
    _ = (∑ j, c j * (h j) ^ (n j + 1)) • x := by rw [hc]
    _ = ∑ j, c j • ((h j) ^ (n j + 1) • x) := by
        rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _
    _ = 0 := Finset.sum_eq_zero fun j _ => by
        rw [pow_succ', mul_smul, hn j, smul_zero, smul_zero]

end PModQC

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F : OModulePresheaf π} (hF : F.IsQuasicoherent) (U : V.affineOpens) {ι : Type*} [Fintype ι] (h : ι → Γ(V, U.1)) (hcov : U.1 ≤ ⨆ j, V.basicOpen (h j)) (x : F.obj U.1) (hx : ∀ j, F.res (V.basicOpen_le (h j)) x = 0) : x = 0 :=
  AlgebraicGeometry.OModulePresheaf.G4T.eq_zero_of_forall_res_basicOpen_eq_zero hF U h hcov x hx
