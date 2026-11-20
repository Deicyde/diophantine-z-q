/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_of_isQuasicoherent. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.LinearAlgebra.Quotient.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_of_isQuasicoherent

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsAffine V] [IsSeparated π]
    (F : OModulePresheaf π) (hF : F.IsQuasicoherent) (K : V.OrderedAffineCover) (i : ℕ) :
    Subsingleton (F.HSucc K i) := by
  have h := AlgebraicGeometry.OModulePresheaf.ker_d_succ_le_range_d_of_isQuasicoherent F hF K i
  refine subsingleton_of_forall_eq 0 (fun y => ?_)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
  exact h x.2
