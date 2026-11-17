/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.Scheme.finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [IsProper t] [GrpObj (Over.mk t)]
    (Z : Set X) (hZ : IsClosed Z) (U : X.Opens) (hU : IsAffineOpen U) (hZU : Zᶜ ⊆ (U : Set X))
    (he : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t).left (IsLocalRing.closedPoint k) ∉ Z) :
    Set.Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t |
      ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
        z.left (IsLocalRing.closedPoint k) ∈ Z ↔ (z * x).left (IsLocalRing.closedPoint k) ∈ Z} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen.solution
