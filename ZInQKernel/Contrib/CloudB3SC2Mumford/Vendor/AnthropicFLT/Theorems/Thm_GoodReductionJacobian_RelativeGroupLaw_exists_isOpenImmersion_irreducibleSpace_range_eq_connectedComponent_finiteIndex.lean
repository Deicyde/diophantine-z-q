/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f) :
    ∃ (G₀ : Scheme.{u}) (i : G₀ ⟶ G) (L₀ : RelativeGroupLaw k (i ≫ f)),
      IsOpenImmersion i ∧ IsClosedImmersion i ∧ IrreducibleSpace G₀ ∧
      Set.range i =
        connectedComponent ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (L₀.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      (L.IsCommutative → L₀.IsCommutative) ∧
      ∃ S : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f), S.Finite ∧
        ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
          ∃ s ∈ S, ∃ a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f),
            x = L.mul (𝟙 (Spec (CommRingCat.of k))) s
              (NeronModelInfra.schemeHomOverComp a (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex.solution
