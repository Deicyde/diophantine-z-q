/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe v u

open CategoryTheory MonoidalCategory

theorem CategoryTheory.MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {M N M' N' : C} (e : M ≅ M') (h : Nonempty (M ⊗ N ≅ 𝟙_ C)) (h' : Nonempty (M' ⊗ N' ≅ 𝟙_ C)) :
    Nonempty (N ≅ N') := by p2m_exact_reverting @_root_.P2MW.S_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit.solution
