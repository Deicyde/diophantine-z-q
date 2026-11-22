/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) :
    (∀ i : ℕ, Fintype.card K.ι ≤ i → IsEmpty (K.Idx i)) ∧
    (∀ i : ℕ, Fintype.card K.ι ≤ i → Subsingleton (F.cochain K i)) ∧
    (∀ i : ℕ, Fintype.card K.ι ≤ i + 1 → Subsingleton (F.HSucc K i)) ∧
    (Nontrivial R →
      (∀ i : ℕ, Fintype.card K.ι ≤ i → F.cechFinrank K i = 0) ∧
      (∀ N : ℕ, Fintype.card K.ι ≤ N →
        F.eulerChar K = ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le.solution
