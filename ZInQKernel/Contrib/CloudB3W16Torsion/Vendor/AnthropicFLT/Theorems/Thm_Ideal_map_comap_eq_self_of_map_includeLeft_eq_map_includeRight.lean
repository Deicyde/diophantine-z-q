/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Ideal_map_comap_eq_self_of_map_includeLeft_eq_map_includeRight. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Ideal_map_comap_eq_self_of_map_includeLeft_eq_map_includeRight

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open TensorProduct

theorem Ideal.map_comap_eq_self_of_map_includeLeft_eq_map_includeRight
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (I : Ideal B)
    (hI : I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) =
      I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B)) :
    (I.comap (algebraMap A B)).map (algebraMap A B) = I := by p2m_exact_reverting @_root_.P2MW.S_Ideal_map_comap_eq_self_of_map_includeLeft_eq_map_includeRight.solution
