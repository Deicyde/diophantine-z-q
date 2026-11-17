/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_Module_finrank_baseChange_eq_one_of_rankAtStalk_eq_one. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_Module_finrank_baseChange_eq_one_of_rankAtStalk_eq_one

universe u

open TensorProduct

set_option autoImplicit false

theorem solution
    {R : Type u} [CommRing R] (P : Type u) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Flat R P]
    (h : ∀ 𝔭, Module.rankAtStalk (R := R) P 𝔭 = 1)
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K (K ⊗[R] P) = 1 := by
  have hq : Module.rankAtStalk (R := K) (K ⊗[R] P) ⟨⊥, Ideal.isPrime_bot⟩ = 1 := by
    rw [Module.rankAtStalk_baseChange]; exact h _
  rw [Module.rankAtStalk_eq_finrank_tensorProduct] at hq
  haveI : Nontrivial (Localization.AtPrime (⊥ : Ideal K)) := by infer_instance
  rwa [Module.finrank_baseChange] at hq
