/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent (git blob fa77dea3ea92d9a8c3499dc4f812440c4fc1ebf7, sha256 48c36f5ed7e693663109c6671e0f91560611b89f3ac8abb0a3913553ee8d7d7a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent

set_option autoImplicit false

open ModularCurve

theorem solution
    (κ : Type*) [Field κ] (k : Type*) [Field k] [Algebra κ k]
    {n : ℕ} (f : Fin n → LaurentSeries κ) (hf : LinearIndependent κ f) :
    LinearIndependent k (⇑(coeffMap (algebraMap κ k)) ∘ f) := by
  classical
  set g : κ →+* k := algebraMap κ k with hg
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro c hc i₀

  let B := Module.Basis.ofVectorSpace κ k

  have hcomb : ∀ j, ∑ i, (B.repr (c i) j) • f i = 0 := by
    intro j
    ext m

    have hm : ∑ i, ((f i).coeff m) • c i = 0 := by
      have h0 := congrArg (fun x : LaurentSeries k => x.coeff m) hc
      simp only [HahnSeries.coeff_zero, HahnSeries.coeff_sum, Function.comp_apply, HahnSeries.coeff_smul, coeffMap_coeff,
        smul_eq_mul] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, mul_comm]

    have hj := congrArg (fun x : k => B.repr x j) hm
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hj
    rw [HahnSeries.coeff_sum, HahnSeries.coeff_zero]
    simp only [HahnSeries.coeff_smul, smul_eq_mul]
    rw [← hj]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hzero : ∀ j, B.repr (c i₀) j = 0 := fun j => hf _ (hcomb j) i₀
  have hrepr : B.repr (c i₀) = 0 := Finsupp.ext hzero
  simpa using congrArg B.repr.symm hrepr

#print axioms solution
