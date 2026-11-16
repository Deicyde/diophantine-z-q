/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy (AI-assisted)
-/
import ZInQKernel.Contrib.CloudB3W11AxCompletion.GaloisAction
import ZInQKernel.Contrib.CloudB3W11AxEstimate.AxApprox

/-!
# Unconditional Ax–Sen–Tate closure for arbitrary intermediate fields

The arithmetic estimate is the genuine, kernel-compiled theorem
`CloudB3W11AxEstimate.uniform_ax_approximation`, with degree-independent
constant `p²`. It is a port of the Apache-2.0 Ax proof recovered from
anthropics/fermats-last-theorem@6e837e75; its source attribution and proof are
in `AxApprox.lean`.

This file fills the previously explicit estimate interface and reuses the
already proved isometric completion bridge. It does not duplicate the public
81-line completion proof. The public root fixed/closure API has its exact
arbitrary-`K` type, with no finite-dimensional or arithmetic assumptions.
Final OneProof closing wrappers and discharge/review checks remain separate.
-/

namespace ZInQ.Contrib.CloudB3W11AxCompletion

open ZInQ.Contrib.G9.PkgI4

variable (p : ℕ) [Fact p.Prime]

/-- The formerly missing uniform arithmetic input is now proved with `p²`,
independently of `K` and of the degree of every algebraic approximant. -/
theorem uniformAxApproximation_proved (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    UniformAxApproximation p K ((p : ℝ) ^ 2) := by
  intro a δ hδ h
  exact ZInQ.Contrib.CloudB3W11AxEstimate.uniform_ax_approximation p K a δ hδ h

/-- Completed `G_K`-fixed points are exactly the closure of the actual image
of arbitrary `K`; the uniform Ax estimate is proved, not a hypothesis. -/
theorem cpAct_fixed_iff_mem_closure (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (x : ℂ_[p]) :
    (∀ σ ∈ K.fixingSubgroup, cpAct p σ x = x) ↔
      x ∈ closure (Set.range (fun y : K => (((y : PadicAlgCl p)) : ℂ_[p]))) := by
  exact fixed_iff_mem_closure_of_uniformAxApproximation p K (sq_nonneg (p : ℝ))
    (uniformAxApproximation_proved p K) x

end ZInQ.Contrib.CloudB3W11AxCompletion

/-- **Ax–Sen–Tate, arbitrary-intermediate-field closure form.** The action is
the canonical Mathlib completion action, proved equal to the repository's
`cpAct`. This retains the exact public root API needed by the Tate trace port. -/
theorem PadicComplex.forall_smul_eq_self_iff_mem_closure
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (x : ℂ_[p]) :
    (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup → σ • x = x) ↔
      x ∈ closure (Set.range fun k : K => ((k : PadicAlgCl p) : ℂ_[p])) := by
  exact (ZInQ.Contrib.CloudB3W11AxCompletion.fixed_galois_smul_iff_cpAct p K x).trans
    (ZInQ.Contrib.CloudB3W11AxCompletion.cpAct_fixed_iff_mem_closure p K x)
