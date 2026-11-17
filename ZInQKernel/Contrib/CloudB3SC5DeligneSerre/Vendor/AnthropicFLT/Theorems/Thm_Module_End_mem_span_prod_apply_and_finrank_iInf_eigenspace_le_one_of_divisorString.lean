/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Module_End_mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString (git blob 582c7684adcef1e655f4334c904d9b9228c74bd3, sha256 f3304521c2786c676bfc0f2f84c7e019c732bfb5775b05eab3720970cc54ceb0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Module_End_mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem Module.End.mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString
    (D : ℕ) (hD : D ≠ 0)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (e : ℕ → V)
    (hli : LinearIndependent ℂ (fun d : Nat.divisors D => e (d : ℕ)))
    (hspan : Submodule.span ℂ (Set.range fun d : Nat.divisors D => e (d : ℕ)) = ⊤)
    (U : ℕ → Module.End ℂ V)
    (hcomm : ∀ p q : ℕ, p.Prime → q.Prime → p ∣ D → q ∣ D → Commute (U p) (U q))
    (hdown : ∀ q : ℕ, q.Prime → q ∣ D → ∀ d : ℕ, d ∣ D → q ∣ d → U q (e d) = e (d / q))
    (hbase : ∀ q : ℕ, q.Prime → q ∣ D → ∃ a b : ℂ, ∀ d : ℕ, d ∣ D → ¬ q ∣ d →
      U q (e d) = a • e d + b • e (d * q)) :
    (∀ d : ℕ, d ∣ D → ∃ T ∈ Algebra.adjoin ℂ {A : Module.End ℂ V | ∃ q : ℕ, q.Prime ∧ q ∣ D ∧ A = U q},
      e d = T (e D)) ∧
    ∀ lam : ℕ → ℂ,
      Module.finrank ℂ ↥(⨅ q ∈ D.primeFactors, Module.End.eigenspace (U q) (lam q)) ≤ 1 := by
  revert D hD V e hli hspan U hcomm hdown hbase
  exact @_root_.P2MW.S_Module_End_mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString.solution
