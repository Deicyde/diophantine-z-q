/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul (git blob bf756f888e603d1115015dba2f89a777a26ce6e7, sha256 4862ae3b600401da1bfec4f5fff947486b669a48a0a80e472171260301dd29ce).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
    {K : Type*} [Field K] [IsAlgClosed K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {T : Type*} [CommRing T] [Module T V] [SMulCommClass T K V] [FaithfulSMul T V]
    {𝔭 : Ideal T} (h𝔭 : 𝔭 ∈ minimalPrimes T) :
    ∃ χ : T →+* K, RingHom.ker χ = 𝔭 ∧
      ∃ x : V, x ≠ 0 ∧ (∀ p ∈ 𝔭, p • x = 0) ∧ (∀ r : T, r • x = 0 → r ∈ 𝔭) ∧
        ∀ t : T, t • x = χ t • x := by
  revert K V T 𝔭 h𝔭
  exact @_root_.P2MW.S_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul.solution
