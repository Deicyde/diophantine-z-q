/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v w

theorem Ideal.natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent
    (k : Type u) [Field k] {R : Type v} {C : Type w} [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing C] [IsDomain C] [Algebra k C] [Algebra R C]
    [IsScalarTower k R C] [Algebra.FiniteType R C]
    {d : ℕ} (z : Fin d → C) (hz : AlgebraicIndependent R z) (r : R) (hr : r ≠ 0)
    (hint : ∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c))
    (p : Ideal R) [p.IsMaximal] (hrp : r ∉ p)
    (Q : Ideal C) (hQ : Q ∈ (p.map (algebraMap R C)).minimalPrimes) :
    (d : WithBot ℕ∞) ≤ ringKrullDim (C ⧸ Q) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent.solution
