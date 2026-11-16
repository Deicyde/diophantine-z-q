/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v w

theorem MvPolynomial.exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure
    {R : Type u} [CommRing R] [IsDomain R] {σ : Type v} [Finite σ] (F : MvPolynomial σ R)
    (hF : Irreducible (MvPolynomial.map (algebraMap R (AlgebraicClosure (FractionRing R))) F)) :
    ∃ c : R, c ≠ 0 ∧ ∀ (E : Type w) [Field E] (φ : R →+* E), φ c ≠ 0 →
      Irreducible (MvPolynomial.map φ F) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.solution
