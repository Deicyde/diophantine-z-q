/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard (git blob 473ce2e4846dd3a2eea4a9c1738f8591156fbd00, sha256 cb89638ea9d30d4d717c2d208c4772e8c12f0db40608097cf6600356934d340c).
Modified for the Z-in-Q kernel (2026-11-16, cluster C5): import paths relocated (modules already
vendored elsewhere in the kernel are imported from there), the upstream lakefile options set as
`set_option` lines, and: dropped import P2M.Util (wrapper commands replaced by ordinary Lean); replaced 1 proof-wrapper tactic call(s) by `revert` + `exact` of the paired Sol proof.
Any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Polynomial
open scoped MatrixGroups

theorem Representation.exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard
    (G : Type) [Group G] [Finite G]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ Nat.card G)
    (k : Type) [Field k] [Finite k] [CharP k ℓ]
    (n m : ℕ) (hm : 0 < m) (hℓm : ¬ ℓ ∣ m) (hGm : ∀ g : G, g ^ m = 1)
    (S : Subalgebra ℤ ℂ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (hζS : ζ ∈ S) (φ : S →+* k)
    (ρbar : G →* GL (Fin n) k) :
    ∃ ρ : G →* GL (Fin n) ℂ, ∀ g : G, ∃ P : Polynomial S,
      P.map (algebraMap S ℂ) = ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly ∧
      P.map φ = ((ρbar g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly := by
  revert G ℓ hℓ k n m hm hℓm hGm S ζ hζ hζS φ ρbar
  exact @_root_.P2MW.S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard.solution
