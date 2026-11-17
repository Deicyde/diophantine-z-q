/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Subgroup_exists_exact_fundamental_domain_of_secondCountableTopology (git blob f5f9e02f972b34eb66717dba701cc282a19c40ef, sha256 0486f8973944571e45718554b79bd5e9186e23a76d27d7ed7e0c8190781d2faa).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Topology.Algebra.Group.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Subgroup_exists_exact_fundamental_domain_of_secondCountableTopology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem Subgroup.exists_exact_fundamental_domain_of_secondCountableTopology
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    (Γ : Subgroup G) (hdisc : ∃ V : Set G, IsOpen V ∧ V ∩ (Γ : Set G) = {1}) :
    ∃ F : Set G,
      (∃ U C : ℕ → Set G, (∀ n, IsOpen (U n)) ∧ (∀ n, IsOpen (C n)) ∧ F = ⋃ n, U n \ C n) ∧
      ∀ x : G, ∃! γ : ↥Γ, (γ : G) * x ∈ F := by
  revert G Γ hdisc
  exact @_root_.P2MW.S_Subgroup_exists_exact_fundamental_domain_of_secondCountableTopology.solution
