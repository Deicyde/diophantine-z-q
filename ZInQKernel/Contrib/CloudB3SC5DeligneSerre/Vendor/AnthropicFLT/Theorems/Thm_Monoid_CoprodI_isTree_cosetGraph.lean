/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Monoid_CoprodI_isTree_cosetGraph (git blob 8fcd80712f593112ce84ad4e07618b1178942ae4, sha256 87320687b48d204fe927d1a70703aa143ac01b68ae861f1eed4f592c2248a740).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Monoid_CoprodI_isTree_cosetGraph

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
theorem Monoid.CoprodI.isTree_cosetGraph {G : Fin 2 → Type*} [∀ i, Group (G i)] :
    (SimpleGraph.fromRel fun v w : (i : Fin 2) × (Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := i)).range) =>
        v.1 ≠ w.1 ∧ ∃ g : Monoid.CoprodI G,
          v.2 = (QuotientGroup.mk g : Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := v.1)).range) ∧
          w.2 = (QuotientGroup.mk g : Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := w.1)).range)).IsTree := by
  revert G
  exact @_root_.P2MW.S_Monoid_CoprodI_isTree_cosetGraph.solution
