/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_CuspForm_IntegralStructure (git blob 1046f8d98b56d6d0c7f28a110f37274ca47e885e, sha256 9c6077678f419bc6bf2193a680fd59648a03c6b2190f5901d2553c6c48375281).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

def CuspForm.intLattice (N : ℕ) (k : ℤ) : Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) k) :=
  Submodule.span ℤ {f | ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ)}

def CuspForm.HasIntegralStructure (N : ℕ) (k : ℤ) : Prop :=
  Submodule.span ℂ ((CuspForm.intLattice N k : Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) :
    Set (CuspForm (CongruenceSubgroup.Gamma0 N) k)) = ⊤
