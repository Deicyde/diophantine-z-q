/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq (git blob 8325a11a236f38c2e99f55be79620735e178170e, sha256 85f0706fff8b68c1a63b820837ec117215428a987779ffe27c7ffd93378cbc64).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open WeierstrassCurve

theorem WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq
    {k Ω : Type*} [Field k] [Field Ω] [DecidableEq Ω] [Algebra k Ω] (E : WeierstrassCurve k)
    [E.IsElliptic] (N : ℕ) [NeZero N] (hN : (N : k) ≠ 0)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // N • P = 0} = N ^ 2) :
    Nonempty (ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point N) := by
  revert k Ω E N hN hfull
  exact @_root_.P2MW.S_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq.solution
