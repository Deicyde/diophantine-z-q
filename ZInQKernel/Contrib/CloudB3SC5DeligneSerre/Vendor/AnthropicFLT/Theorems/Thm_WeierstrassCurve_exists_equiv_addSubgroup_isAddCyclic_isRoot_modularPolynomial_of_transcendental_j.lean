/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j (git blob b503f78cec49d39a6ccdb3a5b983893d43879ac7, sha256 8336401bf1222a92c4ffef69085323469da772fb0002506442f45b34cb240506).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve WeierstrassCurve

universe u v in

theorem WeierstrassCurve.exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j
    (K : Type u) [Field K] (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra k Ω]
    (hN : (N : k) ≠ 0) (E : WeierstrassCurve k) [E.IsElliptic] (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // N • P = 0} = N ^ 2) :
    ∃ Θ : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} ≃
        {y : Ω // (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω)
          (algebraMap k Ω E.j))).IsRoot y},
      ∀ (σ : Ω ≃ₐ[k] Ω) (H H' : {H : AddSubgroup (E.baseChange Ω).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}),
        H'.1 = H.1.map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)) →
          ((Θ H').1 : Ω) = σ (Θ H).1 := by
  revert K N data k Ω hN E hE hfull
  exact @_root_.P2MW.S_WeierstrassCurve_exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j.solution
