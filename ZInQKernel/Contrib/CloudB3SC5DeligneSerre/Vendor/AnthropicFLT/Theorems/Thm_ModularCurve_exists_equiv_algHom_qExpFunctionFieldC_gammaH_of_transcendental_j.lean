/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j (git blob 80d2faca3be8dbf97d87b32c25c41add1d87c72f, sha256 db86f837ea54c28a067276a6e8cc273c3a6c6e4a0c0a1b7c97decc849947fb27).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine
open scoped MatrixGroups

universe u v in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (H : Subgroup (ZMod M)ˣ)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) (hx : (x : LaurentSeries K) = jqModC K)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // M • P = 0} = M ^ 2) :
    ∃ Φ : {s : Set (E.baseChange Ω).toAffine.Point // ∃ P : (E.baseChange Ω).toAffine.Point,
            addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} ≃
        {ψ : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] Ω // ψ x = algebraMap k Ω E.j},
      ∀ (σ : Ω ≃ₐ[k] Ω)
        (s s' : {s : Set (E.baseChange Ω).toAffine.Point // ∃ P : (E.baseChange Ω).toAffine.Point,
            addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}}),
        s'.1 = (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)) '' s.1 →
          ((Φ s').1 : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] Ω) =
            ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp (Φ s).1 := by
  revert K M hM H x hx k Ω E hE hfull
  exact @_root_.P2MW.S_ModularCurve_exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j.solution
