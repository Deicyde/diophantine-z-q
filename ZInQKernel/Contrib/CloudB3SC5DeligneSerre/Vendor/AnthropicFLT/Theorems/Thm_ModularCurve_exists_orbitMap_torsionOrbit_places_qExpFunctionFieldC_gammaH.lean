/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_orbitMap_torsionOrbit_places_qExpFunctionFieldC_gammaH (git blob 5aa4f0fee27e03ccaba146f3f706caf3404b5a08, sha256 d9228956ca31259c092dace0ec57523d50e0695ea422b7b255b36971b0879da8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_orbitMap_torsionOrbit_places_qExpFunctionFieldC_gammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_orbitMap_torsionOrbit_places_qExpFunctionFieldC_gammaH
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (H : Subgroup (ZMod M)ˣ) (j₀ : K) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hE₀ : E₀.j = j₀)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) (hx : (x : LaurentSeries K) = jqModC K)
    (S : Finset (Place K (qExpFunctionFieldC K (CohCarrier.GammaH M H))))
    (hS : ∀ Q, Q ∈ S ↔
      0 < Q.ord (x - algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) j₀)) :
    ∃ f : {s : Set E₀.toAffine.Point // ∃ P : E₀.toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} →
        Place K (qExpFunctionFieldC K (CohCarrier.GammaH M H)),
      (∀ s, f s ∈ S) ∧ (∀ Q ∈ S, ∃ s, f s = Q) ∧
      (∀ s s', f s = f s' ↔ ∃ γ : VariableChange K, γ • E₀ = E₀ ∧
        ∀ T ∈ s.1, ∃ T' ∈ s'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T') ∧
      ∀ s, (f s).ord (x - algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) j₀) =
        (Nat.card {s' : {s : Set E₀.toAffine.Point // ∃ P : E₀.toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} //
          f s' = f s} : ℤ) := by
  revert K M hM H j₀ E₀ hE₀ x hx S hS
  exact @_root_.P2MW.S_ModularCurve_exists_orbitMap_torsionOrbit_places_qExpFunctionFieldC_gammaH.solution
