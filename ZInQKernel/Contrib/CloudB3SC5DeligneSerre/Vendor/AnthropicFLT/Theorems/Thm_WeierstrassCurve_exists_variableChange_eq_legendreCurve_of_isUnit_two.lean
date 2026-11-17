/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_exists_variableChange_eq_legendreCurve_of_isUnit_two (git blob 70da6c5a9b6a494fe864a4b9148cce9012224817, sha256 417c7b704e68ef67aa80ad8661109a1f30161bfcea3eec50753d31e78f3e3ee3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_HasseInvariant
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_variableChange_eq_legendreCurve_of_isUnit_two

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open WeierstrassCurve

universe u in

theorem WeierstrassCurve.exists_variableChange_eq_legendreCurve_of_isUnit_two
    {M : Type u} [Field M] (A : ValuationSubring M) (h2 : IsUnit (2 : A))
    (E : WeierstrassCurve M) [E.IsElliptic] (hj : E.j ∈ A)
    {e₁ e₂ e₃ w : M} (he : E.twoTorsionPolynomial.roots = {e₁, e₂, e₃}) (hw : w ^ 2 = e₂ - e₁) :
    ∃ (l : A) (κ : VariableChange M), IsUnit l ∧ IsUnit (1 - l) ∧
      IsUnit (legendreCurve l).Δ ∧ (l : M) = (e₃ - e₁) / (e₂ - e₁) ∧
      (κ.u : M) = w ∧ κ.r = e₁ ∧ κ.s = -E.a₁ / 2 ∧ κ.t = -(E.a₃ + e₁ * E.a₁) / 2 ∧
      κ • E = (legendreCurve l).map A.subtype := by
  revert M A h2 E hj e₁ e₂ e₃ w he hw
  exact @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_eq_legendreCurve_of_isUnit_two.solution
