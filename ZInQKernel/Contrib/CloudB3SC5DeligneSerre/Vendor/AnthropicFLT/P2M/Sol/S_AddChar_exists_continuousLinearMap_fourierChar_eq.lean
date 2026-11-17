/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AddChar_exists_continuousLinearMap_fourierChar_eq (git blob 038c1112717f31ec0254b2c10c53fc49eb9a93f7, sha256 be008a410baa5dd69deee303bab615b05eaf8aed2f69d5c9b6f9d63022f8282b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AddChar_exists_continuousLinearMap_fourierChar_eq

set_option autoImplicit false

open scoped FourierTransform
open Real

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : AddChar E Circle) (hχ : Continuous χ) :
    ∃ l : E →L[ℝ] ℝ, ∀ x, χ x = 𝐞 (l x) := by

  obtain ⟨F, ⟨hF0, hFlift⟩, huniq⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts (⟨χ, hχ⟩ : C(E, Circle)) 0 0
      (by simp)
  have hF : ∀ x, Circle.exp (F x) = χ x := fun x => congrFun hFlift x

  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    let G : C(E, ℝ) := ⟨fun z => F (z + y) - F y, by fun_prop⟩
    have hG : G = F := by
      refine huniq G ⟨by simp [G], ?_⟩
      funext z
      simp only [Function.comp_apply, ContinuousMap.coe_mk, G, Circle.exp_sub, hF,
        AddChar.map_add_eq_mul, mul_div_cancel_right]
    have := congrArg (fun (H : C(E, ℝ)) => H x) hG
    simp only [G, ContinuousMap.coe_mk] at this
    linarith

  let Fhom : E →+ ℝ := { toFun := F, map_zero' := hF0, map_add' := hadd }
  let l₀ : E →L[ℝ] ℝ := Fhom.toRealLinearMap F.continuous
  refine ⟨(2 * π)⁻¹ • l₀, fun x => ?_⟩
  rw [Real.fourierChar_apply', ContinuousLinearMap.smul_apply, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by positivity), one_mul]
  exact (hF x).symm
