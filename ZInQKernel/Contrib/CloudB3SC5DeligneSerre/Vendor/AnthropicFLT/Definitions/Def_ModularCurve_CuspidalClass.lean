/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_ModularCurve_CuspidalClass (git blob 7d9cf43200edbbe1745b1d203e26eed9ebbc2cbe, sha256 c7a7339537b72036a1a034747ad77b4d3996475f249e66b9b5d4c7e0b8e764a2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_AtkinLehner
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_GeometricBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

variable (N : ℕ) [NeZero N]

def frickeInvolutionBar :
    modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N :=
  geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (frickeInvolutionFull N)

theorem frickeInvolutionBar_def :
    frickeInvolutionBar N =
      geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (frickeInvolutionFull N) :=
  rfl

def cuspZeroBar : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  frickeInvolutionBar N • cuspInftyBar N

theorem cuspZeroBar_def : cuspZeroBar N = frickeInvolutionBar N • cuspInftyBar N := rfl

def cuspidalDivisor : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  Finsupp.single (cuspZeroBar N) 1 - Finsupp.single (cuspInftyBar N) 1

theorem cuspidalDivisor_def :
    cuspidalDivisor N = Finsupp.single (cuspZeroBar N) 1 - Finsupp.single (cuspInftyBar N) 1 :=
  rfl

theorem degree_cuspidalDivisor : Divisor.degree (cuspidalDivisor N) = 0 := by
  rw [cuspidalDivisor_def, map_sub, Divisor.degree_single, Divisor.degree_single, cuspZeroBar_def,
    Place.deg_smul, sub_self]

def cuspidalDivisor₀ :
    Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N) :=
  ⟨cuspidalDivisor N, Divisor.mem_degZero.mpr (degree_cuspidalDivisor N)⟩

@[simp]
theorem coe_cuspidalDivisor₀ :
    (cuspidalDivisor₀ N : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) =
      cuspidalDivisor N :=
  rfl

def cuspidalClass : JZero N := Pic0.mk (cuspidalDivisor₀ N)

theorem cuspidalClass_def : cuspidalClass N = Pic0.mk (cuspidalDivisor₀ N) := rfl

end ModularCurve

end
