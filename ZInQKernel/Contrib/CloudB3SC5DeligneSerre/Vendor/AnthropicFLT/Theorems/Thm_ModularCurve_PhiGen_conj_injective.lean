/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_PhiGen_conj_injective (git blob 3fee3adcbed3064dd9dc7bbd21301cae32def631, sha256 76f76e254cd01a799d914b11b8085842925382891c6e150a31aa7270cf8e5088).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_PhiGen_conj_injective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.conj_injective {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) : Function.Injective (conj ℓ ζ (K := K)) := by
  revert K ℓ hℓ ζ hζ
  exact @_root_.P2MW.S_ModularCurve_PhiGen_conj_injective.solution
