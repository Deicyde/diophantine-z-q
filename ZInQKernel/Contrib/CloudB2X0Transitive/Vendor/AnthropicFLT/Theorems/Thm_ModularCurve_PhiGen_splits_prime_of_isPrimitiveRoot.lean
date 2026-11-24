/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.splits_prime_of_isPrimitiveRoot {K : Type*} [Field K] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (qExpand K p (jqModC K))) = (Polynomial.X - Polynomial.C (qExpand K (p * p) (jqModC K))) * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.solution
