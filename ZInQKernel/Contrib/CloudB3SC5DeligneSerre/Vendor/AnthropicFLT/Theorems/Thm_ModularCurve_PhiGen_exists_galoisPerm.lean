/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_PhiGen_exists_galoisPerm (git blob 74fa07a01f9005342c85938da0e67bdd07a6700b, sha256 3439506626cae8f76dfdf997d18c3375e4cb0c527e7c354e1a81ca9ab6cce4fb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_PhiGen_exists_galoisPerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.exists_galoisPerm {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ) (σ : K →+* K) : ∃ e : Fin ℓ ≃ Fin ℓ, ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e b : Fin ℓ) : ℕ) := by
  revert K ℓ hℓ ζ hζ σ
  exact @_root_.P2MW.S_ModularCurve_PhiGen_exists_galoisPerm.solution
