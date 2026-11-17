/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Pic0_natCard_torsion_prime_eq_pow_genus (git blob aa1e973fd613e4f426acbd89823430abb277674e, sha256 7a08d3b67b64a53b3dbe83e6371156f446431cb0fb0c1d2c0dca2dcff3648b44).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_natCard_torsion_prime_eq_pow_genus_complex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_genus_eq_of_constantFieldExtension_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_natCard_torsion_eq_of_constantFieldExtension
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_constantFieldDescent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_constantFieldExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Pic0_natCard_torsion_prime_eq_pow_genus

open AlgebraicCurve

theorem solution (K F : Type*) [Field K] [Field F]
    [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (p : ℕ) [Fact p.Prime] :
    Nat.card (Pic0.torsion K F p) = p ^ (2 * genus K F) := by

  obtain ⟨K₀, F₀, _, _, _, _, _, _, _, _, _, _, _, _, _, hfg₀, hgen⟩ :=
    AlgebraicCurve.exists_constantFieldDescent K F hfg
  haveI : CharZero K₀ := (algebraMap K₀ K).charZero

  obtain ⟨Fc, _, _, _, _, _, _, _, _, hfgc, hgenc⟩ :=
    AlgebraicCurve.exists_constantFieldExtension K₀ F₀ ℂ hfg₀
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero

  have h1 := AlgebraicCurve.Pic0.natCard_torsion_eq_of_constantFieldExtension
    K₀ F₀ K F hfg₀ hfg hgen p hp
  have h2 := AlgebraicCurve.genus_eq_of_constantFieldExtension_of_isAlgClosed K₀ F₀ K F hfg₀ hfg hgen

  have h3 := AlgebraicCurve.Pic0.natCard_torsion_eq_of_constantFieldExtension
    K₀ F₀ ℂ Fc hfg₀ hfgc hgenc p hp
  have h4 := AlgebraicCurve.genus_eq_of_constantFieldExtension_of_isAlgClosed K₀ F₀ ℂ Fc hfg₀ hfgc hgenc

  have h5 := AlgebraicCurve.Pic0.natCard_torsion_prime_eq_pow_genus_complex Fc hfgc p
  rw [h1, h2, ← h3, ← h4, h5]
