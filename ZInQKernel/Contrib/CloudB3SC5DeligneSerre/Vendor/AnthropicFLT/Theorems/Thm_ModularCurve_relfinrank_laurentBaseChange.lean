/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange (git blob accf1c17a69153bc3447621a84666390bfdd42e2, sha256 9f031559a4b11d9058f0a2332251298aea6c18dd60f642dd2de16219da798c67).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.FieldTheory.Relrank
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_relfinrank_laurentBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve

theorem ModularCurve.relfinrank_laurentBaseChange (L : Type*) [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (t : LaurentSeries ℚ) (ht : t ∈ F₀) (htr : Transcendental ℚ t) : IntermediateField.relfinrank (IntermediateField.adjoin L ({coeffEmb L t} : Set (LaurentSeries L))) (laurentBaseChange L F₀) = IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({t} : Set (LaurentSeries ℚ))) F₀ := by
  revert L F₀ t ht htr
  exact @_root_.P2MW.S_ModularCurve_relfinrank_laurentBaseChange.solution
