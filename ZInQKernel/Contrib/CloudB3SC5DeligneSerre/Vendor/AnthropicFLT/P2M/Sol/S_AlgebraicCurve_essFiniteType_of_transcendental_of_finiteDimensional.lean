/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional (git blob ba4f112461b9ea9ba8d2303eb4a6bdf19b897cc0, sha256 e8c7f637490b562c1b89271b5fe9e7b43ccad4f93b20b6eada21c00df675b926).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional

set_option autoImplicit false

open IntermediateField Polynomial

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K F := by
  haveI := hfd
  let e : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x htr
  haveI : Algebra.EssFiniteType K[X] (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc K) (nonZeroDivisors K[X])
  haveI : Algebra.EssFiniteType K (RatFunc K) := Algebra.EssFiniteType.comp K K[X] (RatFunc K)
  haveI : Algebra.EssFiniteType K ↥K⟮x⟯ := Algebra.EssFiniteType.of_surjective e.toAlgHom e.surjective
  haveI : Algebra.EssFiniteType ↥K⟮x⟯ F := Algebra.EssFiniteType.of_finiteType _ _
  exact Algebra.EssFiniteType.comp K ↥K⟮x⟯ F
