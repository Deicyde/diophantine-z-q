/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_exists_D_ne_zero (git blob d48f30cb62f82f450df14b6987097bcf53059d57, sha256 a8126af2a6c26d5596f502bb380e8a1a1a9674461d6b697ab4d92b7bfa8ff3ba).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_exists_D_ne_zero

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] : ∃ t : F, KaehlerDifferential.D K F t ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
  have hmem : ω ∈ Submodule.span F (Set.range (KaehlerDifferential.D K F)) := by
    rw [KaehlerDifferential.span_range_derivation]
    exact Submodule.mem_top
  have hbot : Submodule.span F (Set.range (KaehlerDifferential.D K F)) = ⊥ :=
    Submodule.span_eq_bot.2 (by rintro _ ⟨t, rfl⟩; exact h t)
  rw [hbot, Submodule.mem_bot] at hmem
  exact hω hmem
