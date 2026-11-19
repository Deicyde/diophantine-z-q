/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin (git blob a498f2006f463fb0f552210fa5ff5c139fca2bba, sha256 dc086dd5d585637fd682db2e0ee11074d97710874a98e034e65d569b38e230ba).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_ne_zero
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.RatFunc.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin

set_option autoImplicit false

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) : v.deg ≠ 0 := by
  classical

  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) := transcendental_iff_injective.mp hx
  let lift : RatFunc K →ₐ[K] F :=
    RatFunc.liftAlgHom (Polynomial.aeval x) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)
  have hlift : ∀ p : Polynomial K, lift (algebraMap (Polynomial K) (RatFunc K) p) = Polynomial.aeval x p := fun p => by
    have h := RatFunc.liftAlgHom_apply_div (Polynomial.aeval x)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj) p 1
    rwa [map_one, div_one, map_one, div_one] at h
  letI : Algebra (RatFunc K) F := lift.toRingHom.toAlgebra
  haveI : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq' (lift.comp_algebraMap).symm
  haveI hFD : FiniteDimensional (RatFunc K) F := by
    obtain ⟨s, hs⟩ := Module.finite_def.mp ‹FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F›
    refine ⟨⟨s, ?_⟩⟩
    rw [eq_top_iff]
    rintro z -
    have hz : z ∈ Submodule.span (IntermediateField.adjoin K ({x} : Set F)) (s : Set F) := by
      rw [hs]; trivial
    induction hz using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul c y _ hy =>
        have hrange : IntermediateField.adjoin K ({x} : Set F) ≤ lift.fieldRange := by
          rw [IntermediateField.adjoin_le_iff]
          rintro y' rfl
          exact ⟨algebraMap (Polynomial K) (RatFunc K) Polynomial.X, (hlift _).trans (Polynomial.aeval_X _)⟩
        obtain ⟨c', hc'⟩ := hrange c.2
        have hcc : c • y = c' • y := by
          change (c : F) * y = lift.toRingHom c' * y
          rw [← hc']
        rw [hcc]
        exact Submodule.smul_mem _ c' hy
  have h1 := AlgebraicCurve.RationalFunctionField.deg_ne_zero (v.restrict (RatFunc K))
  have h2 := AlgebraicCurve.Place.inertiaDeg_pos_of_finiteDimensional (F := RatFunc K) v
  rw [← AlgebraicCurve.Place.deg_restrict_mul_inertiaDeg (F := RatFunc K)]
  exact mul_ne_zero h1 h2.ne'
