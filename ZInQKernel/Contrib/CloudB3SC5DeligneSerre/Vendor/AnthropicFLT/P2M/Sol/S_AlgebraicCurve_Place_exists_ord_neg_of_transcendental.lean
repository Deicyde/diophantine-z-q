/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_exists_ord_neg_of_transcendental (git blob 2dd6754065764ba02741bf4f80a5c4a3899d876d, sha256 d50ccc912a78d78f8efd0310ca38699e0422928865516f44f5b8f195996dad08).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.RatFunc.Degree
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_ord_algebraMap_eq_mul_ord

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Place_exists_ord_neg_of_transcendental

set_option autoImplicit false

open AlgebraicCurve
open scoped nonZeroDivisors

theorem solution {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] (x : F) (hx : Transcendental K x) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : ∃ v : Place K F, v.ord x < 0 := by
  classical

  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hφ : (Polynomial K)⁰ ≤ F⁰.comap (Polynomial.aeval x : Polynomial K →ₐ[K] F) := by
    intro p hp
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    rw [mem_nonZeroDivisors_iff_ne_zero] at hp
    exact fun h => hp (hinj (by rw [h, map_zero]))
  set ψ : RatFunc K →ₐ[K] F := RatFunc.liftAlgHom (Polynomial.aeval x) hφ with hψ_def
  have hψX : ψ RatFunc.X = x := by
    rw [hψ_def, RatFunc.liftAlgHom_apply, RatFunc.num_X, RatFunc.denom_X, Polynomial.aeval_X,
      map_one, div_one]
  letI : Algebra (RatFunc K) F := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm

  have hEle : IntermediateField.adjoin K ({x} : Set F) ≤ ψ.fieldRange :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ⟨RatFunc.X, hψX⟩)
  haveI : Module.Finite (RatFunc K) F := by
    obtain ⟨s, hs⟩ := Module.finite_def.mp
      (inferInstance : Module.Finite (IntermediateField.adjoin K ({x} : Set F)) F)
    refine Module.finite_def.mpr ⟨s, ?_⟩
    rw [eq_top_iff]
    rintro f -
    have hf : f ∈ Submodule.span (IntermediateField.adjoin K ({x} : Set F)) (s : Set F) := by
      rw [hs]; trivial
    induction hf using Submodule.span_induction with
    | mem g hg => exact Submodule.subset_span hg
    | zero => exact Submodule.zero_mem _
    | add g h _ _ hg hh => exact Submodule.add_mem _ hg hh
    | smul e g _ hg =>
      obtain ⟨r, hr⟩ := hEle e.2
      have hsm : e • g = r • g := by
        rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        have he' : algebraMap (IntermediateField.adjoin K ({x} : Set F)) F e = (e : F) := rfl
        rw [he', ← hr]
      rw [hsm]
      exact Submodule.smul_mem _ r hg

  haveI : CharZero (RatFunc K) :=
    charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
  haveI : Algebra.IsAlgebraic (RatFunc K) F := Algebra.IsAlgebraic.of_finite (RatFunc K) F
  haveI : Algebra.IsSeparable (RatFunc K) F := Algebra.IsAlgebraic.isSeparable_of_perfectField

  obtain ⟨vinf, hvinf⟩ :=
    AlgebraicCurve.RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum (K := K)
  obtain ⟨w, hw⟩ := AlgebraicCurve.Place.exists_comap_eq_toValuationSubring (F' := F) vinf
  obtain ⟨e, he0, htrans⟩ :=
    AlgebraicCurve.Place.exists_ord_algebraMap_eq_mul_ord w vinf hw.symm
  refine ⟨w, ?_⟩
  have hX := htrans RatFunc.X
  have hordX : vinf.ord RatFunc.X = -1 := by
    rw [AlgebraicCurve.RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
      vinf hvinf RatFunc.X_ne_zero, RatFunc.intDegree_X]
  have hmapX : algebraMap (RatFunc K) F RatFunc.X = x := by
    rw [RingHom.algebraMap_toAlgebra]
    exact hψX
  rw [hmapX, hordX] at hX
  rw [hX, mul_neg_one, Left.neg_neg_iff]
  exact_mod_cast he0
