/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq

open Polynomial

theorem solution {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] {g : F} (hg : g ∉ Set.range (algebraMap K F)) : ∃ φ : RatFunc K →ₐ[K] F, φ RatFunc.X = g := by

  have htr : Transcendental K g := by
    intro halg
    apply hg
    have hint : IsIntegral K g := halg.isIntegral
    have hdeg : (minpoly K g).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
    obtain ⟨a, ha⟩ := minpoly.degree_eq_one_iff.mp hdeg
    exact ⟨a, ha⟩
  have hinj : Function.Injective (Polynomial.aeval (R := K) g) :=
    transcendental_iff_injective.mp htr
  refine ⟨RatFunc.liftAlgHom (Polynomial.aeval g) ?_, ?_⟩
  · intro p hp
    simp only [Submonoid.mem_comap]
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hp))
  · rw [RatFunc.liftAlgHom_apply]
    simp
