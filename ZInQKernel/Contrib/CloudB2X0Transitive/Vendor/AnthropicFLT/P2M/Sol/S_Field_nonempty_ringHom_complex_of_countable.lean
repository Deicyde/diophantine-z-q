/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Field_nonempty_ringHom_complex_of_countable
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_Field_nonempty_ringHom_complex_of_countable

open Cardinal

universe u

theorem solution
    (K : Type u) [Field K] [CharZero K] [Countable K] : Nonempty (K →+* ℂ) := by
  classical
  haveI : FaithfulSMul ℚ K :=
    (faithfulSMul_iff_algebraMap_injective ℚ K).2 (algebraMap ℚ K).injective
  haveI : FaithfulSMul ℚ ℂ :=
    (faithfulSMul_iff_algebraMap_injective ℚ ℂ).2 (algebraMap ℚ ℂ).injective

  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ

  have hct : #ℂ = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' (R := ℚ) _ ht
      mk_le_aleph0 (by rw [mk_complex]; exact aleph0_lt_continuum)

  have h1 : Cardinal.lift.{0} #s ≤ Cardinal.lift.{u} #t := by
    rw [← hct, mk_complex, lift_continuum]
    calc Cardinal.lift.{0} #s ≤ Cardinal.lift.{0} ℵ₀ := lift_le.2 mk_le_aleph0
      _ = ℵ₀ := lift_aleph0
      _ ≤ 𝔠 := aleph0_le_continuum
  obtain ⟨e⟩ := Cardinal.lift_mk_le'.1 h1

  have hind : AlgebraicIndependent ℚ (fun i : s => ((e i : t) : ℂ)) :=
    ht.1.comp e e.injective
  set A := Algebra.adjoin ℚ (Set.range ((↑) : s → K)) with hA
  let g : A →ₐ[ℚ] ℂ :=
    (MvPolynomial.aeval (fun i : s => ((e i : t) : ℂ))).comp hs.1.aevalEquiv.symm.toAlgHom
  have hg : Function.Injective g :=
    (algebraicIndependent_iff_injective_aeval.1 hind).comp hs.1.aevalEquiv.symm.injective

  haveI : Algebra.IsAlgebraic A K := hs.isAlgebraic
  letI : Algebra A ℂ := g.toRingHom.toAlgebra
  haveI : Module.IsTorsionFree A ℂ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hg
  haveI : Module.IsTorsionFree A K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Subtype.val_injective
  exact ⟨(IsAlgClosed.lift (R := A) (S := K) (M := ℂ)).toRingHom⟩
