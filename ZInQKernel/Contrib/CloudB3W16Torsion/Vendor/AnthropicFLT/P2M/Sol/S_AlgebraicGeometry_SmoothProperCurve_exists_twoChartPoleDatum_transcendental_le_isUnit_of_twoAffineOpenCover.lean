/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_exists_twoChartPoleDatum_transcendental_le_isUnit_of_twoAffineOpenCover. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_forall_le_exists_section_invModule_disjoint_of_twoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_twoChartPoleDatum_of_section_invModule
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_twoChartPoleDatum_transcendental_le_isUnit_of_twoAffineOpenCover

universe u

open scoped TensorProduct
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve hiding specMap
open NeronModelInfra
open CategoryTheory.MonoidalCategory

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (𝒱 : C.TwoAffineOpenCover) (m₀ : ℕ) :
    ∃ (U V : C.Opens) (_ : U ⊔ V = ⊤)
      (_ : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
      (f : Γ(C, U)) (g : Γ(C, V))
      (_ : U ⊓ V = C.basicOpen f) (_ : U ⊓ V = C.basicOpen g)
      (_ : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
        (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
      (m : ℕ),
      m₀ ≤ m ∧ IsUnit (m : R) ∧
      (letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
        Module.Free R (Γ(C, V) ⧸ Ideal.span {g}) ∧ Module.finrank R (Γ(C, V) ⧸ Ideal.span {g}) = m) ∧
      (∀ (K : Type u) [Field K] [Algebra R K],
        letI := Scheme.TwoAffineOpenCover.algebraOfHom
          (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
          ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ U);
        Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app U).hom f)) ∧
      (∀ (K : Type u) [Field K] [Algebra R K],
        letI := Scheme.TwoAffineOpenCover.algebraOfHom
          (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
          ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ V);
        Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app V).hom g)) := by
  classical
  obtain ⟨m₁, hL⟩ :=
    AlgebraicGeometry.SmoothProperCurve.exists_forall_le_exists_section_invModule_disjoint_of_twoAffineOpenCover
      R c ε 𝒱

  let k := IsLocalRing.ResidueField R
  let p := ringChar k
  haveI : CharP k p := ringChar.charP k
  let N := max m₀ (max m₁ 1)
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨m, hNm, hmk⟩ : ∃ m : ℕ, N ≤ m ∧ (m : k) ≠ 0 := by
    rcases CharP.char_is_prime_or_zero k p with hp | hp
    · refine ⟨N * p + 1, ?_, ?_⟩
      · have : 1 ≤ p := hp.one_lt.le
        calc N = N * 1 := (mul_one N).symm
          _ ≤ N * p := Nat.mul_le_mul_left N this
          _ ≤ N * p + 1 := Nat.le_succ _
      · rw [Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero k p, mul_zero, zero_add, Nat.cast_one]
        exact one_ne_zero
    · haveI : CharZero k := by
        haveI : CharP k 0 := hp ▸ (ringChar.charP k)
        exact CharP.charP_to_charZero k
      exact ⟨N, le_rfl, by exact_mod_cast (show N ≠ 0 by omega)⟩
  have hm₀ : m₀ ≤ m := le_trans (le_max_left _ _) hNm
  have hm₁ : m₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hNm
  have hm1 : 1 ≤ m := le_trans hN1 hNm
  have hunit : IsUnit (m : R) := by
    by_contra h
    apply hmk
    have hmem : (m : R) ∈ IsLocalRing.maximalIdeal R := h
    have := (IsLocalRing.residue_eq_zero_iff (m : R)).mpr hmem
    rwa [map_natCast] at this
  obtain ⟨s, hs⟩ := hL m hm₁
  obtain ⟨U, V, hcov, hUε, f, g, hf, hg, hfg, hfree, hTf, hTg⟩ :=
    AlgebraicGeometry.SmoothProperCurve.exists_twoChartPoleDatum_of_section_invModule R c ε m hm1 s hs
  exact ⟨U, V, hcov, hUε, f, g, hf, hg, hfg, m, hm₀, hunit, hfree, hTf, hTg⟩
