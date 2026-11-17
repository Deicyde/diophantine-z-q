/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_genus_riemannIndex_of_isCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq

set_option autoImplicit false

universe u v

open AlgebraicCurve

theorem solution
    {K : Type u} {F : Type v} [Field K] [PerfectField K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] (hC : ConstantsAreBase K F)
    {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g) :
    g = genusFF K F := by
  obtain ⟨γ, hγ⟩ := exists_genus_riemannIndex_of_isCurveOver (K := K) (F := F) hC

  have star : ∀ D : Divisor K F, (indexOfSpecialty D : ℤ) = γ - g + ell (Kc - D) := by
    intro D
    have h1 := (hγ D).2
    have h2 := hRR D
    linarith
  obtain ⟨⟨Q⟩, hfin, γ₀, D₀, hreach⟩ := stichtenothGenusExists_of_isCurveOver (K := K) (F := F) hC
  haveI : Nonempty (Place K F) := ⟨Q⟩
  haveI : FiniteDimensional K (LSpace (0 : Divisor K F)) := hfin

  obtain ⟨n, hn⟩ := exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached hreach Q
  have hle : γ ≤ g := by
    have h := star ((n : ℤ) • Finsupp.single Q 1)
    rw [hn] at h
    have h' : (0 : ℤ) ≤ ell (Kc - (n : ℤ) • Finsupp.single Q 1) := Int.natCast_nonneg _
    push_cast at h
    linarith

  haveI : Module.Finite K Q.ResidueField := IsCurveOver.finiteResidue Q
  have hdeg : 0 < (Q.deg : ℤ) := by
    have : 0 < Module.finrank K Q.ResidueField := Module.finrank_pos
    exact_mod_cast this
  have hvan : ell (Kc - (Kc + Finsupp.single Q 1)) = 0 := by
    apply ell_eq_zero_of_degree_neg
    rw [sub_add_cancel_left, map_neg, Divisor.degree_single]
    linarith
  have hge : (g : ℤ) ≤ γ := by
    have h := star (Kc + Finsupp.single Q 1)
    rw [hvan] at h
    have h' : (0 : ℤ) ≤ indexOfSpecialty (Kc + Finsupp.single Q 1) := Int.natCast_nonneg _
    push_cast at h
    linarith
  have hγg : γ = g := le_antisymm hle hge

  have hi0 : (indexOfSpecialty (0 : Divisor K F) : ℤ) = γ := by
    have h := (hγ 0).2
    rw [ell_zero_eq_one_of_constantsAreBase hC, map_zero] at h
    push_cast at h
    linarith
  have hH1 : indexOfSpecialty (0 : Divisor K F) = genusFF K F :=
    indexOfSpecialty_eq_finrank_H1 (0 : Divisor K F)
  have : (g : ℤ) = genusFF K F := by rw [← hH1, hi0, hγg]
  exact_mod_cast this
