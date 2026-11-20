/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_omegaSpace_finite_of_genusReached
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached

set_option autoImplicit false
set_option maxHeartbeats 4000000

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (Q : Place K F) :
    ∃ n : ℕ, indexOfSpecialty ((n : ℤ) • Finsupp.single Q (1 : ℤ)) = 0 := by
  classical

  have hQdeg : (1 : ℤ) ≤ (Q.deg : ℤ) := by
    have hfin : Module.Finite K Q.ResidueField := IsCurveOver.finiteResidue Q
    have hpos : 0 < Q.deg := Module.finrank_pos
    exact_mod_cast hpos

  set B : ℤ := (indexOfSpecialty (0 : Divisor K F) : ℤ) + γ - 1 with hB
  refine ⟨B.natAbs + 1, ?_⟩
  set n : ℕ := B.natAbs + 1 with hn
  set Dn : Divisor K F := (n : ℤ) • Finsupp.single Q (1 : ℤ) with hDn

  have hdeg : Divisor.degree Dn = (n : ℤ) * (Q.deg : ℤ) := by
    simp only [hDn, zsmul_eq_mul, Finsupp.smul_single, mul_one]
    exact Divisor.degree_single Q (n : ℤ)

  have hBn : B < (n : ℤ) * (Q.deg : ℤ) := by
    have h1 : B < (n : ℤ) := by
      have : B ≤ |B| := le_abs_self B
      rw [Int.abs_eq_natAbs] at this
      calc B ≤ (B.natAbs : ℤ) := this
        _ < (B.natAbs : ℤ) + 1 := lt_add_one _
        _ = (n : ℤ) := by push_cast [hn]; ring
    calc B < (n : ℤ) := h1
      _ = (n : ℤ) * 1 := (mul_one _).symm
      _ ≤ (n : ℤ) * (Q.deg : ℤ) := by
          apply mul_le_mul_of_nonneg_left hQdeg
          exact_mod_cast Nat.zero_le n

  by_contra hne

  haveI homegafin : Module.Finite K ↥(omegaSpace (K := K) (F := F) Dn) :=
    omegaSpace_finite_of_genusReached h Dn
  have homegane : (omegaSpace (K := K) (F := F) Dn) ≠ ⊥ := by
    intro hbot
    apply hne
    rw [← finrank_omegaSpace_eq_indexOfSpecialty Dn, hbot]
    exact finrank_bot K _

  obtain ⟨ψ, hψ, hψne⟩ := (Submodule.ne_bot_iff _).mp homegane

  haveI hfin0 : Module.Finite K ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F)) :=
    omegaSpace_finite_of_genusReached h 0
  have hle : (ell Dn : ℤ) ≤ (indexOfSpecialty (0 : Divisor K F) : ℤ) := by
    have hls := ell_sub_le_indexOfSpecialty Dn (0 : Divisor K F) hψ hψne
    simp only [sub_zero] at hls
    exact_mod_cast hls

  have hmax := h.isMax Dn
  rw [hdeg] at hmax

  linarith
