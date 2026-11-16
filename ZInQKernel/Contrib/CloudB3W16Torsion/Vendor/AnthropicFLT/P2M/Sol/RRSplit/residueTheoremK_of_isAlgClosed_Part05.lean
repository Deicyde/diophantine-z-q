/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean; source lines 7509-8121.
Includes FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean material:
Copyright (c) 2025 Salvatore Mercuri. Authors: Salvatore Mercuri, Kevin Buzzard.
Modification notice (CloudB3 Worker16 curve support, 2026-11-16):
Factored at balanced source section boundaries. Relocated imports with the canonical main-port reuse map; expanded P2M
namespace/open/export command helpers to ordinary Lean commands, removed metadata
reactivation commands, and resolved metadata aliases directly. Expanded local notation
literally. Promoted source-private helpers into the original P2MW module namespace
so proofs can cross factoring-file boundaries without new root-name collisions.
Kept mathematical proof bodies and all public solution signatures; no new mathematical
assumptions. Lean 4.35 compatibility edits are recorded in the accompanying manifest.
Complete original LICENSE, NOTICE, and attribution are in this vendor root; a local
copy is supplied in RRSplit for independent distribution of this support patch.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.RRSplit.residueTheoremK_of_isAlgClosed_Part04

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed

-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_nonneg_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_nonneg_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_of_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_of_ord_nonneg
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_iff_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_iff_ord_nonneg
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.exists_ord_pos :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.exists_ord_pos
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.aeval_mem :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.aeval_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.exists_coeff_ord_ne_zero :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.exists_coeff_ord_ne_zero
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.isUnit_algebraMap :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.isUnit_algebraMap
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.adicValuation_algebraMap :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.adicValuation_algebraMap
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_algebraMap :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_algebraMap
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_eq_neg_log_of_valuationSubring_eq :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_eq_neg_log_of_valuationSubring_eq
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_prod :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_prod
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_add_eq_min :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_add_eq_min
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_add_eq_left :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_add_eq_left
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.subsingleton_canonicalLocalResidueDataK_of_surj :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.subsingleton_canonicalLocalResidueDataK_of_surj
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_regularSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_regularSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.regularPoleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.regularPoleSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_regularPoleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_regularPoleSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.regularPoleSubmodule_mono :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.regularPoleSubmodule_mono
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.iSup_regularPoleSubmodule_eq_top :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.iSup_regularPoleSubmodule_eq_top
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.exists_mem_regularPoleSubmodule :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.exists_mem_regularPoleSubmodule
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.surjective_algebraMap_residueField_of_isAlgClosed_of_finiteResidue :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.surjective_algebraMap_residueField_of_isAlgClosed_of_finiteResidue
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.subsingleton_canonicalLocalResidueDataK_of_isAlgClosed_of_finiteResidue :=
  @_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.subsingleton_canonicalLocalResidueDataK_of_isAlgClosed_of_finiteResidue


section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.TensorProduct
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.TensorProduct
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsLocalRing
open scoped _root_.AlgebraicCurve.Place _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place _root_.Valued _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Valued _root_.NNReal _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.NNReal _root_.WithZero _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute)

namespace KwF4R1V386a
open _root_.ModularCurve

open ModularCurve.KwF4R1V384a

section IsSeparableLift

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

theorem kwF4R1V386a_isSeparable_algebraMap_fiberCompletion
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    [FiniteDimensional E F] [Algebra.IsSeparable E F]
    (v : Place K E) (w' : v.fiber F) (g : F) :
    IsSeparable v.adicCompletion (algebraMap F w'.1.adicCompletion g) := by

  have hroot : Polynomial.aeval (R := v.adicCompletion)
      (algebraMap F w'.1.adicCompletion g)
      ((minpoly E g).map (algebraMap E v.adicCompletion)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap,
      show algebraMap F w'.1.adicCompletion g
          = IsScalarTower.toAlgHom E F w'.1.adicCompletion g from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, _root_.map_zero]

  have hmapsep : ((minpoly E g).map (algebraMap E v.adicCompletion)).Separable :=
    Polynomial.Separable.map (Algebra.IsSeparable.isSeparable E g)
  exact hmapsep.of_dvd (minpoly.dvd v.adicCompletion _ hroot)

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 8000000 in

theorem kwF4R1V386a_isSeparable_fiberCompletion
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    [FiniteDimensional E F] [Algebra.IsSeparable E F]
    (v : Place K E) (w' : v.fiber F) :
    Algebra.IsSeparable v.adicCompletion w'.1.adicCompletion := by

  have hgen : Algebra.adjoin v.adicCompletion
      (Set.range (algebraMap F w'.1.adicCompletion)) = ⊤ := by
    rw [Algebra.eq_top_iff]
    intro y
    obtain ⟨x, rfl⟩ := kwF4R1V384a_semilocalComponent_surjective v w' y
    induction x using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero]; exact zero_mem _
    | tmul c g =>
      rw [kwF4R1V384a_semilocalComponent_tmul, ← Algebra.smul_def]
      exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self g)) c
    | add x y hx hy => rw [map_add]; exact add_mem hx hy

  have hsep : ∀ x ∈ Set.range (algebraMap F w'.1.adicCompletion),
      IsSeparable v.adicCompletion x := by
    rintro _ ⟨g, rfl⟩
    exact kwF4R1V386a_isSeparable_algebraMap_fiberCompletion v w' g

  have hgenI : IntermediateField.adjoin v.adicCompletion
      (Set.range (algebraMap F w'.1.adicCompletion)) = ⊤ := by
    rw [eq_top_iff]; intro x _
    exact IntermediateField.algebra_adjoin_le_adjoin _ _ (hgen ▸ Algebra.mem_top)

  haveI hsepAdj : Algebra.IsSeparable v.adicCompletion
      (IntermediateField.adjoin v.adicCompletion
        (Set.range (algebraMap F w'.1.adicCompletion))) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable v.adicCompletion
      w'.1.adicCompletion).mpr hsep
  rw [hgenI] at hsepAdj
  exact Algebra.IsSeparable.of_algHom v.adicCompletion
    (⊤ : IntermediateField v.adicCompletion w'.1.adicCompletion)
    (IntermediateField.topEquiv (F := v.adicCompletion)
      (E := w'.1.adicCompletion)).symm.toAlgHom

end IsSeparableLift


section DistinctKernels

open scoped _root_.Valued _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Valued _root_.NNReal _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.NNReal _root_.WithZero _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

theorem kwF4R1V386a_spectralNorm_eq_absoluteValue [FiniteDimensional E F]
    (w' : Place K F) (y : w'.adicCompletion) :
    letI := kw_ffgc_rankOne_adicCompletion (w'.restrict E)
    letI : NontriviallyNormedField (w'.restrict E).adicCompletion :=
      Valued.toNontriviallyNormedField (w'.restrict E).adicCompletion ℤᵐ⁰
    spectralNorm (w'.restrict E).adicCompletion w'.adicCompletion y
      = kw_ffgc_absoluteValue E w' y := by
  letI := kw_ffgc_rankOne_adicCompletion (w'.restrict E)
  letI : NontriviallyNormedField (w'.restrict E).adicCompletion :=
    Valued.toNontriviallyNormedField (w'.restrict E).adicCompletion ℤᵐ⁰
  haveI : IsUltrametricDist (w'.restrict E).adicCompletion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (fun a b => Valuation.norm_add_le Valued.v a b)
  haveI : Algebra.IsAlgebraic (w'.restrict E).adicCompletion w'.adicCompletion :=
    Algebra.IsAlgebraic.of_finite _ _
  exact (spectralNorm_unique_field_norm_ext (f := kw_ffgc_absoluteValue E w')
    (kw_ffgc_absoluteValue_extends E w') y).symm

theorem kwF4R1V386a_spectralNorm_eq_absoluteValue_fiber
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F) (y : w'.1.adicCompletion) :
    letI := kw_ffgc_rankOne_adicCompletion v
    letI : NontriviallyNormedField v.adicCompletion :=
      Valued.toNontriviallyNormedField v.adicCompletion ℤᵐ⁰
    spectralNorm v.adicCompletion w'.1.adicCompletion y
      = kw_ffgc_absoluteValue E w'.1 y := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  exact kwF4R1V386a_spectralNorm_eq_absoluteValue (K := K) (E := E) w' y

theorem kwF4R1V386a_valuedAlgebraMap_le_one_iff (w' : Place K F) (g : F) :
    Valued.v (algebraMap F w'.adicCompletion g) ≤ 1 ↔ g ∈ w'.toValuationSubring := by
  have hval : Valued.v (algebraMap F w'.adicCompletion g) = w'.adicValuation g :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      (v := w'.heightOneSpectrum) (K := F) g
  rw [hval]
  rcases eq_or_ne g 0 with rfl | hg
  · simp only [_root_.map_zero, zero_le_one, w'.toValuationSubring.zero_mem]
  · rw [w'.mem_iff_ord_nonneg hg, Place.ord, neg_nonneg]
    have hvne : w'.adicValuation g ≠ 0 := w'.adicValuation_ne_zero hg
    rw [show (0 : ℤ) = WithZero.log (1 : ℤᵐ⁰) from WithZero.log_one.symm]
    exact ⟨fun hle => WithZero.log_le_log hvne one_ne_zero |>.mpr hle,
      fun hlog => (WithZero.log_le_log hvne one_ne_zero).mp hlog⟩

theorem kwF4R1V386a_absoluteValue_algebraMap_le_one_iff
    (w' : Place K F) (g : F) :
    kw_ffgc_absoluteValue E w' (algebraMap F w'.adicCompletion g) ≤ 1
      ↔ g ∈ w'.toValuationSubring := by
  letI := kw_ffgc_rankOne_adicCompletion w'
  have hr : (0 : ℝ) < ((w'.ramificationIndex E : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (w'.ramificationIndex_pos (F := E)))

  show ‖algebraMap F w'.adicCompletion g‖ ^ ((w'.ramificationIndex E : ℝ))⁻¹ ≤ 1
    ↔ g ∈ w'.toValuationSubring
  constructor
  · intro hle
    have hn : ‖algebraMap F w'.adicCompletion g‖ ≤ 1 := by
      by_contra hgt
      have hgt' : 1 < ‖algebraMap F w'.adicCompletion g‖ := not_le.mp hgt
      exact absurd ((Real.one_lt_rpow_iff_of_pos (lt_trans one_pos hgt')).mpr
        (Or.inl ⟨hgt', hr⟩)) (not_lt.mpr hle)
    rw [Valued.toNormedField.norm_le_one_iff] at hn
    exact (kwF4R1V386a_valuedAlgebraMap_le_one_iff w' g).mp hn
  · intro hmem
    have hn : ‖algebraMap F w'.adicCompletion g‖ ≤ 1 := by
      rw [Valued.toNormedField.norm_le_one_iff]
      exact (kwF4R1V386a_valuedAlgebraMap_le_one_iff w' g).mpr hmem
    calc ‖algebraMap F w'.adicCompletion g‖ ^ ((w'.ramificationIndex E : ℝ))⁻¹
        ≤ 1 ^ ((w'.ramificationIndex E : ℝ))⁻¹ :=
          Real.rpow_le_rpow (norm_nonneg _) hn hr.le
      _ = 1 := Real.one_rpow _

theorem kwF4R1V386a_distinctKernels :
    KwF4R1V384aDistinctKernels K F E := by
  intro _ _ _ v w' w'' hne hker
  apply hne

  have hsurj' := kwF4R1V384a_semilocalComponent_surjective v w'
  have hann : ∀ a ∈ RingHom.ker (kwF4R1V384a_semilocalComponent F v w').toRingHom,
      kwF4R1V384a_semilocalComponent F v w'' a = 0 := fun a ha => by
    have : a ∈ RingHom.ker (kwF4R1V384a_semilocalComponent F v w'').toRingHom :=
      hker ▸ ha
    exact this
  let σ : w'.1.adicCompletion →ₐ[v.adicCompletion] w''.1.adicCompletion :=
    (Ideal.Quotient.liftₐ _ (kwF4R1V384a_semilocalComponent F v w'') hann).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsurj').symm.toAlgHom

  have hσcomp : ∀ x, σ (kwF4R1V384a_semilocalComponent F v w' x)
      = kwF4R1V384a_semilocalComponent F v w'' x := by
    intro x
    have hstep1 : (Ideal.quotientKerAlgEquivOfSurjective hsurj').symm
        (kwF4R1V384a_semilocalComponent F v w' x) = Ideal.Quotient.mk _ x := by
      rw [show kwF4R1V384a_semilocalComponent F v w' x
          = Ideal.quotientKerAlgEquivOfSurjective hsurj' (Ideal.Quotient.mk _ x) from rfl,
        AlgEquiv.symm_apply_apply]
    simp only [σ, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.liftₐ_apply]
    erw [hstep1, Ideal.Quotient.lift_mk]
  have hσF : ∀ g : F, σ (algebraMap F w'.1.adicCompletion g)
      = algebraMap F w''.1.adicCompletion g := by
    intro g
    have h' := hσcomp ((1 : v.adicCompletion) ⊗ₜ[E] g)
    rwa [kwF4R1V384a_semilocalComponent_tmul, map_one, one_mul,
      kwF4R1V384a_semilocalComponent_tmul, map_one, one_mul] at h'

  letI := kw_ffgc_rankOne_adicCompletion v
  letI : NontriviallyNormedField v.adicCompletion :=
    Valued.toNontriviallyNormedField v.adicCompletion ℤᵐ⁰
  have hσinj : Function.Injective σ := σ.toRingHom.injective
  have hσspec : ∀ y, spectralNorm v.adicCompletion w''.1.adicCompletion (σ y)
      = spectralNorm v.adicCompletion w'.1.adicCompletion y := by
    intro y
    unfold spectralNorm
    congr 1
    exact minpoly.algHom_eq σ hσinj y

  refine Subtype.ext ?_
  refine AlgebraicCurve.Place.ext (K := K) (F := F) (SetLike.ext fun g => ?_)

  rw [← kwF4R1V386a_absoluteValue_algebraMap_le_one_iff (K := K) (E := E) w'.1 g,
    ← kwF4R1V386a_absoluteValue_algebraMap_le_one_iff (K := K) (E := E) w''.1 g,
    ← kwF4R1V386a_spectralNorm_eq_absoluteValue_fiber (K := K) (E := E) v w'
      (algebraMap F w'.1.adicCompletion g),
    ← kwF4R1V386a_spectralNorm_eq_absoluteValue_fiber (K := K) (E := E) v w''
      (algebraMap F w''.1.adicCompletion g),
    ← hσF g, hσspec]

end DistinctKernels


section FinrankCompletionEF

open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.Valuation
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Valuation

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

theorem kwF4R1V386a_ramificationIdx_completion_eq
    (w' : Place K F) :
    (maximalIdeal (w'.restrict E).adicCompletionIntegers).ramificationIdx'
      (maximalIdeal w'.adicCompletionIntegers) = w'.ramificationIndex E := by
  set e := w'.ramificationIndex E with he
  have hepos : 0 < e := w'.ramificationIndex_pos (F := E)

  obtain ⟨π, hπval⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer E
    (w'.restrict E).heightOneSpectrum

  have hmap : (maximalIdeal (w'.restrict E).adicCompletionIntegers).map
      (algebraMap (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers)
        = Ideal.span {algebraMap _ w'.adicCompletionIntegers π} := by
    rw [show maximalIdeal ((w'.restrict E).adicCompletionIntegers : Type _)
        = (w'.restrict E).heightOneSpectrum.completionIdeal E from rfl,
      IsDedekindDomain.HeightOneSpectrum.completionIdeal,
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer E
        _ hπval,
      Ideal.map_span, Set.image_singleton]
  have hπval' : Valued.v (π : (w'.restrict E).adicCompletion)
      = (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤᵐ⁰) := hπval

  have hval : Valued.v ((algebraMap (w'.restrict E).adicCompletionIntegers
        w'.adicCompletionIntegers π : w'.adicCompletionIntegers) : w'.adicCompletion)
      = (↑(Multiplicative.ofAdd (-(e : ℤ))) : ℤᵐ⁰) := by
    rw [show ((algebraMap _ w'.adicCompletionIntegers π
          : w'.adicCompletionIntegers) : w'.adicCompletion)
        = kw_ffgc_adicCompletionComap E w' (π : (w'.restrict E).adicCompletion) from
      (kw_ffgc_adicCompletionComapIntegers_coe E w' π).symm,
      kw_ffgc_valued_adicCompletionComap, hπval', ← WithZero.coe_pow, WithZero.coe_inj,
      ← ofAdd_nsmul, nsmul_eq_mul, mul_neg_one, he]

  refine Ideal.ramificationIdx_spec ?_ ?_
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      show maximalIdeal (w'.adicCompletionIntegers : Type _)
        = w'.heightOneSpectrum.completionIdeal F from rfl,
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.mem_completionIdeal_pow, hval]
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      show maximalIdeal (w'.adicCompletionIntegers : Type _)
        = w'.heightOneSpectrum.completionIdeal F from rfl,
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.mem_completionIdeal_pow, hval]
    simp only [WithZero.coe_le_coe, Multiplicative.ofAdd_le, not_le]
    omega

set_option maxHeartbeats 16000000 in

set_option synthInstance.maxHeartbeats 12800000 in
theorem kwF4R1V386a_integersToCompletion_commute
    (w' : Place K F) (a : (w'.restrict E).toValuationSubring) :
    algebraMap (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers
        (algebraMap (w'.restrict E).toValuationSubring
          (w'.restrict E).adicCompletionIntegers a)
      = algebraMap w'.toValuationSubring w'.adicCompletionIntegers
          (restrictInclusion E w' a) := by
  apply Subtype.ext
  exact (kw_ffgc_adicCompletionComap_algebraMap_algebraMap E w' (a : E)).symm

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 8000000 in

theorem kwF4R1V386a_inertiaDeg_completion_eq
    (w' : Place K F) :
    (maximalIdeal (w'.restrict E).adicCompletionIntegers).inertiaDeg'
      (maximalIdeal w'.adicCompletionIntegers) = w'.inertiaDeg E := by

  haveI : IsLocalHom (algebraMap (w'.restrict E).adicCompletionIntegers
      w'.adicCompletionIntegers) :=
    kw_ffgc_isLocalHom_adicCompletionComapIntegers E w'
  haveI : (maximalIdeal w'.adicCompletionIntegers).LiesOver
      (maximalIdeal (w'.restrict E).adicCompletionIntegers) := by
    have hcomap : (maximalIdeal w'.adicCompletionIntegers).comap
        (algebraMap (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers)
        = maximalIdeal (w'.restrict E).adicCompletionIntegers :=
      ((IsLocalRing.local_hom_TFAE (algebraMap (w'.restrict E).adicCompletionIntegers
        w'.adicCompletionIntegers)).out 0 4).mp ‹IsLocalHom _›
    exact ⟨hcomap.symm⟩
  rw [Ideal.inertiaDeg'_algebraMap]

  symm
  refine Algebra.finrank_eq_of_equiv_equiv
    (kw_ffgc_residueFieldEquivCompletionResidueField (w'.restrict E))
    (kw_ffgc_residueFieldEquivCompletionResidueField w') ?_

  ext a
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe]

  exact congrArg (IsLocalRing.residue w'.adicCompletionIntegers)
    (kwF4R1V386a_integersToCompletion_commute (K := K) (E := E) w' a)

theorem kwF4R1V386a_finrankCompletionEF [Algebra.IsSeparable E F] :
    KwF4R1V384aFinrankCompletionEF K F E := by
  intro _ _ _ v wfib
  have hv : wfib.1.restrict E = v := Place.mem_fiber.mp wfib.2

  haveI hsep : Algebra.IsSeparable v.adicCompletion wfib.1.adicCompletion :=
    kwF4R1V386a_isSeparable_fiberCompletion v wfib
  rcases wfib with ⟨w', hw'⟩
  dsimp only at hv hsep ⊢
  subst hv

  haveI : Algebra.IsSeparable (w'.restrict E).adicCompletion w'.adicCompletion := hsep
  haveI : Algebra.IsAlgebraic (w'.restrict E).adicCompletion w'.adicCompletion :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : IsIntegralClosure w'.adicCompletionIntegers
      (w'.restrict E).adicCompletionIntegers w'.adicCompletion :=
    kw_ffgc_isIntegralClosure_adicCompletionIntegers E w'
  haveI : IsNoetherian (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers :=
    IsIntegralClosure.isNoetherian (w'.restrict E).adicCompletionIntegers
      (w'.restrict E).adicCompletion w'.adicCompletion w'.adicCompletionIntegers
  haveI : Module.Finite (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers :=
    Module.IsNoetherian.finite _ _

  have hpne : maximalIdeal (w'.restrict E).adicCompletionIntegers ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_isField _
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr h)

  have hef := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    w'.adicCompletionIntegers (w'.restrict E).adicCompletion w'.adicCompletion hpne
  rw [kwF4R1V386a_ramificationIdx_completion_eq (K := K) w',
    kwF4R1V386a_inertiaDeg_completion_eq (K := K) w'] at hef
  exact_mod_cast hef.symm

end FinrankCompletionEF


section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

theorem kwF4R1V386a_completionTraceSum_of_isSeparable [Algebra.IsSeparable E F] :
    AlgebraicCurve.KwHgfV352CompletionTraceSum K F E :=
  kwF4R1V384a_completionTraceSum_of_distinctKernels_finrankEF
    kwF4R1V386a_distinctKernels kwF4R1V386a_finrankCompletionEF

end Headline


end ModularCurve.KwF4R1V386a



end

end


end


section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.KaehlerDifferential
open _root_.ModularCurve.KwF4R1V391a
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.ModularCurve.KwF4R1V391a
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.ModularCurve.KwF4R1V386a
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.ModularCurve.GF24a9RRDx
open ModularCurve.KwF4R1V398a ModularCurve.KwF4R1V402a
open _root_.ModularCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.ModularCurve

noncomputable section

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Place.ord Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential diagonalHom diagonalHom_apply diagonal_mem_adeleSpace HasCanonicalDivisor HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTerm kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_support_finite_of_adeleSpace weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar Place.mem_fiber Place.valuationSubringAlgebra Place.finite_setOf_restrict_eq kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kaehlerCotrace kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt KwHgfV352CompletionTraceSum FiberKaehlerCotraceResidueIdentityK CotraceResidueIdentityOnFiberLocalizedK Place.finiteResidue_of_deg_pos residueTraceCompletionCommute residueTheoremK_ratFunc_of_isAlgClosed)

open _root_.AlgebraicCurve

section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [∀ w : Place K F, w.FiniteResidue] [FiniteDimensional E F]
variable [Nontrivial Ω[E⁄K]] [∀ v : Place K E, v.DCoordGenerates]
variable [Nontrivial Ω[F⁄K]] [∀ w : Place K F, w.DCoordGenerates]

theorem kw_es_fiberKaehlerCotraceResidueIdentity_of_RTCC_CTS
    (hRTCC : KwF4R1V391aResidueTraceCompletionCommute K F E)
    (hCTS : KwHgfV352CompletionTraceSum K F E) :
    FiberKaehlerCotraceResidueIdentity K F E := by
  intro _ _ ωE _hωE _hωF v f
  calc ∑ w ∈ v.fiber F,
          kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F f) w

      = ∑ w' ∈ (v.fiber F).attach,
          Algebra.trace K v.ResidueField
            (kwHgfV352_localResidueCompletion v
              (kwHgfV352_completionTraceAt v w'.1 w'.2 f
                * algebraMap E v.adicCompletion (v.differentialCoeff ωE))) := by
        rw [← Finset.sum_attach (v.fiber F)
          (fun w => kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F f) w)]
        refine Finset.sum_congr rfl fun w' _ => ?_
        rw [kaehlerResidueTerm_kaehlerPullback_diagonal_eq_dCoord_shift v w'.1 ωE f,
          hRTCC v w'.1 w'.2 (f * algebraMap E F (v.differentialCoeff ωE)),
          kwF4R1V391a_completionTraceAt_mul_algebraMap v w'.1 w'.2 f
            (v.differentialCoeff ωE)]

    _ = Algebra.trace K v.ResidueField
          (kwHgfV352_localResidueCompletion v
            ((∑ w' ∈ (v.fiber F).attach, kwHgfV352_completionTraceAt v w'.1 w'.2 f)
              * algebraMap E v.adicCompletion (v.differentialCoeff ωE))) := by
        rw [Finset.sum_mul,
          kwHgfV352_localResidueCompletion_sum v (v.fiber F).attach _,
          map_sum]

    _ = Algebra.trace K v.ResidueField
          (kwHgfV352_localResidueCompletion v
            (algebraMap E v.adicCompletion (Algebra.trace E F f)
              * algebraMap E v.adicCompletion (v.differentialCoeff ωE))) := by
        rw [← hCTS v f]

    _ = Algebra.trace K v.ResidueField
          (v.localResidue (Algebra.trace E F f * v.differentialCoeff ωE)) := by
        rw [← map_mul, kwHgfV352_localResidueCompletion_algebraMap v]

    _ = kaehlerResidueTerm ωE (diagonalHom K E (Algebra.trace E F f)) v := by
        unfold kaehlerResidueTerm; rw [diagonalHom_apply]

end Headline


section Compose

variable {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
variable [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
variable [HasLocalResidue K F]
variable [∀ w : Place K F, w.FiniteResidue]
variable [Nontrivial Ω[F⁄K]]

theorem kw_es_residueTheoremK_of_RTCC_isAlgClosed
    [HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]
    (hgen : kaehlerPullback K F (RatFunc K) (dX K) ≠ 0)
    (hRTCC : KwF4R1V391aResidueTraceCompletionCommute K F (RatFunc K)) :
    ResidueTheoremK K F := by

  have hCTS : KwHgfV352CompletionTraceSum K F (RatFunc K) :=
    kwF4R1V386a_completionTraceSum_of_isSeparable (K := K) (F := F) (E := RatFunc K)

  exact residueTheoremK_of_fiberKaehlerCotraceResidueIdentity_ratFunc_isAlgClosed hgen
    (kw_es_fiberKaehlerCotraceResidueIdentity_of_RTCC_CTS hRTCC hCTS)

theorem kw_es_residueTheoremK_of_RTCC_isAlgClosed'
    [HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]
    (hRTCC : KwF4R1V391aResidueTraceCompletionCommute K F (RatFunc K)) :
    ResidueTheoremK K F :=
  kw_es_residueTheoremK_of_RTCC_isAlgClosed
    (kaehlerPullback_eq_kaehlerCotrace (K := K) (F := F) (E := RatFunc K) (dX K) ▸
      kaehlerCotrace_dX_ne_zero_of_isSeparable K F (RationalFunctionField.placeInfty K))
    hRTCC

end Compose


end AlgebraicCurve


end


end


end


section S18AliasSR
namespace ModularCurve
export _root_.ModularCurve (KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute)
 namespace KwTateRR3
end ModularCurve.KwTateRR3
open scoped _root_.ModularCurve in
theorem ModularCurve.KwTateRR3.kwTateRR3_RTCC_of_isSeparable
    {K F E : Type*} [Field K] [Field F] [Algebra K F]
    [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F]
    [∀ u : AlgebraicCurve.Place K E, u.FiniteResidue]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K E] [PerfectField K]
    [Nontrivial Ω[F⁄K]] [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra.IsSeparable E F] :
    ModularCurve.KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute K F E :=
  AlgebraicCurve.residueTraceCompletionCommute
end S18AliasSR


section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.Submodule
open _root_.ModularCurve.KwF4R1V391a
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.ModularCurve.KwF4R1V391a
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.ModularCurve.KwTateRR3
open ModularCurve.GF24a9RRDx

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute)

namespace KwTateRR3
open _root_.ModularCurve

section RTCCSeparable

variable {K F E : Type*} [Field K] [Field F] [Algebra K F]
variable [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [∀ u : Place K E, u.FiniteResidue]
variable [IsCurveOver K F] [IsCurveOver K E] [PerfectField K]

end RTCCSeparable


section RTKCapstone

variable {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
variable [Field F] [Algebra K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
variable [HasLocalResidue K F]
variable [∀ w : Place K F, w.FiniteResidue]
variable [Nontrivial Ω[F⁄K]]
variable [IsCurveOver K F] [IsCurveOver K (RatFunc K)]
variable [∀ u : Place K (RatFunc K), u.FiniteResidue]

theorem kwTateRR3_residueTheoremK_of_isAlgClosed
    [HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates] :
    ResidueTheoremK K F :=
  kw_es_residueTheoremK_of_RTCC_isAlgClosed'
    (kwTateRR3_RTCC_of_isSeparable (E := RatFunc K))

end RTKCapstone


end ModularCurve.KwTateRR3



end


end


end


theorem solution
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheoremK K F :=
  ModularCurve.KwTateRR3.kwTateRR3_residueTheoremK_of_isAlgClosed

end P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed
