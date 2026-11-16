/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean; source lines 9809-11709.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.RRSplit.residueTheoremK_ratFunc_of_isAlgClosed_Part05

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed

section
section

set_option linter.unusedSectionVars false

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

section NamedRow

variable (K F)
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

def CanonicalLocalResidueKSimplePoleCoordIndep : Prop :=
  ∀ (v : Place K F) (π' : F), v.ord π' = 1 →
    ∀ (R : v.CanonicalLocalResidueDataK),
      R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * (π')⁻¹) = 1

end NamedRow


section SATGate

variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end SATGate


section XInvCoordinate

variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1XAtom_mul_differentialCoeff_dX_eq_neg :
    p1PrincipalPartAtom K (X : K[X]) 1 1 * (placeInfty K).differentialCoeff (dX K)
      = -((placeInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)
          * ((RatFunc.X : RatFunc K)⁻¹)⁻¹) := by
  show algebraMap K[X] (RatFunc K) 1 / algebraMap K[X] (RatFunc K) X ^ 1
        * (placeInfty K).differentialCoeff (dX K)
      = -((placeInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)
          * ((RatFunc.X : RatFunc K)⁻¹)⁻¹)
  rw [show (dX K) = KaehlerDifferential.D K (RatFunc K) RatFunc.X from rfl,
    differentialCoeff_placeInfty_D_X_eq K, RatFunc.algebraMap_X, map_one, pow_one, inv_inv,
    one_div]
  field_simp [RatFunc.X_ne_zero (K := K), sq, mul_comm]

end XInvCoordinate


section InftyXDischarge

variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem trace_placeInfty_residueField_one :
    Algebra.trace K (placeInfty K).ResidueField 1 = 1 := by
  rw [show (1 : (placeInfty K).ResidueField) = algebraMap K _ 1 from (map_one _).symm,
    Algebra.trace_algebraMap, show Module.finrank K (placeInfty K).ResidueField = 1 from
      deg_placeInfty K, one_smul]

theorem simplePoleResidueAux_placeInfty_p1XAtom_eq_neg_one
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K))
    (himem : p1PrincipalPartAtom K (X : K[X]) 1 1 * (placeInfty K).differentialCoeff (dX K)
        ∈ (placeInfty K).simplePoleSubmodule) :
    (placeInfty K).simplePoleResidueAux ⟨_, himem⟩ = -1 := by

  set R := (placeInfty K).canonicalLocalResidueDataKOfExtend
  rw [← (placeInfty K).localResidueData_res_eq_simplePoleResidueAux R.toLocalResidueData himem,
    show R.toLocalResidueData.res = R.res from rfl,
    p1XAtom_mul_differentialCoeff_dX_eq_neg K, _root_.map_neg,
    hsp (placeInfty K) (RatFunc.X : RatFunc K)⁻¹ (ord_placeInfty_X_inv K) R]

theorem p1PlaceInftySimplePoleResidueEulerValueX_of_simplePoleCoordIndep
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K)) :
    P1PlaceInftySimplePoleResidueEulerValueX K := by
  intro himem
  rw [simplePoleResidueAux_placeInfty_p1XAtom_eq_neg_one K hsp himem, _root_.map_neg,
    trace_placeInfty_residueField_one K]

end InftyXDischarge


section ComposedEngine

variable (K) [DecidableEq (RatFunc K)] [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1PrincipalPartMOneSimplePoleCancel_of_simplePoleCoordIndep
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) (heq : ω₀ = dX K)
    (hsp : CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K)) :
    P1PrincipalPartMOneSimplePoleCancel K hω₀ :=
  p1PrincipalPartMOneSimplePoleCancel_of_inftyX K hwd hω₀ heq
    (p1PlaceInftySimplePoleResidueEulerValueX_of_simplePoleCoordIndep K hsp)

end ComposedEngine


section Monotonicity

variable (K) [DecidableEq (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

end Monotonicity


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end

end


end


section
section

open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField

namespace IntermediateField

export _root_.IntermediateField (charP toAlgebra map_le_iff_le_comap mk val isIntegral_iff topEquiv_apply lift_top lift AdjoinSimple.gen inclusion lift_injective lift_adjoin_simple ext adjoin_simple_le_iff charZero equivOfEq algebraMap_apply smul_def adjoin mk.injEq AdjoinSimple.algebraMap_gen comap topEquiv mem_top adjoinRootEquivAdjoin restrictScalars rec adjoinRootEquivAdjoin_apply_root coe_smul AdjoinSimple.coe_gen mem_bot mem_adjoin_simple_self adjoin_map smul_mem restrict map)

open _root_.IntermediateField

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem adjoin_simple_map_algHom' (e : F →ₐ[K] F') (t : F) :
    (K⟮t⟯).map e = K⟮e t⟯ := by
  rw [adjoin_map, Set.image_singleton]

theorem adjoin_simple_eq_top_of_algEquiv (e : F ≃ₐ[K] F') {t : F}
    (htop : K⟮t⟯ = (⊤ : IntermediateField K F)) :
    K⟮e t⟯ = (⊤ : IntermediateField K F') := by
  have key : K⟮(e : F →ₐ[K] F') t⟯ = (⊤ : IntermediateField K F') := by
    rw [← adjoin_simple_map_algHom' (e : F →ₐ[K] F') t, htop,
      ← AlgHom.fieldRange_eq_map, AlgEquiv.fieldRange_eq_top]
  exact key

end IntermediateField


namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

section Congr

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem IsPurelyTranscendentalSimple.congr (e : F ≃ₐ[K] F')
    (h : IsPurelyTranscendentalSimple K F) : IsPurelyTranscendentalSimple K F' := by
  obtain ⟨t, ht, htop⟩ := h
  refine ⟨e t, ?_, IntermediateField.adjoin_simple_eq_top_of_algEquiv e htop⟩
  unfold Transcendental at ht ⊢
  rw [show (e t : F') = (e : F →ₐ[K] F') t from rfl,
    isAlgebraic_algHom_iff (e : F →ₐ[K] F') e.injective]
  exact ht

end Congr


section RatFuncInstance

variable (K : Type*) [Field K]

theorem isPurelyTranscendentalSimple_ratFunc :
    IsPurelyTranscendentalSimple K (RatFunc K) :=
  (isPurelyTranscendentalSimple_adjoin_simple (RatFunc.transcendental_X (K := K))).congr
    (RatFunc.algEquivOfTranscendental (RatFunc.X : RatFunc K)
      (RatFunc.transcendental_X (K := K))).symm

end RatFuncInstance


section Iff

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isPurelyTranscendentalSimple_of_ratFuncAlgEquiv
    (h : Nonempty (RatFunc K ≃ₐ[K] F)) : IsPurelyTranscendentalSimple K F :=
  (isPurelyTranscendentalSimple_ratFunc K).congr h.some

end Iff


section CharZeroReflection

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end CharZeroReflection


section TowerComposites

variable {K F F' : Type*} [Field K] [Field F] [Field F']
variable [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

end TowerComposites


end AlgebraicCurve


namespace ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve

variable (N : ℕ) [NeZero N]

end ModularCurve


namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

end AlgebraicCurve


namespace ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve

end ModularCurve


section AxiomAudits

end AxiomAudits


end


end


section
section

open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

section AbstractEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open scoped AlgebraicCurve.Place in
theorem Place.dCoordGenerates_of_valSubringKaehlerSpanTop
    (hspan : ValSubringKaehlerSpanTop K F) (v : Place K F) :
    v.DCoordGenerates := by
  constructor
  rw [eq_top_iff,
    ← KaehlerDifferential.span_range_map_derivation_of_isLocalization (R := K)
      (S := v.toValuationSubring) (T := F) (nonZeroDivisors v.toValuationSubring),
    Submodule.span_le]
  rintro _ ⟨f, rfl⟩

  have hDf : KaehlerDifferential.D K v.toValuationSubring f
      ∈ (⊤ : Submodule v.toValuationSubring Ω[v.toValuationSubring⁄K]) := Submodule.mem_top
  rw [← hspan v] at hDf
  have hmap : (KaehlerDifferential.map K K v.toValuationSubring F ∘
        KaehlerDifferential.D K v.toValuationSubring) f
      ∈ Submodule.map (KaehlerDifferential.map K K v.toValuationSubring F)
        (Submodule.span v.toValuationSubring _) :=
    Submodule.mem_map_of_mem hDf
  rw [Submodule.map_span, Set.image_singleton,
    v.kaehlerMap_subring_D_uniformizer] at hmap

  exact Submodule.span_le_restrictScalars v.toValuationSubring F {v.dCoord} hmap

open scoped AlgebraicCurve.Place in
theorem Place.dCoordGenerates_of_valSubringKaehlerFinite_of_charZero
    [CharZero K] [∀ v : Place K F, v.FiniteResidue]
    (hfin : ValSubringKaehlerFinite K F) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_valSubringKaehlerSpanTop
    (valSubringKaehlerSpanTop_of_kaehlerFinite_of_charZero hfin) v

end AbstractEngine


section ChainComposites

variable {K F F' : Type*} [Field K] [Field F] [Field F']
variable [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

open scoped AlgebraicCurve.Place in
theorem Place.dCoordGenerates_of_isPurelyTranscendentalSimple
    [CharZero K] [∀ v : Place K F, v.FiniteResidue]
    (h : IsPurelyTranscendentalSimple K F) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_valSubringKaehlerFinite_of_charZero
    (valSubringKaehlerFinite_of_core
      (hasSeparatingTranscendentalCore_of_isPurelyTranscendentalSimple h)) v

end ChainComposites


end AlgebraicCurve


namespace ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve

variable (N : ℕ) [NeZero N]

end ModularCurve


namespace ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve

variable (N : ℕ) [NeZero N]

theorem gate_dCoordGenerates_of_ratFunc_sat
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [CharZero K] [∀ v : Place K F, v.FiniteResidue]
    (hRat : Nonempty (RatFunc K ≃ₐ[K] F)) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_isPurelyTranscendentalSimple
    (isPurelyTranscendentalSimple_of_ratFuncAlgEquiv hRat) v

end ModularCurve


section AxiomAudits

end AxiomAudits


end


end


section
section

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum residueFieldEquivOfHeightOneSpectrum deg_ofHeightOneSpectrum deg_finitePlace)

open _root_.AlgebraicCurve.RationalFunctionField

variable {K : Type*} [Field K]

scoped instance (priority := low) instDCoordGenerates [CharZero K] (v : Place K (RatFunc K)) :
    v.DCoordGenerates :=
  ModularCurve.gate_dCoordGenerates_of_ratFunc_sat ⟨AlgEquiv.refl⟩ v

end RationalFunctionField


section TransportTwoRoutes

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]

end TransportTwoRoutes


section ConsumerDemonstrations

variable {K : Type*} [Field K] [CharZero K]

end ConsumerDemonstrations


end AlgebraicCurve


namespace ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve
open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField

section RatBasePinned

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

end RatBasePinned


section RatBaseCrossing

end RatBaseCrossing


end ModularCurve


section AxiomAudits

end AxiomAudits


end

end


end


section
section

noncomputable section

open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end Uniqueness


section Profile

variable (K : Type*) [Field K]

theorem exists_smul_dX_eq (ω : Ω[(RatFunc K)⁄K]) : ∃ c : RatFunc K, c • dX K = ω := by
  have hmem : ω ∈ Submodule.span (RatFunc K) {dX K} :=
    span_dX_eq_top K ▸ Submodule.mem_top
  exact Submodule.mem_span_singleton.mp hmem

section ProfileValues

variable [CharZero K] [DecidableEq (RatFunc K)]

theorem ordDifferential_dX_of_ne_placeInfty {v : Place K (RatFunc K)}
    (hv : v ≠ placeInfty K) : v.ordDifferential (dX K) = 0 := by
  rw [Place.ordDifferential]
  exact p1DifferentialCoeffUnitFinite_dX K v hv

theorem ordDifferential_dX_placeInfty :
    (placeInfty K).ordDifferential (dX K) = -2 :=
  ordDifferential_placeInfty_D_ratFuncX K (ordDifferentialWellDefined_ratFunc K)

theorem exists_divisor_smul_dX {c : RatFunc K} (hc : c ≠ 0) :
    ∃ D : Divisor K (RatFunc K),
      (∀ v : Place K (RatFunc K), D v = v.ordDifferential (c • dX K)) ∧
        Divisor.degree D = -2 := by
  obtain ⟨Dc, hDc, hDcdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (F := RatFunc K) c hc
  refine ⟨Dc + Finsupp.single (placeInfty K) (-2), fun v => ?_, ?_⟩
  ·
    rw [Finsupp.add_apply, hDc v,
      v.ordDifferential_smul hc (v.differentialCoeff_ne_zero (dX_ne_zero K))]
    rcases eq_or_ne v (placeInfty K) with rfl | hne
    · rw [ordDifferential_dX_placeInfty K, Finsupp.single_eq_same]
    · rw [ordDifferential_dX_of_ne_placeInfty K hne, Finsupp.single_eq_of_ne hne]
  ·
    rw [map_add, hDcdeg, zero_add, Divisor.degree_single, deg_placeInfty K, Nat.cast_one,
      mul_one]

end ProfileValues


section Instance

variable [CharZero K]

scoped instance instHasCanonicalDivisorRatFunc :
    HasCanonicalDivisor (K := K) (F := RatFunc K) where
  exists_divisor ω hω := by
    classical
    obtain ⟨c, hc⟩ := exists_smul_dX_eq K ω
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hω hc.symm
    obtain ⟨D, hD, -⟩ := exists_divisor_smul_dX K hc0
    refine ⟨D, fun v => ?_⟩
    rw [← hc]
    exact hD v

end Instance


section ExactDivisor

variable [CharZero K] [DecidableEq (RatFunc K)]

end ExactDivisor


end Profile


section RatDiamond

end RatDiamond


end AlgebraicCurve


namespace ModularCurve

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve
open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IntermediateField

end ModularCurve


section AxiomAudit

end AxiomAudit


end

end


end


section
section

set_option linter.unusedSectionVars false

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

section KaehlerToolbox

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

theorem D_pow_succ_inv (f : F) (m : ℕ) :
    KaehlerDifferential.D K F ((f ^ (m + 1))⁻¹)
      = (-((m + 1 : ℕ) : F) * (f ^ (m + 2))⁻¹) • KaehlerDifferential.D K F f := by
  rw [← inv_pow f (m + 1), Derivation.leibniz_pow, Derivation.leibniz_inv, Nat.add_sub_cancel,
    smul_smul, ← Nat.cast_smul_eq_nsmul F (m + 1), smul_smul, ← inv_pow f (m + 2)]
  congr 1
  push_cast
  ring

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

variable (v : Place K F)

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.differentialCoeff_add'' [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] (ω₁ ω₂ : Ω[F⁄K]) :
    v.differentialCoeff (ω₁ + ω₂) = v.differentialCoeff ω₁ + v.differentialCoeff ω₂ :=
  v.differentialCoeff_unique (by
    rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])




theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.Place.differentialCoeff_D_uniformizer_pow_inv [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (m : ℕ) :
    v.differentialCoeff (KaehlerDifferential.D K F ((v.uniformizer ^ (m + 1))⁻¹))
      = -((m + 1 : ℕ) : F) * (v.uniformizer ^ (m + 2))⁻¹ := by
  rw [D_pow_succ_inv, show KaehlerDifferential.D K F v.uniformizer = v.dCoord from rfl,
    v.differentialCoeff_smul, v.differentialCoeff_dCoord, mul_one]




end Place


end KaehlerToolbox


section DXCoeffIntegrality

variable {K : Type*} [Field K]

theorem ratFuncDXCoeff_eq_of_D_eq_smul_dX {f e : RatFunc K}
    (h : KaehlerDifferential.D K (RatFunc K) f = e • dX K) : ratFuncDXCoeff K f = e := by
  have key : (ratFuncDXCoeff K f - e) • dX K = 0 := by
    rw [sub_smul, ← D_eq_ratFuncDXCoeff_smul_dX K f, h, sub_self]
  rcases smul_eq_zero.mp key with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' (dX_ne_zero K)

theorem ratFuncDXCoeff_zero : ratFuncDXCoeff K (0 : RatFunc K) = 0 :=
  ratFuncDXCoeff_eq_of_D_eq_smul_dX (by rw [_root_.map_zero, zero_smul])

section FinitePlaces

variable {w : HeightOneSpectrum K[X]}



theorem ord_algebraMap_denom_eq_zero_of_ord_nonneg {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : 0 ≤ ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord f) :
    ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
  by_contra hne
  have hpd : p ∣ f.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ f.num := fun hpn =>
    hp.not_isUnit (f.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K) f.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hf)).mp h)
  have hordd : 0 < ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K) f.denom) :=
    lt_of_le_of_ne (((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _))
      (Ne.symm hne)
  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [← f.num_div_denom, div_eq_mul_inv, ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_mul hnum0 (inv_ne_zero hden0),
    ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_inv, hordn] at hord
  omega

theorem ratFuncDXCoeff_eq_zero_or_ord_nonneg_of_ord_nonneg {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {g : RatFunc K}
    (hg : g ≠ 0) (hord : 0 ≤ ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord g) :
    ratFuncDXCoeff K g = 0 ∨ 0 ≤ ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (ratFuncDXCoeff K g) := by
  rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hne
  · exact Or.inl h0
  refine Or.inr ?_
  have hW : g.num.derivative * g.denom - g.num * g.denom.derivative ≠ 0 :=
    wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero K hne
  have hW' : algebraMap K[X] (RatFunc K)
      (g.num.derivative * g.denom - g.num * g.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hW
  have hd' : algebraMap K[X] (RatFunc K) g.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero g.denom_ne_zero
  have hWord : 0 ≤ ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K)
      (g.num.derivative * g.denom - g.num * g.denom.derivative)) :=
    ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _)
  have hden : ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K) g.denom) = 0 :=
    ord_algebraMap_denom_eq_zero_of_ord_nonneg hp hwp hg hord
  have key : ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (ratFuncDXCoeff K g)
      = ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K)
          (g.num.derivative * g.denom - g.num * g.denom.derivative))
        - 2 * ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord (algebraMap K[X] (RatFunc K) g.denom) := by
    rw [ratFuncDXCoeff_def, div_eq_mul_inv,
      ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_mul hW' (inv_ne_zero (pow_ne_zero 2 hd')), ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_inv, ← zpow_natCast,
      ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)).ord_zpow]
    push_cast
    ring
  rw [key, hden]
  omega

end FinitePlaces


section PlaceInftySide

variable [DecidableEq (RatFunc K)]

theorem ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
    {f : RatFunc K} (hf : f ≠ 0) (hord : (placeInfty K).ord f = 1) :
    ratFuncDXCoeff K f ≠ 0 ∧ (placeInfty K).ord (ratFuncDXCoeff K f) = 2 := by
  obtain ⟨e, he0, heord, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hf hord
  rw [ratFuncDXCoeff_eq_of_D_eq_smul_dX hDe]
  exact ⟨he0, heord⟩

theorem ratFuncDXCoeff_eq_zero_or_two_le_ord_placeInfty_of_ord_nonneg
    {g : RatFunc K} (hg : g ≠ 0) (hord : 0 ≤ (placeInfty K).ord g) :
    ratFuncDXCoeff K g = 0 ∨ 2 ≤ (placeInfty K).ord (ratFuncDXCoeff K g) := by
  rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hne
  · exact Or.inl h0
  refine Or.inr ?_
  rcases eq_or_lt_of_le hord with heq | hlt
  ·
    obtain ⟨e, he, hDe⟩ := exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero hg heq.symm
    have hee := ratFuncDXCoeff_eq_of_D_eq_smul_dX hDe
    rcases he with rfl | h2
    · exact absurd hee hne
    · rw [hee]; exact h2
  ·
    have hW : g.num.derivative * g.denom - g.num * g.denom.derivative ≠ 0 :=
      wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero K hne
    have h := ord_placeInfty_ratFuncDXCoeff_ge hg hW
    omega

end PlaceInftySide


end DXCoeffIntegrality


section LemmaA

variable {K : Type*} [Field K] [CharZero K]

theorem ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    ratFuncDXCoeff K v.uniformizer ≠ 0 ∧
      (ratFuncDXCoeff K g = 0 ∨
        v.ord (ratFuncDXCoeff K v.uniformizer) ≤ v.ord (ratFuncDXCoeff K g)) := by
  classical
  have hg0 : 0 ≤ v.ord g := v.ord_nonneg_of_mem hg
  rcases eq_or_ne g 0 with rfl | hgne
  ·
    refine ⟨?_, Or.inl (ratFuncDXCoeff_zero (K := K))⟩
    rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
      exact (ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp hp.separable
        (Place.uniformizer_ne_zero _) (Place.ord_uniformizer _)).1
    · exact (ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
        ((placeInfty K).uniformizer_ne_zero) ((placeInfty K).ord_uniformizer)).1
  · rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    ·
      obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
      obtain ⟨hπne, hπord⟩ := ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        hp.separable (Place.uniformizer_ne_zero _) (Place.ord_uniformizer _)
      refine ⟨hπne, ?_⟩
      rcases ratFuncDXCoeff_eq_zero_or_ord_nonneg_of_ord_nonneg hp hwp hgne hg0 with h0 | hge
      · exact Or.inl h0
      · exact Or.inr (by rw [hπord]; exact hge)
    ·
      obtain ⟨hπne, hπord⟩ :=
        ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
          (f := (placeInfty K).uniformizer)
          ((placeInfty K).uniformizer_ne_zero) ((placeInfty K).ord_uniformizer)
      refine ⟨hπne, ?_⟩
      rcases ratFuncDXCoeff_eq_zero_or_two_le_ord_placeInfty_of_ord_nonneg hgne hg0
        with h0 | hge
      · exact Or.inl h0
      · exact Or.inr (by rw [hπord]; exact hge)

theorem differentialCoeff_D_eq_ratFuncDXCoeff_div (v : Place K (RatFunc K)) (f : RatFunc K)
    (hπ : ratFuncDXCoeff K v.uniformizer ≠ 0) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) f)
      = ratFuncDXCoeff K f / ratFuncDXCoeff K v.uniformizer :=
  v.differentialCoeff_unique (by
    rw [show v.dCoord = KaehlerDifferential.D K (RatFunc K) v.uniformizer from rfl,
      D_eq_ratFuncDXCoeff_smul_dX K v.uniformizer, D_eq_ratFuncDXCoeff_smul_dX K f,
      smul_smul, div_mul_cancel₀ _ hπ])

theorem differentialCoeff_D_mem_of_mem (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) g) ∈ v.toValuationSubring := by
  obtain ⟨hπne, hcase⟩ := ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le v hg
  rw [differentialCoeff_D_eq_ratFuncDXCoeff_div v g hπne]
  rcases hcase with h0 | hle
  · rw [h0, zero_div]; exact zero_mem _
  · rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hgne'
    · rw [h0, zero_div]; exact zero_mem _
    · refine v.mem_of_ord_nonneg (div_ne_zero hgne' hπne) ?_
      rw [div_eq_mul_inv, v.ord_mul hgne' (inv_ne_zero hπne), v.ord_inv]
      omega

end LemmaA


section ExactDifferentialEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

variable (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

open scoped AlgebraicCurve.Place.CanonicalLocalResidueDataK in
theorem CanonicalLocalResidueDataK.res_differentialCoeff_D_of_mem_poleSubmodule
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) (N : ℕ) {g : F} (hg : g ∈ v.poleSubmodule N) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F g)) = 0 := by
  induction N generalizing g with
  | zero =>

    have hg' : g ∈ v.toValuationSubring := by
      have h := (v.mem_poleSubmodule (n := 0) (f := g)).mp hg
      rwa [pow_zero, one_mul] at h
    exact R.res_of_mem _ (hint g hg')
  | succ N ih =>

    obtain ⟨c, hc⟩ := hsurj (v.laurentTailCoeff (N + 1) ⟨g, hg⟩)
    have hclift : IsLocalRing.residue _ (algebraMap K v.toValuationSubring c)
        = v.laurentTailCoeff (N + 1) ⟨g, hg⟩ := by
      rw [← hc, IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    have hrem : g - algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹ ∈ v.poleSubmodule N := by
      have h := v.laurentTail_remainder_mem_poleSubmodule hg hclift
      rwa [v.coe_algebraMap] at h

    have hpeel : R.res (v.differentialCoeff (KaehlerDifferential.D K F
        (algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹))) = 0 := by
      rw [Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero,
        v.differentialCoeff_smul, v.differentialCoeff_D_uniformizer_pow_inv,
        show algebraMap K F c * (-((N + 1 : ℕ) : F) * (v.uniformizer ^ (N + 2))⁻¹)
            = algebraMap K F (c * -((N + 1 : ℕ) : K)) * (v.uniformizer ^ ((N + 1) + 1))⁻¹ by
          rw [map_mul, _root_.map_neg, map_natCast]; ring]
      exact R.res_algebraMap_mul_uniformizer_pow_inv v (Nat.le_add_left 1 N) _

    have hsplit : R.res (v.differentialCoeff (KaehlerDifferential.D K F g))
        = R.res (v.differentialCoeff (KaehlerDifferential.D K F
            (g - algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹)))
          + R.res (v.differentialCoeff (KaehlerDifferential.D K F
            (algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹))) := by
      conv_lhs => rw [show g = (g - algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹)
          + algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹ by ring]
      rw [map_add, v.differentialCoeff_add'', map_add]
    rw [hsplit, ih hrem, hpeel, add_zero]

open scoped AlgebraicCurve.Place.CanonicalLocalResidueDataK in
theorem CanonicalLocalResidueDataK.res_differentialCoeff_D_of_surj
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) (g : F) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F g)) = 0 := by
  obtain ⟨N, hN⟩ := v.exists_mem_poleSubmodule g
  exact CanonicalLocalResidueDataK.res_differentialCoeff_D_of_mem_poleSubmodule v hsurj hint
    R N hN

open scoped AlgebraicCurve.Place.CanonicalLocalResidueDataK in
theorem CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_of_surj [CharZero K]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) (π' : F) {n : ℕ} (hn : 1 ≤ n) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (n + 1))⁻¹) = 0 := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn

  have hres : R.res (v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹))) = 0 :=
    CanonicalLocalResidueDataK.res_differentialCoeff_D_of_surj v hsurj hint R _

  have hpow : v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹))
      = -((m + 1 : ℕ) : F) * (((π') ^ (m + 2))⁻¹
          * v.differentialCoeff (KaehlerDifferential.D K F π')) := by
    rw [D_pow_succ_inv, v.differentialCoeff_smul]
    ring

  have hne : -(((m + 1 : ℕ) : F)) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, Nat.cast_eq_zero]
    omega

  have hkey : v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (1 + m + 1))⁻¹
      = (-((m + 1 : ℕ) : K))⁻¹
          • v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹)) := by
    rw [Algebra.smul_def, map_inv₀, _root_.map_neg, map_natCast, hpow,
      show 1 + m + 1 = m + 2 from by omega, inv_mul_cancel_left₀ hne]
    ring
  rw [hkey, map_smul, hres, smul_zero]

open scoped AlgebraicCurve.Place.CanonicalLocalResidueDataK in
theorem CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_of_integral
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) {π' : F} (hπ' : v.ord π' = 1) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * (π')⁻¹) = 1 := by
  have hπ'0 : π' ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ'
    exact zero_ne_one hπ'
  have hπv0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero

  set w : F := π' * (v.uniformizer)⁻¹ with hw_def
  have hw0 : w ≠ 0 := mul_ne_zero hπ'0 (inv_ne_zero hπv0)
  have hword : v.ord w = 0 := by
    rw [hw_def, v.ord_mul hπ'0 (inv_ne_zero hπv0), v.ord_inv, hπ', v.ord_uniformizer]
    ring
  have hwmem : w ∈ v.toValuationSubring := v.mem_of_ord_nonneg hw0 hword.ge
  have hwinvmem : w⁻¹ ∈ v.toValuationSubring := by
    refine v.mem_of_ord_nonneg (inv_ne_zero hw0) ?_
    rw [v.ord_inv, hword]
    omega

  have hπ'_eq : π' = v.uniformizer * w := by
    rw [hw_def, mul_comm π' (v.uniformizer)⁻¹, ← mul_assoc, mul_inv_cancel₀ hπv0, one_mul]

  have hD : KaehlerDifferential.D K F π'
      = v.uniformizer • KaehlerDifferential.D K F w
        + w • KaehlerDifferential.D K F v.uniformizer := by
    conv_lhs => rw [hπ'_eq]
    exact Derivation.leibniz _ _ _

  have hcoeff : v.differentialCoeff (KaehlerDifferential.D K F π')
      = v.uniformizer * v.differentialCoeff (KaehlerDifferential.D K F w) + w := by
    rw [hD, v.differentialCoeff_add'', v.differentialCoeff_smul, v.differentialCoeff_smul,
      show KaehlerDifferential.D K F v.uniformizer = v.dCoord from rfl,
      v.differentialCoeff_dCoord, mul_one]

  have hsplit : v.differentialCoeff (KaehlerDifferential.D K F π') * (π')⁻¹
      = v.differentialCoeff (KaehlerDifferential.D K F w) * w⁻¹ + (v.uniformizer)⁻¹ := by
    rw [hcoeff, hπ'_eq, mul_inv]
    field_simp
  rw [hsplit, map_add, gate_canonicalLocalResidueDataK_uniformizer_inv v R,
    R.res_of_mem _ (mul_mem (hint w hwmem) hwinvmem), zero_add]

end Place


end ExactDifferentialEngine


section RatFuncClauses

variable {K : Type*} [Field K] [CharZero K] [HasCanonicalLocalResidueKStar K (RatFunc K)]

theorem canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_ratFunc
    (v : Place K (RatFunc K)) (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (π' : RatFunc K) (R : v.CanonicalLocalResidueDataK) {n : ℕ} (hn : 1 ≤ n) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) π')
      * ((π') ^ (n + 1))⁻¹) = 0 :=
  Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_of_surj v hsurj
    (fun _ hh => differentialCoeff_D_mem_of_mem v hh) R π' hn

theorem canonicalLocalResidueDataK_res_differentialCoeff_D_mul_inv_ratFunc
    (v : Place K (RatFunc K)) {π' : RatFunc K} (hπ' : v.ord π' = 1)
    (R : v.CanonicalLocalResidueDataK) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) π') * (π')⁻¹) = 1 :=
  Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_of_integral v
    (fun _ hh => differentialCoeff_D_mem_of_mem v hh) R hπ'

end RatFuncClauses


theorem canonicalLocalResidueKSimplePoleCoordIndep_ratFunc (K : Type*) [Field K] [CharZero K]
    [HasCanonicalLocalResidueKStar K (RatFunc K)] :
    CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K) :=
  fun v _ hπ' R => canonicalLocalResidueDataK_res_differentialCoeff_D_mul_inv_ratFunc v hπ' R

section PlaceInftyConsumers

variable (K : Type*) [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]

theorem canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_placeInfty
    (π' : RatFunc K) (R : (placeInfty K).CanonicalLocalResidueDataK) {n : ℕ} (hn : 1 ≤ n) :
    R.res ((placeInfty K).differentialCoeff (KaehlerDifferential.D K (RatFunc K) π')
      * ((π') ^ (n + 1))⁻¹) = 0 :=
  canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_ratFunc (placeInfty K)
    (surjective_algebraMap_residueField_placeInfty K) π' R hn

theorem canonicalLocalResidueDataK_res_X_pow_mul_D_X
    (R : (placeInfty K).CanonicalLocalResidueDataK) (n : ℕ) :
    R.res ((RatFunc.X : RatFunc K) ^ n
        * (placeInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) RatFunc.X)) = 0 := by
  rw [X_pow_mul_differentialCoeff_D_X_eq_neg K n, _root_.map_neg, neg_eq_zero]
  exact canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_placeInfty K
    (RatFunc.X : RatFunc K)⁻¹ R (Nat.le_add_left 1 n)

theorem canonicalLocalResidueDataK_kaehlerResidueTerm_X_pow
    (R : (placeInfty K).CanonicalLocalResidueDataK) (n : ℕ) :
    Algebra.trace K (placeInfty K).ResidueField
        (R.res (diagonalHom K (RatFunc K) ((RatFunc.X : RatFunc K) ^ n) (placeInfty K)
          * (placeInfty K).differentialCoeff
              (KaehlerDifferential.D K (RatFunc K) RatFunc.X))) = 0 := by
  rw [diagonalHom_apply, canonicalLocalResidueDataK_res_X_pow_mul_D_X K R n, _root_.map_zero]

end PlaceInftyConsumers


section AlgClosedDischarge

variable (K : Type*) [Field K] [CharZero K] [HasCanonicalLocalResidueKStar K (RatFunc K)]

theorem surjective_algebraMap_residueField_of_deg_eq_one {F : Type*} [Field F] [Algebra K F]
    (v : Place K F) (hdeg : v.deg = 1) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  intro z
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp
    (show Module.finrank K v.ResidueField = 1 from hdeg) z
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

theorem surjective_algebraMap_residueField_ratFunc_of_isAlgClosed [IsAlgClosed K]
    (v : Place K (RatFunc K)) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  classical
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    refine surjective_algebraMap_residueField_of_deg_eq_one K _ ?_
    rw [deg_ofHeightOneSpectrum K hwp]
    have h := IsAlgClosed.degree_eq_one_of_irreducible K hp
    rw [degree_eq_natDegree hp.ne_zero] at h
    exact_mod_cast h
  · exact surjective_algebraMap_residueField_placeInfty K

variable [IsAlgClosed K]

theorem canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed :
    CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K) :=
  fun v π' _ R _ hn =>
    canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_ratFunc v
      (surjective_algebraMap_residueField_ratFunc_of_isAlgClosed K v) π' R hn

end AlgClosedDischarge


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end


section
section

noncomputable section

open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

section PerfectDCoord

variable (K : Type*) [Field K] [PerfectField K]

theorem exists_ne_zero_smul_dX_of_uniformizer (v : Place K (RatFunc K)) :
    ∃ c : RatFunc K, c ≠ 0 ∧
      KaehlerDifferential.D K (RatFunc K) v.uniformizer = c • dX K := by
  classical
  have hord : v.ord v.uniformizer = 1 := v.ord_uniformizer
  have hpi0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  ·
    obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    obtain ⟨hne, -⟩ := ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
      (PerfectField.separable_of_irreducible hp) hpi0 hord
    exact ⟨ratFuncDXCoeff K _, hne, D_eq_ratFuncDXCoeff_smul_dX K _⟩
  ·
    obtain ⟨e, he0, -, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hpi0 hord
    exact ⟨e, he0, hDe⟩

namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum residueFieldEquivOfHeightOneSpectrum deg_ofHeightOneSpectrum deg_finitePlace)

open _root_.AlgebraicCurve.RationalFunctionField

scoped instance (priority := low) instDCoordGeneratesPerfectField (v : Place K (RatFunc K)) :
    v.DCoordGenerates := by
  obtain ⟨c, hc0, hDc⟩ := exists_ne_zero_smul_dX_of_uniformizer K v
  refine ⟨?_⟩
  have hdc : v.dCoord = KaehlerDifferential.D K (RatFunc K) v.uniformizer := rfl
  rw [hdc, hDc, eq_top_iff, ← span_dX_eq_top K, Submodule.span_singleton_le_iff_mem]
  exact Submodule.mem_span_singleton.mpr
    ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩

end RationalFunctionField


end PerfectDCoord


section Profile

variable (K : Type*) [Field K]

section PerfectProfileValues

variable [PerfectField K] [DecidableEq (RatFunc K)]

theorem p1DifferentialCoeffUnitFinite_dX_of_perfectField :
    P1DifferentialCoeffUnitFinite K (dX_ne_zero K) := by
  intro v hvinf
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    exact ord_differentialCoeff_dX_ofHeightOneSpectrum hp hwp
      (PerfectField.separable_of_irreducible hp)
  · exact absurd rfl hvinf

theorem p1DifferentialCoeffRegularFinite_dX_of_perfectField :
    P1DifferentialCoeffRegularFinite K (dX_ne_zero K) :=
  p1DifferentialCoeffRegularFinite_of_unitFinite (dX_ne_zero K)
    (p1DifferentialCoeffUnitFinite_dX_of_perfectField K)

theorem ordDifferential_dX_of_ne_placeInfty_of_perfectField {v : Place K (RatFunc K)}
    (hv : v ≠ placeInfty K) : v.ordDifferential (dX K) = 0 := by
  rw [Place.ordDifferential]
  exact p1DifferentialCoeffUnitFinite_dX_of_perfectField K v hv

theorem ordDifferential_dX_placeInfty_of_perfectField :
    (placeInfty K).ordDifferential (dX K) = -2 :=
  ordDifferential_placeInfty_D_ratFuncX K
    (ordDifferentialWellDefined_ratFunc_of_perfectField K)

theorem exists_divisor_smul_dX_of_perfectField {c : RatFunc K} (hc : c ≠ 0) :
    ∃ D : Divisor K (RatFunc K),
      (∀ v : Place K (RatFunc K), D v = v.ordDifferential (c • dX K)) ∧
        Divisor.degree D = -2 := by
  obtain ⟨Dc, hDc, hDcdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (F := RatFunc K) c hc
  refine ⟨Dc + Finsupp.single (placeInfty K) (-2), fun v => ?_, ?_⟩
  ·
    rw [Finsupp.add_apply, hDc v,
      v.ordDifferential_smul hc (v.differentialCoeff_ne_zero (dX_ne_zero K))]
    rcases eq_or_ne v (placeInfty K) with rfl | hne
    · rw [ordDifferential_dX_placeInfty_of_perfectField K, Finsupp.single_eq_same]
    · rw [ordDifferential_dX_of_ne_placeInfty_of_perfectField K hne,
        Finsupp.single_eq_of_ne hne]
  ·
    rw [map_add, hDcdeg, zero_add, Divisor.degree_single, deg_placeInfty K, Nat.cast_one,
      mul_one]

end PerfectProfileValues


section PerfectInstance

variable [PerfectField K]

scoped instance instHasCanonicalDivisorRatFuncPerfectField :
    HasCanonicalDivisor (K := K) (F := RatFunc K) where
  exists_divisor ω hω := by
    classical
    obtain ⟨c, hc⟩ := exists_smul_dX_eq K ω
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hω hc.symm
    obtain ⟨D, hD, -⟩ := exists_divisor_smul_dX_of_perfectField K hc0
    refine ⟨D, fun v => ?_⟩
    rw [← hc]
    exact hD v

end PerfectInstance


section PerfectExactDivisor

variable [PerfectField K] [DecidableEq (RatFunc K)]

end PerfectExactDivisor


section CharZeroRoutes

variable [CharZero K]

end CharZeroRoutes


end Profile


section FiniteFieldReadings

end FiniteFieldReadings


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end

end


end


section
section

set_option maxHeartbeats 1600000

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

namespace ModularCurve

namespace MilneAvAg9bRd13T2CoordIndepChar3

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

theorem _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.ModularCurve.MilneAvAg9bRd13T2CoordIndepChar3.ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
    (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) (π' : F) {n : ℕ} (hn : 1 ≤ n)
    (hnK : (n : K) ≠ 0) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (n + 1))⁻¹) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hmK : ((m + 1 : ℕ) : K) ≠ 0 := by
    rwa [show m + 1 = 1 + m from by omega]

  have hres : R.res (v.differentialCoeff
      (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹))) = 0 :=
    Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_of_surj v hsurj hint R _

  have hpow : v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹))
      = -((m + 1 : ℕ) : F) * (((π') ^ (m + 2))⁻¹
          * v.differentialCoeff (KaehlerDifferential.D K F π')) := by
    rw [D_pow_succ_inv, v.differentialCoeff_smul]
    ring

  have hne : -(((m + 1 : ℕ) : F)) ≠ 0 := by
    rw [neg_ne_zero, ← map_natCast (algebraMap K F) (m + 1)]
    exact (map_ne_zero_iff _ (algebraMap K F).injective).mpr hmK

  have hkey : v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (1 + m + 1))⁻¹
      = (-((m + 1 : ℕ) : K))⁻¹
          • v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹)) := by
    rw [Algebra.smul_def, map_inv₀, _root_.map_neg, map_natCast, hpow,
      show 1 + m + 1 = m + 2 from by omega, inv_mul_cancel_left₀ hne]
    ring
  rw [hkey, map_smul, hres, smul_zero]




end MilneAvAg9bRd13T2CoordIndepChar3


end ModularCurve


end


end


end


section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

section ChoiceOpacity

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring mk.injEq rec ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk adicValuation_valuationSubring mem_iff_adicValuation_le_one isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one isEquiv_adicValuation_ofHeightOneSpectrum ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg deg_restrict_mul_inertiaDeg ord_neg mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq finite_setOf_restrict_eq)

open _root_.AlgebraicCurve.Place

section BumpConstruction

variable (v : Place K F)

end BumpConstruction


end Place


end ChoiceOpacity


section CanonicalKResidueTerm

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

section SupportMachinery

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]

variable (K F)

variable {K F}

section Bridge

variable [HasLocalResidue K F] [HasCanonicalLocalResidueKStar K F]

variable [Nontrivial Ω[F⁄K]]

end Bridge


end SupportMachinery


end CanonicalKResidueTerm


section RatFuncPlaceInftyClause

variable {K : Type*} [Field K] [CharZero K] [DecidableEq (RatFunc K)]

theorem residueTheoremK_placeInfty_clause_X_pow
    (Rfam : ∀ v : Place K (RatFunc K), v.CanonicalLocalResidueDataK) (n : ℕ) :
    kaehlerResidueTermKFam Rfam (KaehlerDifferential.D K (RatFunc K) RatFunc.X)
      (diagonalHom K (RatFunc K) ((RatFunc.X : RatFunc K) ^ n)) (placeInfty K) = 0 := by
  rw [kaehlerResidueTermKFam_apply]
  exact canonicalLocalResidueDataK_kaehlerResidueTerm_X_pow K (Rfam (placeInfty K)) n

end RatFuncPlaceInftyClause


section GenericGates

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

end GenericGates


section AlgClosedGate

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
  [HasCanonicalDivisor (K := K) (F := RatFunc K)]

end AlgClosedGate


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end


section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]

section EulerPerfectField

variable {p : K[X]} [Fact (Irreducible p)]

theorem ag9b12c_trace_root_pow_div_derivative_of_lt_of_perfectField (hpmon : p.Monic)
    {k : ℕ} (hk : k < p.natDegree - 1) :
    Algebra.trace K (AdjoinRoot p)
      (AdjoinRoot.root p ^ k / aeval (AdjoinRoot.root p) (derivative p)) = 0 := by
  haveI : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis
  have hmin : minpoly K (AdjoinRoot.powerBasis hpmon.ne_zero).gen = p :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hpmon
  have h := FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_of_lt
    (AdjoinRoot.powerBasis hpmon.ne_zero) (k := k)
    (by rwa [AdjoinRoot.powerBasis_dim])
  rwa [hmin, AdjoinRoot.powerBasis_gen] at h

theorem ag9b12c_trace_root_pow_div_derivative_self_of_perfectField (hpmon : p.Monic)
    (hd : 0 < p.natDegree) :
    Algebra.trace K (AdjoinRoot p)
      (AdjoinRoot.root p ^ (p.natDegree - 1) /
        aeval (AdjoinRoot.root p) (derivative p)) = 1 := by
  haveI : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis
  have hmin : minpoly K (AdjoinRoot.powerBasis hpmon.ne_zero).gen = p :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hpmon
  have h := FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_self
    (AdjoinRoot.powerBasis hpmon.ne_zero)
    (by rwa [AdjoinRoot.powerBasis_dim])
  rwa [hmin, AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim] at h

theorem ag9b12c_aeval_root_eq_sum_range {c : K[X]} {d : ℕ} (hd : c.natDegree < d) :
    (aeval (AdjoinRoot.root p) c : AdjoinRoot p)
      = ∑ k ∈ Finset.range d, c.coeff k • AdjoinRoot.root p ^ k := by
  rw [aeval_def, eval₂_eq_sum_range' (algebraMap K (AdjoinRoot p)) hd]
  exact Finset.sum_congr rfl fun k _ => (Algebra.smul_def _ _).symm

theorem ag9b12c_trace_adjoinRoot_mk_div_mk_derivative_of_perfectField (hpmon : p.Monic)
    {c : K[X]} (hdeg : c.degree < p.degree) :
    Algebra.trace K (AdjoinRoot p)
        (AdjoinRoot.mk p c / AdjoinRoot.mk p (derivative p))
      = c.coeff (p.natDegree - 1) := by
  haveI : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis
  have hpd : 0 < p.natDegree := (Fact.out : Irreducible p).natDegree_pos
  have hcd : c.natDegree < p.natDegree := by
    rcases eq_or_ne c 0 with rfl | hc
    · simpa using hpd
    · exact natDegree_lt_natDegree hc hdeg
  rw [← AdjoinRoot.aeval_eq, ← AdjoinRoot.aeval_eq,
    ag9b12c_aeval_root_eq_sum_range K hcd, Finset.sum_div, map_sum]
  trans ∑ k ∈ Finset.range p.natDegree,
      c.coeff k * Algebra.trace K (AdjoinRoot p)
        (AdjoinRoot.root p ^ k / aeval (AdjoinRoot.root p) (derivative p))
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, mul_div_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single (p.natDegree - 1)]
  · rw [ag9b12c_trace_root_pow_div_derivative_self_of_perfectField K hpmon hpd, mul_one]
  · intro k hk hkne
    have hk' : k < p.natDegree - 1 :=
      lt_of_le_of_ne (Nat.le_sub_one_of_lt (Finset.mem_range.mp hk)) hkne
    rw [ag9b12c_trace_root_pow_div_derivative_of_lt_of_perfectField K hpmon hk', mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.sub_lt hpd one_pos)) h

end EulerPerfectField


section DerivativeRegular

theorem ag9b12c_differentialCoeff_add (v : Place K (RatFunc K))
    (ω₁ ω₂ : Ω[(RatFunc K)⁄K]) :
    v.differentialCoeff (ω₁ + ω₂) = v.differentialCoeff ω₁ + v.differentialCoeff ω₂ :=
  v.differentialCoeff_unique
    (by rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

theorem ag9b12c_differentialCoeff_D_mem_finitePlace {p : K[X]} (hpirr : Irreducible p)
    {f : RatFunc K} (hf : f ∈ (finitePlace K hpirr).toValuationSubring) :
    (finitePlace K hpirr).differentialCoeff (D K (RatFunc K) f)
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  set ξ : K[X] := f.num.derivative * f.denom - f.num * f.denom.derivative
  have hd0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hcoeff : v.differentialCoeff (D K (RatFunc K) f)
      = algebraMap K[X] (RatFunc K) ξ * ((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
          * v.differentialCoeff (dX K) := by
    have hkey := denom_sq_smul_D_eq K f
    refine v.differentialCoeff_unique ?_
    rw [mul_smul, v.differentialCoeff_smul_dCoord, mul_comm, mul_smul, ← hkey, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hd0), one_smul]
  rw [hcoeff]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact algebraMap_mem_ofHeightOneSpectrum K _ ξ
  · have hden_notmem : f.denom ∉ (heightOneSpectrumOfIrreducible K hpirr).asIdeal :=
      denom_notMem_of_mem_ofHeightOneSpectrum K _ hf
    have hordd : v.ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
      by_contra h
      exact hden_notmem ((Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K)
        (F := RatFunc K) _ f.denom_ne_zero).mp h)
    refine v.mem_of_ord_nonneg (inv_ne_zero (pow_ne_zero 2 hd0)) ?_
    rw [v.ord_inv, ← zpow_natCast, v.ord_zpow, hordd, mul_zero, _root_.neg_zero]
  · exact v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
      (ord_differentialCoeff_dX_ofHeightOneSpectrum hpirr
        (heightOneSpectrumOfIrreducible_asIdeal K hpirr)
        (PerfectField.separable_of_irreducible hpirr)).ge

end DerivativeRegular


section LeibnizCore

theorem ag9b12c_uniformizer_div_mem_finitePlace {p : K[X]} (hpirr : Irreducible p) :
    (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero
  refine v.mem_of_ord_nonneg (div_ne_zero v.uniformizer_ne_zero hp0) ?_
  rw [div_eq_mul_inv, v.ord_mul v.uniformizer_ne_zero (inv_ne_zero hp0), v.ord_inv,
    v.ord_uniformizer, ord_finitePlace_self K hpirr]
  omega

theorem ag9b12c_one_sub_uniformizer_div_mul_differentialCoeff_D
    {p : K[X]} (hpirr : Irreducible p) :
    (1 : RatFunc K) - (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
        * (finitePlace K hpirr).differentialCoeff
            (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
      = algebraMap K[X] (RatFunc K) p
          * (finitePlace K hpirr).differentialCoeff
              (D K (RatFunc K) ((finitePlace K hpirr).uniformizer
                / algebraMap K[X] (RatFunc K) p)) := by
  set v := finitePlace K hpirr
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hpirr.ne_zero
  have hleib : D K (RatFunc K) v.uniformizer
      = (v.uniformizer / algebraMap K[X] (RatFunc K) p)
            • D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)
        + algebraMap K[X] (RatFunc K) p
            • D K (RatFunc K) (v.uniformizer / algebraMap K[X] (RatFunc K) p) := by
    have h := (D K (RatFunc K)).leibniz (a := v.uniformizer / algebraMap K[X] (RatFunc K) p)
      (b := algebraMap K[X] (RatFunc K) p)
    rw [div_mul_cancel₀ _ hp0] at h
    exact h
  have h1 : (1 : RatFunc K)
      = (v.uniformizer / algebraMap K[X] (RatFunc K) p)
            * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
        + algebraMap K[X] (RatFunc K) p
            * v.differentialCoeff
                (D K (RatFunc K) (v.uniformizer / algebraMap K[X] (RatFunc K) p)) := by
    have hcoord : D K (RatFunc K) v.uniformizer = v.dCoord := rfl
    rw [← v.differentialCoeff_dCoord, ← hcoord, hleib, ag9b12c_differentialCoeff_add K,
      v.differentialCoeff_smul, v.differentialCoeff_smul]
  linear_combination h1

theorem ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace
    {p : K[X]} (hpirr : Irreducible p) :
    (finitePlace K hpirr).uniformizer / algebraMap K[X] (RatFunc K) p
        * (finitePlace K hpirr).differentialCoeff
            (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))
      ∈ (finitePlace K hpirr).toValuationSubring := by
  set v := finitePlace K hpirr
  refine mul_mem (ag9b12c_uniformizer_div_mem_finitePlace K hpirr) ?_
  rw [differentialCoeff_D_algebraMap_polynomial K]
  exact mul_mem (algebraMap_mem_ofHeightOneSpectrum K _ p.derivative)
    (v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero (dX_ne_zero K))
      (ord_differentialCoeff_dX_ofHeightOneSpectrum hpirr
        (heightOneSpectrumOfIrreducible_asIdeal K hpirr)
        (PerfectField.separable_of_irreducible hpirr)).ge)

theorem ag9b12c_residue_uniformizer_div_mul_differentialCoeff_D_eq_one
    {p : K[X]} (hpirr : Irreducible p) :
    IsLocalRing.residue _
        ⟨_, ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩
      = (1 : (finitePlace K hpirr).ResidueField) := by
  set v := finitePlace K hpirr
  rw [← sub_eq_zero, show (1 : v.ResidueField) = IsLocalRing.residue _ 1 by simp,
    ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have hsubmem : (1 : RatFunc K) - (v.uniformizer / algebraMap K[X] (RatFunc K) p
      * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        ∈ v.toValuationSubring :=
    sub_mem (one_mem _)
      (ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr)
  have hcoe : (⟨_, ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩
        - 1 : v.toValuationSubring)
      = -⟨_, hsubmem⟩ :=
    Subtype.ext (by push_cast; ring)
  rw [hcoe]
  refine neg_mem ?_
  have herr : (1 : RatFunc K) - (v.uniformizer / algebraMap K[X] (RatFunc K) p
      * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        = algebraMap K[X] (RatFunc K) p
          * v.differentialCoeff (D K (RatFunc K)
              (v.uniformizer / algebraMap K[X] (RatFunc K) p)) :=
    ag9b12c_one_sub_uniformizer_div_mul_differentialCoeff_D K hpirr
  have hpmem : (⟨algebraMap K[X] (RatFunc K) p, algebraMap_mem_ofHeightOneSpectrum K _ p⟩
      : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [Place.mem_maximalIdeal_iff_adicValuation_lt_one]
    refine (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) (heightOneSpectrumOfIrreducible K hpirr)).lt_one_iff_lt_one.mp ?_
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ p).mpr
      (Ideal.mem_span_singleton_self p)
  have hregmem : v.differentialCoeff (D K (RatFunc K)
        (v.uniformizer / algebraMap K[X] (RatFunc K) p)) ∈ v.toValuationSubring :=
    ag9b12c_differentialCoeff_D_mem_finitePlace K hpirr
      (ag9b12c_uniformizer_div_mem_finitePlace K hpirr)
  have hprod : (⟨_, hsubmem⟩ : v.toValuationSubring)
      = ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ p⟩ * ⟨_, hregmem⟩ :=
    Subtype.ext herr
  rw [hprod]
  exact Ideal.mul_mem_right _ _ hpmem

end LeibnizCore


section BridgeDischarge

theorem ag9b12c_residue_algebraMap_derivative_ne_zero {p : K[X]} (hpirr : Irreducible p) :
    IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) p.derivative,
        algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩
      ≠ (0 : (finitePlace K hpirr).ResidueField) := by
  rw [ne_eq, IsLocalRing.residue_eq_zero_iff,
    Place.mem_maximalIdeal_iff_adicValuation_lt_one]
  intro hlt
  have hlt' := (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
    (F := RatFunc K) (heightOneSpectrumOfIrreducible K hpirr)).lt_one_iff_lt_one.mpr hlt
  rw [HeightOneSpectrum.valuation_lt_one_iff_mem,
    heightOneSpectrumOfIrreducible_asIdeal K hpirr, Ideal.mem_span_singleton] at hlt'
  exact hpirr.not_isUnit
    ((PerfectField.separable_of_irreducible hpirr).isUnit_of_dvd' dvd_rfl hlt')

theorem ag9b12c_simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne
    {p c : K[X]} (hpirr : Irreducible p)
    (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule) :
    (finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩
      = IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) c,
            algebraMap_mem_ofHeightOneSpectrum K _ c⟩
        / IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) p.derivative,
            algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩ := by
  set v := finitePlace K hpirr
  rw [Place.simplePoleResidueAux_apply,
    eq_div_iff (ag9b12c_residue_algebraMap_derivative_ne_zero K hpirr)]
  have hkey : (v.uniformizer * (p1PrincipalPartAtom K p c 1 * v.differentialCoeff (dX K)))
        * algebraMap K[X] (RatFunc K) p.derivative
      = algebraMap K[X] (RatFunc K) c
        * (v.uniformizer / algebraMap K[X] (RatFunc K) p
            * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p))) := by
    rw [differentialCoeff_D_algebraMap_polynomial K]
    show v.uniformizer
        * (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ 1
            * v.differentialCoeff (dX K))
        * algebraMap K[X] (RatFunc K) (derivative p)
      = algebraMap K[X] (RatFunc K) c
        * (v.uniformizer / algebraMap K[X] (RatFunc K) p
            * (algebraMap K[X] (RatFunc K) (derivative p) * v.differentialCoeff (dX K)))
    rw [pow_one, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
    ring_nf
  have hLHSmem : v.uniformizer * (p1PrincipalPartAtom K p c 1 * v.differentialCoeff (dX K))
      * algebraMap K[X] (RatFunc K) p.derivative ∈ v.toValuationSubring :=
    mul_mem hfmem (algebraMap_mem_ofHeightOneSpectrum K _ p.derivative)
  have hRHSmem : algebraMap K[X] (RatFunc K) c
      * (v.uniformizer / algebraMap K[X] (RatFunc K) p
          * v.differentialCoeff (D K (RatFunc K) (algebraMap K[X] (RatFunc K) p)))
        ∈ v.toValuationSubring :=
    mul_mem (algebraMap_mem_ofHeightOneSpectrum K _ c)
      (ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr)
  calc IsLocalRing.residue _ ⟨_, hfmem⟩ * IsLocalRing.residue _ ⟨_,
          algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩
      = IsLocalRing.residue _ (⟨_, hfmem⟩ * ⟨_,
          algebraMap_mem_ofHeightOneSpectrum K _ p.derivative⟩) := (map_mul _ _ _).symm
    _ = IsLocalRing.residue _ ⟨_, hLHSmem⟩ :=
        congrArg (IsLocalRing.residue _) (Subtype.ext rfl)
    _ = IsLocalRing.residue _ ⟨_, hRHSmem⟩ :=
        congrArg (IsLocalRing.residue _) (Subtype.ext hkey)
    _ = IsLocalRing.residue _ (⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩
          * ⟨_, ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩) :=
        congrArg (IsLocalRing.residue _) (Subtype.ext rfl)
    _ = IsLocalRing.residue _ ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩
          * IsLocalRing.residue _
              ⟨_, ag9b12c_uniformizer_div_mul_differentialCoeff_D_mem_finitePlace K hpirr⟩ :=
        map_mul _ _ _
    _ = IsLocalRing.residue _ ⟨_, algebraMap_mem_ofHeightOneSpectrum K _ c⟩ := by
        rw [ag9b12c_residue_uniformizer_div_mul_differentialCoeff_D_eq_one K hpirr, mul_one]

theorem ag9b12c_p1FinitePlaceSimplePoleResidueAdjoinRootValue_of_perfectField :
    P1FinitePlaceSimplePoleResidueAdjoinRootValue K := by
  intro p c _ hpirr _
  letI : Fact (Irreducible p) := ⟨hpirr⟩
  intro hfmem
  rw [ag9b12c_simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne K hpirr hfmem,
    AlgEquiv.symm_apply_eq, map_div₀,
    finitePlaceResidueFieldAlgEquivAdjoinRoot_mk K hpirr c,
    finitePlaceResidueFieldAlgEquivAdjoinRoot_mk K hpirr p.derivative]

end BridgeDischarge


section TraceValue

theorem ag9b12c_trace_finitePlace_simplePoleResidue_mOne_of_perfectField
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p) (hdeg : c.degree < p.degree)
    (hfmem : p1PrincipalPartAtom K p c 1 * (finitePlace K hpirr).differentialCoeff (dX K)
        ∈ (finitePlace K hpirr).simplePoleSubmodule) :
    Algebra.trace K (finitePlace K hpirr).ResidueField
        ((finitePlace K hpirr).simplePoleResidueAux ⟨_, hfmem⟩)
      = c.coeff (p.natDegree - 1) := by
  haveI : Fact (Irreducible p) := ⟨hpirr⟩
  have hval := ag9b12c_p1FinitePlaceSimplePoleResidueAdjoinRootValue_of_perfectField K
    p c hpmon hpirr hdeg
  rw [trace_finitePlace_residueField_eq_trace_adjoinRoot K hpirr, hval hfmem,
    ag9b12c_trace_adjoinRoot_mk_div_mk_derivative_of_perfectField K hpmon hdeg]

theorem ag9b12c_p1MOneSimplePoleCancel_dX_of_inftyEulerValue_of_perfectField
    (hinf : P1PlaceInftySimplePoleResidueEulerValue K) :
    P1PrincipalPartMOneSimplePoleCancel K (dX_ne_zero K) := by
  intro p c hpmon hpirr hdeg hfmem himem
  rw [ag9b12c_trace_finitePlace_simplePoleResidue_mOne_of_perfectField K
      hpmon hpirr hdeg hfmem,
    hinf p c hpmon hpirr hdeg himem, add_neg_cancel]

end TraceValue


end AlgebraicCurve


end

end


end


section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.deg Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ord_smul Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.toValuationSubring Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff IsCurveOver Place.ordDifferential Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply adeleSpace diagonal_mem_adeleSpace HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasLocalResidue HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg weilOfKaehlerK weilOfKaehlerK_apply ResidueTheoremK Place.finite_setOf_restrict_eq)

open _root_.AlgebraicCurve

open scoped Polynomial P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Polynomial

open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

section LemmaAPerfect

variable {K : Type*} [Field K] [PerfectField K]

theorem ag9b13e_ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le_of_perfectField
    (v : Place K (RatFunc K)) {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    ratFuncDXCoeff K v.uniformizer ≠ 0 ∧
      (ratFuncDXCoeff K g = 0 ∨
        v.ord (ratFuncDXCoeff K v.uniformizer) ≤ v.ord (ratFuncDXCoeff K g)) := by
  classical
  have hg0 : 0 ≤ v.ord g := v.ord_nonneg_of_mem hg
  rcases eq_or_ne g 0 with rfl | hgne
  · refine ⟨?_, Or.inl (ratFuncDXCoeff_zero (K := K))⟩
    rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
      exact (ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp)
        (Place.uniformizer_ne_zero _) (Place.ord_uniformizer _)).1
    · exact (ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
        ((placeInfty K).uniformizer_ne_zero) ((placeInfty K).ord_uniformizer)).1
  · rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    ·
      obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
      obtain ⟨hπne, hπord⟩ := ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp)
        (Place.uniformizer_ne_zero _) (Place.ord_uniformizer _)
      refine ⟨hπne, ?_⟩
      rcases ratFuncDXCoeff_eq_zero_or_ord_nonneg_of_ord_nonneg hp hwp hgne hg0 with h0 | hge
      · exact Or.inl h0
      · exact Or.inr (by rw [hπord]; exact hge)
    ·
      obtain ⟨hπne, hπord⟩ :=
        ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
          (f := (placeInfty K).uniformizer)
          ((placeInfty K).uniformizer_ne_zero) ((placeInfty K).ord_uniformizer)
      refine ⟨hπne, ?_⟩
      rcases ratFuncDXCoeff_eq_zero_or_two_le_ord_placeInfty_of_ord_nonneg hgne hg0
        with h0 | hge
      · exact Or.inl h0
      · exact Or.inr (by rw [hπord]; exact hge)

theorem ag9b13e_differentialCoeff_D_eq_ratFuncDXCoeff_div_of_perfectField
    (v : Place K (RatFunc K)) (f : RatFunc K)
    (hπ : ratFuncDXCoeff K v.uniformizer ≠ 0) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) f)
      = ratFuncDXCoeff K f / ratFuncDXCoeff K v.uniformizer :=
  v.differentialCoeff_unique (by
    rw [show v.dCoord = KaehlerDifferential.D K (RatFunc K) v.uniformizer from rfl,
      D_eq_ratFuncDXCoeff_smul_dX K v.uniformizer, D_eq_ratFuncDXCoeff_smul_dX K f,
      smul_smul, div_mul_cancel₀ _ hπ])

theorem ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) g) ∈ v.toValuationSubring := by
  obtain ⟨hπne, hcase⟩ :=
    ag9b13e_ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le_of_perfectField v hg
  rw [ag9b13e_differentialCoeff_D_eq_ratFuncDXCoeff_div_of_perfectField v g hπne]
  rcases hcase with h0 | hle
  · rw [h0, zero_div]; exact zero_mem _
  · rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hgne'
    · rw [h0, zero_div]; exact zero_mem _
    · refine v.mem_of_ord_nonneg (div_ne_zero hgne' hπne) ?_
      rw [div_eq_mul_inv, v.ord_mul hgne' (inv_ne_zero hπne), v.ord_inv]
      omega

end LemmaAPerfect


section SimplePoleRowPerfect

variable (K : Type*) [Field K] [PerfectField K]

theorem ag9b13e_canonicalLocalResidueKSimplePoleCoordIndep_ratFunc_of_perfectField :
    CanonicalLocalResidueKSimplePoleCoordIndep K (RatFunc K) :=
  fun v _ hπ' R =>
    Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_of_integral v
      (fun _ hh => ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField v hh) R hπ'

end SimplePoleRowPerfect


section ChainPerfect

variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]

theorem ag9b13e_p1PlaceInftySimplePoleResidueEulerValueX_of_perfectField :
    P1PlaceInftySimplePoleResidueEulerValueX K :=
  p1PlaceInftySimplePoleResidueEulerValueX_of_simplePoleCoordIndep K
    (ag9b13e_canonicalLocalResidueKSimplePoleCoordIndep_ratFunc_of_perfectField K)

theorem ag9b13e_p1PlaceInftySimplePoleResidueEulerValueMonomial_of_perfectField :
    P1PlaceInftySimplePoleResidueEulerValueMonomial K :=
  p1PlaceInftySimplePoleResidueEulerValueMonomial_of_X K
    (ordDifferential_dX_placeInfty_of_perfectField K)
    (ag9b13e_p1PlaceInftySimplePoleResidueEulerValueX_of_perfectField K)

theorem ag9b13e_p1PlaceInftySimplePoleResidueEulerValue_of_perfectField :
    P1PlaceInftySimplePoleResidueEulerValue K :=
  p1PlaceInftySimplePoleResidueEulerValue_of_monomial K
    (ordDifferential_dX_placeInfty_of_perfectField K)
    (ag9b13e_p1PlaceInftySimplePoleResidueEulerValueMonomial_of_perfectField K)

end ChainPerfect


end AlgebraicCurve


namespace ModularCurve

namespace MilneAvAg9bRd13X113FourRowUpgrade

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenPlaneModel
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenPicZeroFibreDiamond
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenPicZeroLiteralChordChain
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenPicZeroPlaceDictionary
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenPicZeroPlaceDictionary.PlaceConstruction
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenPicZeroLitPic0Comparison
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenX113RiemannRochRows
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MazurTate1973Mt31b
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenX113PackageHeldRowOne
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MilneAvAg9bRd9DictionaryHeld3Closure
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenX113OrdRowWellDefinedReduction
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MilneAvAg9bRd10EllKFinUpperRow
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MilneAvAg9bRd11X113TowerPowerBasis
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.Ag9b11bX113HwdUnitDischarge
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MilneAvAg9bRd11DictionaryBinderShrink
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MilneAvAg9bRd12X113AssemblyRetirement
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MilneAvAg9bRd12T1P1InftyResidue
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MilneAvAg9bRd12X113LocalDatumMint
open _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.MilneAvAg9bRd12X113FiveRowUpgrade

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

end MilneAvAg9bRd13X113FourRowUpgrade


end ModularCurve


end


end


end

end P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed
