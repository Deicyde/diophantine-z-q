import ZInQKernel.Contrib.NeronC.NMPInjective
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.OpenFibre
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric3.ChartCoordinates
import ZInQKernel.Contrib.OneProof.RC.X0Branch.Model

/-! The pinned source of the detector parametrization, tex 8476–8479.
The pullback and function-field transport are on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits ModularCurve
open WeierstrassCurve.ModelTorsion WeierstrassCurve.ModelLevels
  WeierstrassCurve.ModelLevels.ModelGeneric WeierstrassCurve.ModelLevels.ModelGeneric2
  ZInQ.Contrib.CloudW07JacobiansCurves

namespace ZInQ.Manuscript.RC.ModelNeron

open ZInQ.Contrib.NeronC (isSchemeTheoreticallyDominant_spec_map)
open private chart_mem_finiteChart finiteChart_affine from
  ZInQKernel.Contrib.OneProof.RC.X0Model3.AffineEval
open private genericJ_isFractionRing from
  ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.AffineComparison
open private section_fieldComparison from
  ZInQKernel.Contrib.OneProof.RC.ModelGeneric3.ChartCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] X0Model.jAlgebra X0Model.finite_jAlgebra

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N]
  (h₅ : 5 ≤ ell) (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)

/-- The canonical closed-point map of the detector ring. -/
def closed (ell : ℕ) [Fact ell.Prime] : LocalIntegers ell →+* ZMod ell :=
  IsLocalization.lift (M := (integerPrimeIdeal ell).primeCompl)
    (g := Int.castRingHom (ZMod ell)) fun s => by
      apply isUnit_iff_ne_zero.mpr
      intro he
      exact s.property (by
        simpa [integerPrimeIdeal, Ideal.mem_span_singleton, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
          using he)

/-- The affine integral source is separated. -/
theorem separatedM : IsSeparated (Pinned.Y0Level h₅ htame h₂).hom := by
  change IsSeparated (Spec.map (CommRingCat.ofHom (S := ↥(Pinned.Y0LevelAlgebra h₅ htame h₂))
    (algebraMap (LocalIntegers ell) (Pinned.Y0LevelAlgebra h₅ htame h₂))))
  infer_instance

private theorem schematicallyDenseGeneric :
    IsSchemeTheoreticallyDominant (pullback.fst (Pinned.Y0Level h₅ htame h₂).hom
      (detectorRationalPoint (ell := ell))) := by
  letI := rational_isFractionRing ell
  haveI : IsSchemeTheoreticallyDominant (detectorRationalPoint (ell := ell)) :=
    isSchemeTheoreticallyDominant_spec_map _
      (IsFractionRing.injective (LocalIntegers ell) ℚ)
  haveI : QuasiCompact (detectorRationalPoint (ell := ell)) := by
    unfold detectorRationalPoint
    infer_instance
  haveI := Pinned.Y0Level_smooth h₅ htame h₂
  infer_instance

/-- The generic fibre is dense by flat base change from the fraction-field inclusion. -/
theorem denseGeneric :
    IsDominant (pullback.fst (Pinned.Y0Level h₅ htame h₂).hom
      (detectorRationalPoint (ell := ell))) := by
  letI := schematicallyDenseGeneric h₅ htame h₂
  infer_instance

/-- The pinned rational identification in the order of factors used by `generic`. -/
def genericIso :
    (Over.pullback (detectorRationalPoint (ell := ell))).obj (Pinned.Y0Level h₅ htame h₂) ≅
      Y0Rational h₂ := by
  let f := (Pinned.Y0Level h₅ htame h₂).hom
  let g := detectorRationalPoint (ell := ell)
  refine Over.isoMk (f := Over.mk (pullback.snd f g)) (g := Over.mk (pullback.fst g f))
    (pullbackSymmetry f g) (pullbackSymmetry_hom_comp_fst _ _) ≪≫
      Y0RationalFibreIso h₅ htame h₂

/-- The fixed compact curve viewed over the rationals. -/
abbrev compact (N : ℕ) [NeZero N] : Over (Spec (.of ℚ)) :=
  Over.mk (X0Branch.model N).overQ

/-- The pinned generic fibre maps to the compact curve through the actual finite chart. -/
def incl :
    (Over.pullback (detectorRationalPoint (ell := ell))).obj (Pinned.Y0Level h₅ htame h₂) ⟶ compact N :=
  (genericIso h₅ htame h₂).hom ≫ (rationalOpenIsoOverQ h₂).hom ≫
    Over.homMk (X0Model3.finiteChart N).ι rfl

theorem incl_left :
    (incl h₅ htame h₂).left =
      (genericIso h₅ htame h₂).hom.left ≫ rationalOpenImmersion h₂ := by
  change _ ≫ (rationalOpenIso h₂).hom ≫ (X0Model3.finiteChart N).ι = _
  rw [rationalOpenIso_hom_comp]

theorem openIncl : IsOpenImmersion (incl h₅ htame h₂).left := by
  rw [incl_left]
  haveI := rationalOpenImmersion_isOpen h₂
  infer_instance

theorem denseIncl : IsDominant (incl h₅ htame h₂).left := by
  haveI : IsIntegral (compact N).left := (X0Branch.model N).integral
  haveI : IsOpenImmersion (incl h₅ htame h₂).left := openIncl h₅ htame h₂
  haveI : Nonempty (branchFiniteOverQ N).left := ⟨⟨_, chart_mem_finiteChart N default⟩⟩
  let e := genericIso h₅ htame h₂ ≪≫ rationalOpenIsoOverQ h₂
  haveI : Nonempty ((Over.pullback (detectorRationalPoint (ell := ell))).obj
      (Pinned.Y0Level h₅ htame h₂)).left :=
    ⟨e.inv.left (Classical.choice inferInstance)⟩
  exact ⟨(incl h₅ htame h₂).left.isOpenMap.denseRange_of_isPreirreducibleSpace _⟩

/-- Reducedness descends from the rational open along the schematically dense generic fibre. -/
theorem reducedM : IsReduced (Pinned.Y0Level h₅ htame h₂).left := by
  letI : IsIntegral (compact N).left := (X0Branch.model N).integral
  letI : IsOpenImmersion (incl h₅ htame h₂).left := openIncl h₅ htame h₂
  letI : IsReduced (pullback (Pinned.Y0Level h₅ htame h₂).hom
      (detectorRationalPoint (ell := ell))) :=
    isReduced_of_isOpenImmersion (incl h₅ htame h₂).left
  letI := schematicallyDenseGeneric h₅ htame h₂
  haveI : QuasiCompact (detectorRationalPoint (ell := ell)) := by
    unfold detectorRationalPoint
    infer_instance
  exact IsSchemeTheoreticallyDominant.isReduced
    (pullback.fst (Pinned.Y0Level h₅ htame h₂).hom (detectorRationalPoint (ell := ell)))


/-- Pullback on fraction fields through the section equivalence of the actual open. -/
def toModuliField :
    (X0Model.curve N).functionField ≃+* Y0RationalGenericJ h₂ := by
  letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
  letI := genericJ_isFractionRing h₂
  letI : Nonempty (X0Model3.finiteChart N) := ⟨⟨_, chart_mem_finiteChart N default⟩⟩
  letI := functionField_isFractionRing_of_isAffineOpen _ _ (finiteChart_affine N)
  exact IsFractionRing.ringEquivOfRingEquiv (rationalChartSections h₂).val

/-- The actual source invariant, transported from the moduli function field. -/
def sourceJ : (X0Model.curve N).functionField :=
  (toModuliField h₂).symm (Y0RationalGenericJInclusion h₂ (Y0RationalJ h₂))

/-- The descended invariant of the actual iterated Vélu quotient, transported to the compact curve. -/
def quotientJ : (X0Model.curve N).functionField :=
  (toModuliField h₂).symm (Y0RationalGenericQuotientJ h₂)

/-- The field comparison from the generic moduli quotient to the fixed Laurent field. -/
def chartField : (X0Model.curve N).functionField ≃+* modularFunctionField N :=
  (toModuliField h₂).trans
    (genericModularFieldEquiv h₂ (Classical.choice (nonempty_modularPolynomialData N))).toRingEquiv

theorem chart_sourceJ : chartField h₂ (sourceJ h₂) = ⟨jq, jq_mem N⟩ := by
  change genericModularFieldEquiv h₂ (Classical.choice (nonempty_modularPolynomialData N))
    (toModuliField h₂ ((toModuliField h₂).symm _)) = _
  rw [RingEquiv.apply_symm_apply]
  letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
  rw [← show (Y0RationalJMap h₂) (Polynomial.X : Polynomial ℚ) = Y0RationalJ h₂ from
    Polynomial.aeval_X _]
  change genericModularFieldEquiv h₂ (Classical.choice (nonempty_modularPolynomialData N))
    ((Algebra.TensorProduct.includeRight (R := Polynomial ℚ) (A := LeafModCurves.Qj)
      (B := Y0RationalAlgebra h₂)) (algebraMap (Polynomial ℚ) (Y0RationalAlgebra h₂)
        Polynomial.X)) = _
  have hj := DFunLike.congr_fun
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := Polynomial ℚ) (A := LeafModCurves.Qj) (B := Y0RationalAlgebra h₂))
    (Polynomial.X : Polynomial ℚ)
  change algebraMap LeafModCurves.Qj (Y0RationalGenericJ h₂)
    (algebraMap (Polynomial ℚ) LeafModCurves.Qj Polynomial.X) =
      (Algebra.TensorProduct.includeRight (R := Polynomial ℚ) (A := LeafModCurves.Qj)
        (B := Y0RationalAlgebra h₂)) (algebraMap (Polynomial ℚ) (Y0RationalAlgebra h₂)
          Polynomial.X) at hj
  rw [← hj, RatFunc.algebraMap_X]
  exact genericModularFieldEquiv_j h₂ _

theorem chart_quotientJ : chartField h₂ (quotientJ h₂) = ⟨jqN N, jqN_mem N⟩ := by
  change genericModularFieldEquiv h₂ (Classical.choice (nonempty_modularPolynomialData N))
    (toModuliField h₂ ((toModuliField h₂).symm _)) = _
  rw [RingEquiv.apply_symm_apply]
  exact genericModularFieldEquiv_quotientJ h₂ _

/-- Section compatibility on the finite chart determines the entire field comparison. -/
theorem chartField_eq : chartField h₂ = X0Model.functionField N := by
  let U := X0Model3.finiteChart N
  letI : Nonempty U := ⟨⟨_, chart_mem_finiteChart N default⟩⟩
  letI := functionField_isFractionRing_of_isAffineOpen _ _ (finiteChart_affine N)
  apply RingEquiv.toRingHom_injective
  apply IsFractionRing.ringHom_ext (A := Γ(X0Model.curve N, U))
  intro s
  letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
  letI := genericJ_isFractionRing h₂
  have hs := IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (K := (X0Model.curve N).functionField) (L := Y0RationalGenericJ h₂)
    (rationalChartSections h₂).val s
  change toModuliField h₂ ((X0Model.curve N).germToFunctionField U s) =
    Y0RationalGenericJInclusion h₂ ((rationalChartSections h₂).val s) at hs
  change genericModularFieldEquiv h₂ (Classical.choice (nonempty_modularPolynomialData N)) (toModuliField h₂
    ((X0Model.curve N).germToFunctionField U s)) = _
  rw [hs]
  exact (section_fieldComparison h₂ s).symm

#print axioms closed
#print axioms separatedM
#print axioms reducedM
#print axioms schematicallyDenseGeneric
#print axioms denseGeneric
#print axioms genericIso
#print axioms compact
#print axioms incl
#print axioms incl_left
#print axioms openIncl
#print axioms denseIncl
#print axioms toModuliField
#print axioms sourceJ
#print axioms quotientJ
#print axioms chartField
#print axioms chart_sourceJ
#print axioms chart_quotientJ
#print axioms chartField_eq

end ZInQ.Manuscript.RC.ModelNeron
