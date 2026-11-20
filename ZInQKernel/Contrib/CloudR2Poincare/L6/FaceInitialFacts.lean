import ZInQKernel.Contrib.CloudR2Poincare.L6.HZeroFaceInjection
/-!
# Actual native coefficient transport and initial face/cohomology facts

All coefficient maps are the literal pullback of a given actual trivialization,
followed by the native pullbackObjUnitIso. The degree-zero/one injection facts
are discharged by the proved native unit-face injections. Numerical ranks are
computed from genuine proper geometric integrality, not supplied rank Facts.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
namespace ZInQ.Contrib.CloudR2Poincare.L6

/-- Coefficient trivialization transport for the ORIGINAL cohomological pullback,
with the literal canonical unit coefficient and its correct orientation. -/
theorem nativeUnitHPullback_coefficient_naturality
    {Q A : Scheme.{u}} (f : A ⟶ Q) {M : Q.Modules}
    (e : M ≅ Scheme.Modules.unit Q) (q : ℕ) (z : M.H q) :
    nativeUnitHPullback f q (Scheme.Modules.H.map e.hom q z) =
      Scheme.Modules.H.map (((Scheme.Modules.pullback f).mapIso e ≪≫
        Scheme.Modules.pullbackObjUnitIso f).hom) q (Scheme.Modules.H.pullback f M q z) := by
  change Scheme.Modules.H.map (Scheme.Modules.pullbackObjUnitIso f).hom q
    (Scheme.Modules.H.pullback f (Scheme.Modules.unit Q) q (Scheme.Modules.H.map e.hom q z)) = _
  exact (congrArg (Scheme.Modules.H.map (Scheme.Modules.pullbackObjUnitIso f).hom q)
    (Scheme.Modules.H.pullback_naturality f e.hom q z)).trans
      (Scheme.Modules.H.map_comp_apply ((Scheme.Modules.pullback f).map e.hom)
        (Scheme.Modules.pullbackObjUnitIso f).hom q (Scheme.Modules.H.pullback f M q z)).symm

/-- The actual pullback pair on a genuinely trivial module inherits unit-pair
injectivity. This is a coefficient-naturality lemma, not a HasCube/model premise. -/
theorem nativeHPullbackPair_injective_of_unit_iso
    {Q A B : Scheme.{u}} (f : A ⟶ Q) (g : B ⟶ Q) (M : Q.Modules)
    (e : M ≅ Scheme.Modules.unit Q) (q : ℕ)
    (hUnit : Function.Injective (fun z : (Scheme.Modules.unit Q).H q =>
      (nativeUnitHPullback f q z, nativeUnitHPullback g q z))) :
    Function.Injective (fun z : M.H q =>
      (Scheme.Modules.H.pullback f M q z, Scheme.Modules.H.pullback g M q z)) := by
  intro z w hz
  apply (Scheme.Modules.H.mapLinearEquiv e q).injective
  apply hUnit
  apply Prod.ext
  · calc
      nativeUnitHPullback f q (Scheme.Modules.H.map e.hom q z) =
          Scheme.Modules.H.map (((Scheme.Modules.pullback f).mapIso e ≪≫
            Scheme.Modules.pullbackObjUnitIso f).hom) q (Scheme.Modules.H.pullback f M q z) :=
        nativeUnitHPullback_coefficient_naturality f e q z
      _ = Scheme.Modules.H.map (((Scheme.Modules.pullback f).mapIso e ≪≫
            Scheme.Modules.pullbackObjUnitIso f).hom) q (Scheme.Modules.H.pullback f M q w) :=
        congrArg (Scheme.Modules.H.map (((Scheme.Modules.pullback f).mapIso e ≪≫
          Scheme.Modules.pullbackObjUnitIso f).hom) q) (congrArg Prod.fst hz)
      _ = nativeUnitHPullback f q (Scheme.Modules.H.map e.hom q w) :=
        (nativeUnitHPullback_coefficient_naturality f e q w).symm
  · calc
      nativeUnitHPullback g q (Scheme.Modules.H.map e.hom q z) =
          Scheme.Modules.H.map (((Scheme.Modules.pullback g).mapIso e ≪≫
            Scheme.Modules.pullbackObjUnitIso g).hom) q (Scheme.Modules.H.pullback g M q z) :=
        nativeUnitHPullback_coefficient_naturality g e q z
      _ = Scheme.Modules.H.map (((Scheme.Modules.pullback g).mapIso e ≪≫
            Scheme.Modules.pullbackObjUnitIso g).hom) q (Scheme.Modules.H.pullback g M q w) :=
        congrArg (Scheme.Modules.H.map (((Scheme.Modules.pullback g).mapIso e ≪≫
          Scheme.Modules.pullbackObjUnitIso g).hom) q) (congrArg Prod.snd hz)
      _ = nativeUnitHPullback g q (Scheme.Modules.H.map e.hom q w) :=
        (nativeUnitHPullback_coefficient_naturality g e q w).symm

/-- Initial degree-zero native face-map injection from the ACTUAL fibre trivialization. -/
theorem nativeHZero_twoFacesModule_injective
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    [IsProper X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom]
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (M : (X ⊗ Y).left.Modules) (e : M ≅ Scheme.Modules.unit (X ⊗ Y).left) :
    Function.Injective (fun z : M.H 0 =>
      (Scheme.Modules.H.pullback (lift (𝟙 X) (toUnit X ≫ y)).left M 0 z,
        Scheme.Modules.H.pullback (lift (toUnit Y ≫ x) (𝟙 Y)).left M 0 z)) :=
  nativeHPullbackPair_injective_of_unit_iso _ _ M e 0 (nativeHZero_twoFaces_injective X Y x y)

/-- Initial degree-one native face-map injection from the actual fibre trivialization,
not an assumed H1 injection/Kunneth/O-acyclicity premise. -/
theorem nativeHOne_twoFacesModule_injective
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    [IsProper X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom]
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (M : (X ⊗ Y).left.Modules) (e : M ≅ Scheme.Modules.unit (X ⊗ Y).left) :
    Function.Injective (fun z : M.H 1 =>
      (Scheme.Modules.H.pullback (lift (𝟙 X) (toUnit X ≫ y)).left M 1 z,
        Scheme.Modules.H.pullback (lift (toUnit Y ≫ x) (𝟙 Y)).left M 1 z)) :=
  nativeHPullbackPair_injective_of_unit_iso _ _ M e 1 (nativeHOne_twoFaces_injective X Y x y)

/-- Rank one of ACTUAL H0 on a trivial residue-product module. -/
theorem nativeHZero_trivialProduct_finrank_eq_one
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    [IsProper X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom]
    (M : (X ⊗ Y).left.Modules) (e : M ≅ Scheme.Modules.unit (X ⊗ Y).left) :
    letI : (X ⊗ Y).left.Over (Spec (.of k)) := ⟨(X ⊗ Y).hom⟩
    Module.finrank k (M.H 0) = 1 := by
  letI : (X ⊗ Y).left.Over (Spec (.of k)) := ⟨(X ⊗ Y).hom⟩
  haveI : IsProper (fst X Y).left := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom))
  haveI : IsProper (X ⊗ Y).hom := by rw [← Over.w (fst X Y)]; infer_instance
  haveI : GeometricallyIntegral (X ⊗ Y).hom := nativeProduct_geometricallyIntegral X Y
  haveI : IsProper ((X ⊗ Y).left ↘ Spec (.of k)) := inferInstanceAs (IsProper (X ⊗ Y).hom)
  haveI : GeometricallyIntegral ((X ⊗ Y).left ↘ Spec (.of k)) :=
    inferInstanceAs (GeometricallyIntegral (X ⊗ Y).hom)
  exact (Scheme.Modules.finrankH_congr k e 0).trans
    (ZInQ.Contrib.CloudR2Poincare.L3.HOneCoefficients.unit_finrankH_zero (k := k))

/-- Entire-face trivializations force ACTUAL H0 of their pair to have rank two,
including genuine finiteness from proper cohomology of the same coefficients. -/
theorem nativeHZero_trivialFaces_finrank_eq_two
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    [IsProper X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom]
    (MX : X.left.Modules) (MY : Y.left.Modules)
    (eX : MX ≅ Scheme.Modules.unit X.left) (eY : MY ≅ Scheme.Modules.unit Y.left) :
    letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
    letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
    Module.finrank k (MX.H 0 × MY.H 0) = 2 := by
  letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
  haveI : IsProper (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsProper Y.hom)
  haveI : GeometricallyIntegral (X.left ↘ Spec (.of k)) := inferInstanceAs (GeometricallyIntegral X.hom)
  haveI : GeometricallyIntegral (Y.left ↘ Spec (.of k)) := inferInstanceAs (GeometricallyIntegral Y.hom)
  haveI : Module.Finite k ((Scheme.Modules.unit X.left).H 0) :=
    ZInQ.Contrib.CloudR2Poincare.L3.HOneCoefficients.finite_unit_H 0
  haveI : Module.Finite k ((Scheme.Modules.unit Y.left).H 0) :=
    ZInQ.Contrib.CloudR2Poincare.L3.HOneCoefficients.finite_unit_H 0
  haveI : Module.Finite k (MX.H 0) := Scheme.Modules.finite_H_of_iso (p := X.hom) eX.symm 0 inferInstance
  haveI : Module.Finite k (MY.H 0) := Scheme.Modules.finite_H_of_iso (p := Y.hom) eY.symm 0 inferInstance
  have hX : Module.finrank k (MX.H 0) = 1 :=
    (Scheme.Modules.finrankH_congr k eX 0).trans
      (ZInQ.Contrib.CloudR2Poincare.L3.HOneCoefficients.unit_finrankH_zero (k := k))
  have hY : Module.finrank k (MY.H 0) = 1 :=
    (Scheme.Modules.finrankH_congr k eY 0).trans
      (ZInQ.Contrib.CloudR2Poincare.L3.HOneCoefficients.unit_finrankH_zero (k := k))
  rw [Module.finrank_prod, hX, hY]

end ZInQ.Contrib.CloudR2Poincare.L6
