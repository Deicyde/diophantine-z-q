import Lean
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Main
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.NeronC.NeronGroupAbstract
import ZInQKernel.Contrib.CloudW03NeronSurj.Basic

/-!
# Native same-object local model, independent of pending C5 transport

H4 lead, 2026-11-14. The actual source-proved LOCAL henselian-DVR constructor
is imported from H77 C04. Its existing canonical H76 scheme/NMP carriers
are not redeclared. The group law and generic group compatibility are
constructed by the already-published, universe-generic
`NeronC.grpObjOfNeron` / `NeronC.isMonHom_of_neron` on the SAME source scheme
and SAME source generic isomorphism. No unverified C5 GroupLaw or
number-field-only FixedGroupModels export is used.

The literal source restriction is converted to `Over.pullback.map` through
H76's actual morphism-subtype equivalences. This is the native local join
owned by H4, not a re-port or copy of C5's source-law transport.

This constructs only an actual local smooth separated group model with
full NMP. It asserts neither properness of that model nor semistability,
SGA7 unipotence, original-O descent, NOS or RaynaudCriterion. The original
DVR O need not be henselian when this lemma is applied on the separately
CONSTRUCTED strict local P/E.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace ZInQ.Contrib.CloudR2Raynaud.NativeLocalNeronModel

open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian

/-- The original field AV supplies the canonical source bundle on the SAME
scheme. This is the existing H76 bundle construction specialized to that
actual generic group, not a supplied-model hypothesis. -/
theorem source_bundle {K : Type u} [Field K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [hA : PkgI2.IsAbelianVariety A] :
    AbelianSchemePropertyBundle K A.X.hom := by
  letI : GrpObj (Over.mk A.X.hom) := by
    change GrpObj A.X
    infer_instance
  haveI : GeometricallyIntegral A.X.hom := hA.geomIntegral
  haveI : GeometricallyConnected A.X.hom := by
    constructor
    intro L instL y Z fst snd hpb
    haveI : IrreducibleSpace Z :=
      (inferInstance : GeometricallyIrreducible A.X.hom).geometrically_irreducibleSpace
        y fst snd hpb
    infer_instance
  exact
    { smooth := hA.smooth
      proper := hA.proper
      connectedFibres := fun s => A.X.hom.isConnected_preimage_singleton s
      hasGroupLaw := ⟨relativeGroupLawOfGrpObj K A.X.hom⟩ }

/-- The canonical source restriction IS the original pullback functor map;
there is no copied source law or unproved mapper compatibility premise. -/
theorem restriction_eq {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {X Y : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of R)}
    (t : Y ⟶ Spec (CommRingCat.of R)) (f : Over.mk t ⟶ Over.mk g) :
    schemeHomOverToOverHom (genericFibreRestrict R K g t (overHomToSchemeHomOver f)) =
      (Over.pullback (specGenericFibreInclusion R K)).map f := rfl

/-- Full source NMP on the actual source scheme gives the full native Over
bijection. Every smooth test is quantified, not only affine or QC tests. -/
theorem raw_mapping {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    (hN : NeronModelPropertyBundle R K g) :
    ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom →
      Function.Bijective (fun f : Y ⟶ Over.mk g =>
        (Over.pullback (specGenericFibreInclusion R K)).map f) := by
  intro Y hY
  let E := schemeHomOverEquivOverHom Y.hom g
  let EK := schemeHomOverEquivOverHom
    (pullback.snd Y.hom (specGenericFibreInclusion R K))
    (pullback.snd g (specGenericFibreInclusion R K))
  have hfun : (fun f : Y ⟶ Over.mk g =>
      (Over.pullback (specGenericFibreInclusion R K)).map f) =
      EK ∘ genericFibreRestrict R K g Y.hom ∘ E.symm := by
    funext f
    exact (restriction_eq Y.hom f).symm
  rw [hfun]
  exact EK.bijective.comp ((hN.neronMapping Y.left Y.hom hY).comp E.symm.bijective)

/-- Smooth test objects contain the terminal base object, by the actual
smooth identity R-algebra proof. Avoid broad scheme-identity inference. -/
theorem smooth_unit (R : Type u) [CommRing R] :
    Smooth (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := by
  have hId : RingHom.Smooth (RingHom.id R) := RingHom.Smooth.of_bijective Function.bijective_id
  have hSpec : Smooth (Spec.map (CommRingCat.ofHom (RingHom.id R))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr hId
  simpa only [Over.tensorUnit_hom, CommRingCat.ofHom_id, Spec.map_id] using hSpec

/-- The actual smooth-test class is closed under its cartesian product. -/
theorem smooth_tensor {R : Type u} [CommRing R]
    (X Y : Over (Spec (CommRingCat.of R))) (hX : Smooth X.hom) (hY : Smooth Y.hom) :
    Smooth (X ⊗ Y).hom := by
  letI : Smooth X.hom := hX
  letI : Smooth Y.hom := hY
  rw [Over.tensorObj_hom]
  infer_instance

/-- A native group model with the exact generic group iso and ALL-smooth
NMP, obtained without assuming any pending source/group transport theorem. -/
theorem exists_group_model
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A] :
    ∃ (G : Grp (Over (Spec (CommRingCat.of R))))
      (_ : Smooth G.X.hom) (_ : IsSeparated G.X.hom) (_ : QuasiCompact G.X.hom)
      (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.obj G ≅ A),
      IsCommMonObj G.X ∧
      NeronModelPropertyBundle R K G.X.hom ∧
      AbelianSchemePropertyBundle K
        (pullback.snd G.X.hom (specGenericFibreInclusion R K)) ∧
      ∀ (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom],
        Function.Bijective (fun f : Y ⟶ G.X =>
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f ≫ gen.hom.hom.hom) := by
  letI : GrpObj (Over.mk A.X.hom) := by
    change GrpObj A.X
    infer_instance
  let LA := relativeGroupLawOfGrpObj K A.X.hom
  have hA := source_bundle A
  obtain ⟨X, g, _LB, e, hN, _hcomm, hIso, _hmul⟩ :=
    ZInQ.Contrib.CloudR2NeronExistence.Henselian.exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
      (R := R) K LA hA
  letI : IsIso e.1 := hIso
  let F := Over.pullback (specGenericFibreInclusion R K)
  let P : Over (Spec (CommRingCat.of R)) → Prop := fun Y => Smooth Y.hom
  let N : Over (Spec (CommRingCat.of R)) := Over.mk g
  let es : F.obj N ≅ A.X := Over.isoMk (asIso e.1) e.2
  have hP1 : P (𝟙_ _) := smooth_unit R
  have hP2 : ∀ Y Z, P Y → P Z → P (Y ⊗ Z) := fun Y Z hY hZ => smooth_tensor Y Z hY hZ
  have hraw := raw_mapping g hN
  have hpost : ∀ Y : Over (Spec (CommRingCat.of R)),
      Function.Bijective (fun q : F.obj Y ⟶ F.obj N => q ≫ es.hom) := by
    intro Y
    constructor
    · intro f k hfk
      exact (cancel_mono es.hom).mp hfk
    · intro q
      refine ⟨q ≫ es.inv, ?_⟩
      simp only [Category.assoc, es.inv_hom_id, Category.comp_id]
  have hmap : ∀ Y, P Y → Function.Bijective (fun f : Y ⟶ N => F.map f ≫ es.hom) :=
    fun Y hY => (hpost Y).comp (hraw Y hY)
  letI : GrpObj N :=
    ZInQ.Contrib.NeronC.grpObjOfNeron F P hP1 hP2 N hN.smooth A.X es hmap
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : GeometricallyIntegral A.X.hom := PkgI2.IsAbelianVariety.geomIntegral
  letI : IsCommMonObj A.X := isCommMonObj_of_isProper_of_geometricallyIntegral A.X
  have hcommN : IsCommMonObj N := by
    -- The same proof was kernel-checked independently in
    -- NeronNativeCommutativity.lean. It is instantiated here without a new
    -- own-library import, so this source keeps its four certified C4/root imports.
    have hμ : ZInQ.Contrib.NeronC.nPhi es μ[N] =
        ZInQ.Contrib.NeronC.nPhi es (fst N N) * ZInQ.Contrib.NeronC.nPhi es (snd N N) := by
      exact ZInQ.Contrib.NeronC.nPhi_nPsi F P N A.X es hmap
        (hP2 N N hN.smooth hN.smooth) _
    constructor
    apply ZInQ.Contrib.NeronC.nPhi_inj F P N A.X es hmap (hP2 N N hN.smooth hN.smooth)
    change ZInQ.Contrib.NeronC.nPhi es ((β_ N N).hom ≫ μ[N]) =
      ZInQ.Contrib.NeronC.nPhi es μ[N]
    rw [ZInQ.Contrib.NeronC.nPhi_comp, hμ, MonObj.comp_mul]
    have hfst : F.map (β_ N N).hom ≫ ZInQ.Contrib.NeronC.nPhi es (fst N N) =
        ZInQ.Contrib.NeronC.nPhi es (snd N N) := by
      rw [← ZInQ.Contrib.NeronC.nPhi_comp, braiding_hom_fst]
    have hsnd : F.map (β_ N N).hom ≫ ZInQ.Contrib.NeronC.nPhi es (snd N N) =
        ZInQ.Contrib.NeronC.nPhi es (fst N N) := by
      rw [← ZInQ.Contrib.NeronC.nPhi_comp, braiding_hom_snd]
    rw [hfst, hsnd, mul_comm]
  letI : IsCommMonObj N := hcommN
  letI : GrpObj (F.obj N) := Functor.grpObjObj
  letI : IsMonHom es.hom :=
    ZInQ.Contrib.NeronC.isMonHom_of_neron F P hP1 hP2 N hN.smooth A.X es hmap
  let G : Grp (Over (Spec (CommRingCat.of R))) := Grp.mk N
  let gen : F.mapGrp.obj G ≅ A := Grp.mkIso' es
  have hgeneric : PkgI2.IsAbelianVariety (F.mapGrp.obj G) := by
    haveI : Smooth A.X.hom := PkgI2.IsAbelianVariety.smooth
    haveI : IsIso es.hom.left := inferInstance
    have hbase : es.hom.left ≫ A.X.hom = (F.obj N).hom := Over.w es.hom
    constructor
    · change IsProper (F.obj N).hom
      rw [← hbase]
      infer_instance
    · change Smooth (F.obj N).hom
      rw [← hbase]
      infer_instance
    · change GeometricallyIntegral (F.obj N).hom
      have hp : IsPullback es.hom.left (F.obj N).hom A.X.hom
          (𝟙 (Spec (CommRingCat.of K))) :=
        IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using hbase⟩
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @GeometricallyIntegral) hp inferInstance
  letI : PkgI2.IsAbelianVariety (F.mapGrp.obj G) := hgeneric
  have hBK : AbelianSchemePropertyBundle K
      (pullback.snd G.X.hom (specGenericFibreInclusion R K)) :=
    source_bundle (F.mapGrp.obj G)
  refine ⟨G, hN.smooth, hN.separated, hN.quasiCompact, gen, hcommN, hN, hBK, ?_⟩
  intro Y hY
  exact hmap Y hY

end ZInQ.Contrib.CloudR2Raynaud.NativeLocalNeronModel

/- These are whole-declaration guards of this ACTUAL local model input,
not a criterion assumption or an instantiated test hiding R/universe data. -/
namespace ZInQ.Contrib.CloudR2Raynaud.NativeLocalNeronModel

open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian

private def ExpectedNativeModel : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A],
    ∃ (G : Grp (Over (Spec (CommRingCat.of R))))
      (_ : Smooth G.X.hom) (_ : IsSeparated G.X.hom) (_ : QuasiCompact G.X.hom)
      (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.obj G ≅ A),
      IsCommMonObj G.X ∧
      NeronModelPropertyBundle R K G.X.hom ∧
      AbelianSchemePropertyBundle K
        (pullback.snd G.X.hom (specGenericFibreInclusion R K)) ∧
      ∀ (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom],
        Function.Bijective (fun f : Y ⟶ G.X =>
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f ≫ gen.hom.hom.hom)

open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let ci ← getConstInfo ``exists_group_model
  match ci with
  | .thmInfo _ => pure ()
  | _ => throwError "Native local model: expected theorem kind"
  let expected ← getConstInfo ``ExpectedNativeModel
  unless ci.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Native local model: one arbitrary symbolic universe required"
  let levels := expected.levelParams.map Level.param
  let actual ← inferType (mkConst ``exists_group_model levels)
  unless ← withTransparency .all <| isDefEq actual (mkConst ``ExpectedNativeModel levels) do
    throwError "Native local model: entire rigid-universe type mismatch"
  let axes ← Lean.collectAxioms ``exists_group_model
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axes.all allowed.contains do
    throwError "Native local model: forbidden transitive axiom: {axes}"
  if ← withTransparency .all <| isDefEq actual (mkConst ``PkgI2.RaynaudCriterion levels) then
    throwError "Native local model must not be the whole Raynaud criterion"
  logInfo m!"NATIVE_LOCAL_MODEL_FULL_RIGID_TYPE/THM/AX3 PASS: {axes}"
  logInfo "NATIVE_LOCAL_MODEL_NOT_RAYNAUD PASS"

#print axioms source_bundle
#print axioms restriction_eq
#print axioms raw_mapping
#print axioms smooth_unit
#print axioms smooth_tensor
#print axioms exists_group_model

end ZInQ.Contrib.CloudR2Raynaud.NativeLocalNeronModel
