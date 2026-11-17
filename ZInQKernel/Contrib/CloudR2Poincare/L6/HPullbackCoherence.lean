import ZInQKernel.Contrib.CloudR2Poincare.L6.HMapAdjunction
/-!
# Composition/identity/unit coherence of the EXISTING native H.pullback

All coefficient arrows and isomorphisms are the existing native scheme-module
maps. The unit specialization is identified with the actual structure-sheaf
coefficient arrow, whose literal ring map composes. No model or square input.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L6

/-- Expose only the existing pullback map's function field. The comp/id
proofs can then match native adjunction-map equalities without unfolding
coercions on nested semilinear pullbacks during their closing exact. -/
private theorem e2_nativeHPullback_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (q : ℕ) (z : M.H q) :
    Scheme.Modules.H.pullback f M q z =
      Scheme.Modules.H.mapOfAdjunction f
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) q z := rfl

/-- EXACT full native pullback composition, with the EXISTING pullbackComp orientation. -/
theorem nativeHPullback_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (M : Z.Modules) (q : ℕ) (z : M.H q) :
    Scheme.Modules.H.map ((Scheme.Modules.pullbackComp a b).app M).hom q
        (Scheme.Modules.H.pullback a ((Scheme.Modules.pullback b).obj M) q
          (Scheme.Modules.H.pullback b M q z)) =
      Scheme.Modules.H.pullback (a ≫ b) M q z := by
  let N := (Scheme.Modules.pullback b).obj M
  let P := (Scheme.Modules.pullback a).obj N
  let φ := (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M
  let ψ := (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app N
  let c := φ ≫ (Scheme.Modules.pushforward b).map ψ ≫
    (Scheme.Modules.pushforwardComp a b).hom.app P
  let e := (Scheme.Modules.pullbackComp a b).hom.app M
  have hcomp := nativeHMapOfAdjunction_comp a b (M := M) (N := N) (P := P) φ ψ q z
  have hp := nativeHMapOfAdjunction_postcompose (a ≫ b) c e q z
  have hu : c ≫ (Scheme.Modules.pushforward (a ≫ b)).map e =
      (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b)).unit.app M := by
    simpa only [c, φ, ψ, P, N, e, Category.assoc] using nativePullbackComp_unit a b M
  have hcoeff := congrArg (fun d => Scheme.Modules.H.mapOfAdjunction (a ≫ b) d q z) hu
  change Scheme.Modules.H.map e q
      (Scheme.Modules.H.pullback a N q (Scheme.Modules.H.pullback b M q z)) =
    Scheme.Modules.H.pullback (a ≫ b) M q z
  rw [e2_nativeHPullback_apply a N q, e2_nativeHPullback_apply b M q,
    e2_nativeHPullback_apply (a ≫ b) M q]
  change Scheme.Modules.H.map e q
      (Scheme.Modules.H.mapOfAdjunction a ψ q
        (Scheme.Modules.H.mapOfAdjunction b φ q z)) =
    Scheme.Modules.H.mapOfAdjunction (a ≫ b)
      ((Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b)).unit.app M) q z
  exact (congrArg (fun v => Scheme.Modules.H.map e q v) hcomp).trans (hp.trans hcoeff)

/-- EXACT identity coherence for the existing native cohomological pullback. -/
theorem nativeHPullback_id (X : Scheme.{u}) (M : X.Modules) (q : ℕ) (z : M.H q) :
    Scheme.Modules.H.map ((Scheme.Modules.pullbackId X).app M).hom q
        (Scheme.Modules.H.pullback (𝟙 X) M q z) = z := by
  let φ := (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app M
  let e := (Scheme.Modules.pullbackId X).hom.app M
  have hp := nativeHMapOfAdjunction_postcompose (𝟙 X) φ e q z
  have hcoeff := congrArg (fun d => Scheme.Modules.H.mapOfAdjunction (𝟙 X) d q z)
    (nativePullbackId_unit X M)
  change Scheme.Modules.H.map e q (Scheme.Modules.H.pullback (𝟙 X) M q z) = z
  rw [e2_nativeHPullback_apply (𝟙 X) M q]
  exact hp.trans (hcoeff.trans (nativeHMapOfAdjunction_id X M q z))

/-- The actual native structure-sheaf coefficient arrow of a scheme morphism. -/
def nativeStructureCoefficient {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.unit Y ⟶ (Scheme.Modules.pushforward f).obj (Scheme.Modules.unit X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/-- Native structure coefficient arrows compose by the ACTUAL ring maps. -/
theorem nativeStructureCoefficient_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) :
    nativeStructureCoefficient b ≫ (Scheme.Modules.pushforward b).map (nativeStructureCoefficient a) ≫
        (Scheme.Modules.pushforwardComp a b).hom.app (Scheme.Modules.unit X) =
      nativeStructureCoefficient (a ≫ b) := by
  ext U s
  rfl

/-- The actual identity structure coefficient is the native pushforwardId coefficient. -/
theorem nativeStructureCoefficient_id (X : Scheme.{u}) :
    nativeStructureCoefficient (𝟙 X) =
      (Scheme.Modules.pushforwardId X).inv.app (Scheme.Modules.unit X) := by
  ext U s
  rfl

/-- The ACTUAL unit coefficient pullback iso is adjoint to the ACTUAL structure coefficient. -/
theorem nativeUnitCoefficient_adjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Scheme.Modules.unit Y) ≫
        (Scheme.Modules.pushforward f).map (Scheme.Modules.pullbackObjUnitIso f).hom =
      nativeStructureCoefficient f := by
  change (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
      (Scheme.Modules.unit Y) (Scheme.Modules.unit X)
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) =
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

/-- The SAME native unit cohomology pullback is the adjunction map of the actual ring coefficient. -/
theorem nativeUnitHPullback_eq_adjunction {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ)
    (z : (Scheme.Modules.unit Y).H q) :
    nativeUnitHPullback f q z =
      Scheme.Modules.H.mapOfAdjunction f (nativeStructureCoefficient f) q z := by
  change Scheme.Modules.H.map (Scheme.Modules.pullbackObjUnitIso f).hom q
      (Scheme.Modules.H.mapOfAdjunction f
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Scheme.Modules.unit Y)) q z) = _
  rw [nativeHMapOfAdjunction_postcompose, nativeUnitCoefficient_adjunction]
  rfl

/-- Unit specialization: the actual additive cohomology pullbacks compose. -/
theorem nativeUnitHPullback_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (q : ℕ) :
    nativeUnitHPullback (a ≫ b) q =
      (nativeUnitHPullback a q).comp (nativeUnitHPullback b q) := by
  ext z
  change nativeUnitHPullback (a ≫ b) q z =
    nativeUnitHPullback a q (nativeUnitHPullback b q z)
  rw [nativeUnitHPullback_eq_adjunction, nativeUnitHPullback_eq_adjunction,
    nativeUnitHPullback_eq_adjunction, nativeHMapOfAdjunction_comp,
    nativeStructureCoefficient_comp]

/-- Unit specialization: the actual identity pullback is identity on every native cohomology degree. -/
theorem nativeUnitHPullback_id (X : Scheme.{u}) (q : ℕ) :
    nativeUnitHPullback (𝟙 X) q = AddMonoidHom.id ((Scheme.Modules.unit X).H q) := by
  ext z
  change nativeUnitHPullback (𝟙 X) q z = z
  rw [nativeUnitHPullback_eq_adjunction, nativeStructureCoefficient_id]
  exact nativeHMapOfAdjunction_id X (Scheme.Modules.unit X) q z

end ZInQ.Contrib.CloudR2Poincare.L6
