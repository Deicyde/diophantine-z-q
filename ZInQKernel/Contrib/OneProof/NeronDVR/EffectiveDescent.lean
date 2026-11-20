import ZInQKernel.Contrib.OneProof.NeronDVR.DescentDatum
import ZInQKernel.Contrib.OneProof.NeronDVR.GroupDescent
import ZInQKernel.Contrib.OneProof.NeronDVR.MappingDescent
import ZInQKernel.Contrib.OneProof.NeronSchemeExtensionExists

/-!
# Néron models from effective descent

A smooth fpqc cover with a Cartesian generic-fibre square descends a Néron
model once the datum given by its mapping property is effective.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronDVR

/-- Effective descent along a smooth fpqc cover preserves the Néron model
predicate and descends the prescribed generic fibre. -/
theorem neron_model_of_effective_descent
    {R R' K K' : Type} [CommRing R] [IsDomain R] [CommRing R']
    [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K']
    (p : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K))
    (hpb : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) t p
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    [Smooth p] [Surjective p] [QuasiCompact p]
    (N : Over (Spec (CommRingCat.of R'))) (hN : CToPrinted.IsNeronModelOver R' K' N)
    (A : Over (Spec (CommRingCat.of K)))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R' K')))).obj N ≅
      (Over.pullback t).obj A)
    (heff : letI : Smooth N.hom := hN.1
      (neronDescentDatum _ p N _ t hpb e hN.2.2.2.2).IsEffective) :
    ∃ X : Over (Spec (CommRingCat.of R)), CToPrinted.IsNeronModelOver R K X ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X ≅ A) := by
  have : Smooth N.hom := hN.1
  have : Flat t := MorphismProperty.of_isPullback hpb (inferInstance : Flat p)
  have : Surjective t := MorphismProperty.of_isPullback hpb (inferInstance : Surjective p)
  have : QuasiCompact t := MorphismProperty.of_isPullback hpb (inferInstance : QuasiCompact p)
  obtain ⟨X, k, hk, hX⟩ := exists_model_with_generic_fibre _ p N _ t hpb e hN.2.2.2.2 heff
  let i : N ≅ (Over.pullback p).obj X := Over.isoMk hk.isoPullback hk.isoPullback_hom_snd
  exact ⟨X, isNeronModelOver_of_fpqc p t hpb X (NeronExt.isNeronModelOver_of_iso i.symm hN), hX⟩

open MonoidalCategory

/-- The transport isomorphism between the two models on the overlap
preserves the group operations. -/
def IsGroupCompatible {S S' : Scheme.{0}} {p : S' ⟶ S}
    {G : Over S'} [GrpObj G] (d : Over.DescentDatum p G) : Prop :=
  letI : GrpObj ((Over.pullback (pullback.fst p p)).obj G) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback (pullback.snd p p)).obj G) := Functor.grpObjObj
  IsMonHom (transportHom G (pullback.fst p p) (pullback.snd p p) d pullback.condition)

/-- Group-scheme effectivity over DVRs, the group conclusion of Bosch–Lütkebohmert–Raynaud,
*Néron Models*, §6.5, Theorem 1 (printed p. 157). One may take the torsor to be the
group acting on itself by translation. -/
def EffectiveDescentForDVRGroups : Prop :=
  ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    (p : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    [Flat p] [Surjective p] [QuasiCompact p]
    (G : Over (Spec (CommRingCat.of R'))) [GrpObj G] [Smooth G.hom]
    [IsSeparated G.hom] [QuasiCompact G.hom] (d : Over.DescentDatum p G),
    IsGroupCompatible d → d.IsEffective

/-- The Néron property gives a group law on the model. Its canonical datum is
group-compatible, so it can be passed to a group effectivity theorem. -/
theorem neron_model_of_compatible_effectivity
    {R R' K K' : Type} [CommRing R] [IsDomain R] [CommRing R']
    [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K']
    (p : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K))
    (hpb : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) t p
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    [Smooth p] [Surjective p] [QuasiCompact p]
    (N : Over (Spec (CommRingCat.of R'))) (hN : CToPrinted.IsNeronModelOver R' K' N)
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R' K')))).obj N ≅
      (Over.pullback t).obj A)
    (effect : ∀ [GrpObj N] [Smooth N.hom] [IsSeparated N.hom] [QuasiCompact N.hom],
      let d := neronDescentDatum _ p N _ t hpb e hN.2.2.2.2
      IsGroupCompatible d → d.IsEffective) :
    ∃ X : Over (Spec (CommRingCat.of R)), CToPrinted.IsNeronModelOver R K X ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X ≅ A) := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let j' := Spec.map (CommRingCat.ofHom (algebraMap R' K'))
  let F := Over.pullback j'
  let B := (Over.pullback t).obj A
  let P : Over (Spec (CommRingCat.of R')) → Prop := fun Y => Smooth Y.hom
  have : Smooth N.hom := hN.1
  have : IsSeparated N.hom := hN.2.1
  have : QuasiCompact N.hom := hN.2.2.2.1
  have : IsSchemeTheoreticallyDominant j :=
    ZInQ.Contrib.NeronC.isSchemeTheoreticallyDominant_spec_map _ (IsFractionRing.injective R K)
  let : GrpObj B := Functor.grpObjObj
  have hunit : P (𝟙_ _) := ZInQ.Contrib.NeronC.smooth_tensorUnit _
  have hprod : ∀ X Y, P X → P Y → P (X ⊗ Y) := ZInQ.Contrib.NeronC.smooth_tensor
  have hB (Y : Over (Spec (CommRingCat.of R'))) (hY : P Y) :
      Function.Bijective (fun f : Y ⟶ N => F.map f ≫ e.hom) := by
    let : Smooth Y.hom := hY
    exact (e.homToEquiv (Z := F.obj Y)).bijective.comp (hN.2.2.2.2 Y)
  let : GrpObj N := ZInQ.Contrib.NeronC.grpObjOfNeron F P hunit hprod N hN.1 B e hB
  have he := ZInQ.Contrib.NeronC.isMonHom_of_neron F P hunit hprod N hN.1 B e hB
  let d := neronDescentDatum j p N j' t hpb e hN.2.2.2.2
  have hcompat := neronDescentDatum_groupCompatible j p j' t hpb N e he hN.2.2.2.2
  have heff : d.IsEffective := effect hcompat
  exact neron_model_of_effective_descent p t hpb N hN A e heff

/-- Over a smooth fpqc cover of DVRs, group-scheme effectivity suffices to descend
a Néron model with a prescribed generic group. -/
theorem neron_model_of_group_effectivity
    (effect : EffectiveDescentForDVRGroups)
    {R R' K K' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K']
    (p : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K))
    (hpb : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) t p
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    [Smooth p] [Surjective p] [QuasiCompact p]
    (N : Over (Spec (CommRingCat.of R'))) (hN : CToPrinted.IsNeronModelOver R' K' N)
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R' K')))).obj N ≅
      (Over.pullback t).obj A) :
    ∃ X : Over (Spec (CommRingCat.of R)), CToPrinted.IsNeronModelOver R K X ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X ≅ A) := by
  refine neron_model_of_compatible_effectivity p t hpb N hN A e ?_
  intro _ _ _ _ d hcompat
  exact effect R R' p N d hcompat

end NeronDVR
