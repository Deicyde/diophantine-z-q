import ZInQKernel.Contrib.OneProof.FaltingsDVR.TorsionSpecialization
import ZInQKernel.Contrib.OneProof.FaltingsDict2
import ZInQKernel.Contrib.OneProof.StrictHenselizationPair

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace SmoothGroup

set_option backward.isDefEq.respectTransparency false in
/-- The generic monomorphism survives an extension of the base, when the
square of generic-fibre maps commutes. -/
theorem mono_pullback_map_of_generic_mono
    {S S' T T' : Scheme.{0}} {X Y : Over S} (u : X ⟶ Y) {s : S' ⟶ S}
    {j : T ⟶ S} {j' : T' ⟶ S'} {g : T' ⟶ T} (h : j' ≫ s = g ≫ j)
    [Mono ((Over.pullback j).map u)] :
    Mono ((Over.pullback j').map ((Over.pullback s).map u)) := by
  let e : Over.pullback s ⋙ Over.pullback j' ≅ Over.pullback j ⋙ Over.pullback g :=
    (Over.pullbackComp j' s).symm ≪≫
      eqToIso (congrArg (fun f : T' ⟶ S => Over.pullback f) h) ≪≫ Over.pullbackComp g j
  have hm : Mono ((Over.pullback j ⋙ Over.pullback g).map u) := by
    change Mono ((Over.pullback g).map ((Over.pullback j).map u))
    infer_instance
  have hEq : (Over.pullback j').map ((Over.pullback s).map u) ≫ e.hom.app Y =
      e.hom.app X ≫ ((Over.pullback j ⋙ Over.pullback g).map u) :=
    e.hom.naturality u
  have : Mono ((Over.pullback j').map ((Over.pullback s).map u) ≫ e.hom.app Y) := by
    rw [hEq]
    infer_instance
  exact mono_of_mono _ (e.hom.app Y)

open ReductSplit ZInQ.FaltingsRestate ZInQ.SemiAbDescend

/-- The scheme map induced by one valuation ring dominating another. -/
abbrev comapSpec {K E : Type} [Field K] [Field E] [Algebra K E]
    {O : ValuationSubring K} {P : ValuationSubring E}
    (hP : P.comap (algebraMap K E) = O) : Spec (.of P) ⟶ Spec (.of O) :=
  Spec.map (CommRingCat.ofHom (ReductSplit.comapHom hP))

private theorem generic_square {K E : Type} [Field K] [Field E] [Algebra K E]
    {O : ValuationSubring K} {P : ValuationSubring E}
    (hP : P.comap (algebraMap K E) = O) :
    genericMap P E ≫ comapSpec hP =
      Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ genericMap O K := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

set_option maxHeartbeats 900000 in
set_option synthInstance.maxHeartbeats 120000 in
/-- Special-fibre torsion survives the generic comparison over any strict
henselization, including over an algebraic closure of its residue field. -/
theorem geometric_special_torsion_kernel_trivial_of_comparison
    {K E : Type} [Field K] [Field E] [Algebra K E]
    {O : ValuationSubring K} {P : ValuationSubring E}
    (hP : P.comap (algebraMap K E) = O)
    [IsDiscreteValuationRing P] [HenselianLocalRing P]
    [IsSepClosed (IsLocalRing.ResidueField P)]
    {A : PkgI3.AbVar K} (G N : GroupModelO A O) (i : G.G ⟶ N.G)
    (hi : (Over.pullback (jO O)).map i ≫ N.gen.hom = G.gen.hom)
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField P) L]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField P) L] :
    let F := Over.pullback (comapSpec hP)
    letI : GrpObj (F.obj G.G) := Functor.grpObjObj
    letI : GrpObj (F.obj N.G) := Functor.grpObjObj
    ∀ (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField P) L)) ≫
      (residueObject P).hom) ⟶ F.obj G.G) (m : ℕ),
      IsUnit (m : O) → a ^ m = 1 → a ≫ F.map i = 1 → a = 1 := by
  let F := Over.pullback (comapSpec hP)
  let J := Over.pullback (jO O)
  let : GrpObj (F.obj G.G) := Functor.grpObjObj
  let : GrpObj (F.obj N.G) := Functor.grpObjObj
  let : GrpObj (J.obj G.G) := Functor.grpObjObj
  let : GrpObj (J.obj N.G) := Functor.grpObjObj
  dsimp only
  intro a m hm ha hg
  have : IsIso (J.map i ≫ N.gen.hom) := hi ▸ inferInstance
  have : IsIso (J.map i) := IsIso.of_isIso_comp_right (J.map i) N.gen.hom
  have : IsMonHom N.gen.hom := N.gen_hom
  have : IsMonHom (J.map i ≫ N.gen.hom) := hi ▸ G.gen_hom
  have : IsMonHom (J.map i) := isMonHom_of_comp_mono _ N.gen.hom
  have : IsMonHom i := isMonHom_of_generic G N i (J.map i) inferInstance rfl
  have : IsMonHom (F.map i) := inferInstance
  have : Mono ((Over.pullback (genericMap P E)).map (F.map i)) :=
    mono_pullback_map_of_generic_mono i (generic_square hP)
  have : IsCommMonObj G.G := isCommMonObj_groupModelO G
  have : IsCommMonObj N.G := isCommMonObj_groupModelO N
  have : IsCommMonObj (F.obj G.G) := F.isCommMonObj_obj
  have : IsCommMonObj (F.obj N.G) := F.isCommMonObj_obj
  have : Smooth (F.obj G.G).hom := show Smooth (pullback.snd G.G.hom _) from inferInstance
  have : Smooth (F.obj N.G).hom := show Smooth (pullback.snd N.G.hom _) from inferInstance
  have : IsSeparated (F.obj G.G).hom :=
    show IsSeparated (pullback.snd G.G.hom _) from inferInstance
  have : IsSeparated (F.obj N.G).hom :=
    show IsSeparated (pullback.snd N.G.hom _) from inferInstance
  have hm' : IsUnit (m : P) := by
    simpa only [map_natCast] using hm.map (ReductSplit.comapHom hP)
  exact algebraicClosure_residue_torsion_kernel_trivial (K := E) (F.map i) a m hm' ha hg

end SmoothGroup
