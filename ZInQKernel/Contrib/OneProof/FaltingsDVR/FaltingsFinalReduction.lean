import ZInQKernel.Contrib.OneProof.FaltingsDVR.ClosureTorsion
import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsDVRReduction
import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsFiniteKernel
import ZInQKernel.Contrib.OneProof.NeronDVR.RelativeSquare

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace ZInQ.FaltingsRestate

open SmoothGroup ReductSplit ReductGlue DictModels.RaynaudOr ZInQ.HeightSplit
open ZInQ.SemiAbDescend ZInQ.Contrib.MilneQuasiInverse.Kernel

/-- A semiabelian group over an algebraically closed field has a finite
comparison kernel if the kernel has no nonidentity prime-to-characteristic
torsion points. -/
def SemiabelianTorsionDetectsFiniteKernel : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X Y : Over (Spec (.of k)))
    [GrpObj X] [GrpObj Y] [IsCommMonObj X] [IsCommMonObj Y]
    [Smooth X.hom] [Smooth Y.hom] [IsSeparated X.hom] [IsSeparated Y.hom]
    [QuasiCompact X.hom] [QuasiCompact Y.hom],
    ConnectedSpace X.left → HasSemiAbelianIdentityComponent X →
    ∀ (c : X ⟶ Y), IsMonHom c →
      (∀ (a : 𝟙_ (Over (Spec (.of k))) ⟶ X) (m : ℕ),
        (m : k) ≠ 0 → a ^ m = 1 → a ≫ c = 1 → a = 1) →
      Finite (kernelObject c).left

private theorem geometricPoint_eq {K : Type} [Field K] (O : ValuationSubring K) :
    sφ (φbar (IsLocalRing.ResidueField O)) ≫ closedFibreMap O = geometricPoint O := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

set_option maxHeartbeats 1500000 in
set_option synthInstance.maxHeartbeats 160000 in
/-- Dedekind Néron existence and specialization reduce the exact printed
Faltings lemma to a finite-kernel assertion for semiabelian groups
over algebraically closed fields. -/
theorem faltingsLemma1DVRPrint_of_torsion_detects_finite_kernel
    (hFin : SemiabelianTorsionDetectsFiniteKernel) : FaltingsLemma1DVRPrint := by
  apply faltingsLemma1DVRPrint_of_closed_quasiFinite_comparison
    NeronDVR.neronSchemeExtensionDedekind_proof
  intro K _ O _ A G N hG _hN i hi
  let k := IsLocalRing.ResidueField O
  let d := closedFibreMap O
  let s := sφ (φbar k)
  let F₀ := Over.pullback d
  let F₁ := Over.pullback s
  let H := Over.pullback (geometricPoint O)
  let : GrpObj (F₀.obj G.G) := Functor.grpObjObj
  let : GrpObj (F₀.obj N.G) := Functor.grpObjObj
  let : GrpObj (F₁.obj (F₀.obj G.G)) := Functor.grpObjObj
  let : GrpObj (F₁.obj (F₀.obj N.G)) := Functor.grpObjObj
  let : GrpObj (H.obj G.G) := Functor.grpObjObj
  let : GrpObj (H.obj N.G) := Functor.grpObjObj
  let isoG := pbCompIso s d (geometricPoint O) (geometricPoint_eq O) (Grp.mk G.G)
  let isoN := pbCompIso s d (geometricPoint O) (geometricPoint_eq O) (Grp.mk N.G)
  let eG : F₁.obj (F₀.obj G.G) ≅ H.obj G.G := isoX isoG
  let eN : F₁.obj (F₀.obj N.G) ≅ H.obj N.G := isoX isoN
  have : IsMonHom eG.hom := isoG.hom.hom.isMonHom_hom
  have : Smooth (F₀.obj G.G).hom := show Smooth (pullback.snd G.G.hom d) from inferInstance
  have : QuasiCompact (F₀.obj G.G).hom :=
    show QuasiCompact (pullback.snd G.G.hom d) from inferInstance
  have hs : HasSemiAbelianIdentityComponent (F₁.obj (F₀.obj G.G)) :=
    hasSemiAbelian_pullback_bar geomConnOfRationalPoint_proof (F₀.obj G.G) hG.2
  have hSemi : HasSemiAbelianIdentityComponent (H.obj G.G) :=
    hasSemiAbelian_of_iso eG hs
  have hConn : ConnectedSpace (H.obj G.G).left := by
    have : ConnectedSpace (F₀.obj G.G).left := hG.1
    have : GeometricallyConnected (F₀.obj G.G).hom :=
      geomConnOfRationalPoint_proof k _ _ η[(F₀.obj G.G)].left (Over.w η[(F₀.obj G.G)])
        inferInstance inferInstance inferInstance
    have h := GeometricallyConnected.connectedSpace_of_subsingleton
      (pullback.snd (F₀.obj G.G).hom s)
    exact (Scheme.homeoOfIso ((Over.forget _).mapIso eG)).connectedSpace_iff.mp h
  let J := Over.pullback (jO O)
  let : GrpObj (J.obj G.G) := Functor.grpObjObj
  let : GrpObj (J.obj N.G) := Functor.grpObjObj
  have : IsMonHom N.gen.hom := N.gen_hom
  have : IsMonHom (J.map i ≫ N.gen.hom) := hi ▸ G.gen_hom
  have : IsMonHom (J.map i) := isMonHom_of_comp_mono _ N.gen.hom
  have : IsMonHom i := isMonHom_of_generic G N i (J.map i) inferInstance rfl
  have : IsMonHom (H.map i) := inferInstance
  have : IsCommMonObj G.G := isCommMonObj_groupModelO G
  have : IsCommMonObj N.G := isCommMonObj_groupModelO N
  have : IsCommMonObj (H.obj G.G) := H.isCommMonObj_obj
  have : IsCommMonObj (H.obj N.G) := H.isCommMonObj_obj
  have : Smooth (H.obj G.G).hom :=
    show Smooth (pullback.snd G.G.hom (geometricPoint O)) from inferInstance
  have : Smooth (H.obj N.G).hom :=
    show Smooth (pullback.snd N.G.hom (geometricPoint O)) from inferInstance
  have : IsSeparated (H.obj G.G).hom :=
    show IsSeparated (pullback.snd G.G.hom (geometricPoint O)) from inferInstance
  have : IsSeparated (H.obj N.G).hom :=
    show IsSeparated (pullback.snd N.G.hom (geometricPoint O)) from inferInstance
  have : QuasiCompact (H.obj G.G).hom :=
    show QuasiCompact (pullback.snd G.G.hom (geometricPoint O)) from inferInstance
  have : QuasiCompact (H.obj N.G).hom :=
    show QuasiCompact (pullback.snd N.G.hom (geometricPoint O)) from inferInstance
  have : Finite (kernelObject (H.map i)).left :=
    hFin (ResBarO O) (H.obj G.G) (H.obj N.G) hConn hSemi (H.map i) inferInstance
      (torsion_kernel_trivial_over_geometricPoint G N i hi)
  have : LocallyOfFiniteType ((H.map i).left ≫ (H.obj N.G).hom) := by
    rw [Over.w]
    infer_instance
  have : LocallyOfFiniteType (H.map i).left :=
    locallyOfFiniteType_of_comp (H.map i).left (H.obj N.G).hom
  have hQ : LocallyQuasiFinite (H.map i).left :=
    locallyQuasiFinite_of_finite_kernel_points (H.map i)
  apply locallyQuasiFinite_closedFibre_of_fieldExtension G N i (ResBarO O)
  have hnat : F₁.map (F₀.map i) ≫ eN.hom = eG.hom ≫ H.map i :=
    pbCompIso_natural' s d (geometricPoint O) (geometricPoint_eq O) i
  have h : (F₁.map (F₀.map i)).left = eG.hom.left ≫ (H.map i).left ≫ eN.inv.left := by
    have h' : F₁.map (F₀.map i) = eG.hom ≫ H.map i ≫ eN.inv := by
      apply (cancel_mono eN.hom).mp
      rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, hnat]
    simpa only [Over.comp_left] using congrArg CommaMorphism.left h'
  change LocallyQuasiFinite (F₁.map (F₀.map i)).left
  rw [h]
  infer_instance

end ZInQ.FaltingsRestate
