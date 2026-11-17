import ZInQKernel.Contrib.OneProof.SGA3NbhdOL
import ZInQKernel.Contrib.OneProof.EGAOpenImm
import ZInQKernel.Contrib.SpreadOut.NumberField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField

namespace SGA3Nbhd

/-- Open immersions of `Over`-pullback maps along a composite. -/
theorem openImm_pb_comp {X' Y' Z' : Scheme.{0}} (a : X' ⟶ Y') (b : Y' ⟶ Z') {P Q : Over Z'} (f : P ⟶ Q) :
    IsOpenImmersion ((Over.pullback (a ≫ b)).map f).left ↔
      IsOpenImmersion ((Over.pullback a).map ((Over.pullback b).map f)).left := by
  let e := Over.pullbackComp a b
  have hw := e.hom.naturality f
  refine MorphismProperty.arrow_mk_iso_iff @IsOpenImmersion
    (Arrow.isoMk ((Over.forget _).mapIso (e.app P)) ((Over.forget _).mapIso (e.app Q)) ?_)
  simp only [Functor.mapIso_hom, Iso.app_hom, Over.forget_map, Arrow.mk_hom]
  exact congrArg CommaMorphism.left hw.symm

theorem openImm_pb_congr {X' Z' : Scheme.{0}} {a a' : X' ⟶ Z'} (h : a = a') {P Q : Over Z'} (f : P ⟶ Q) :
    IsOpenImmersion ((Over.pullback a).map f).left ↔ IsOpenImmersion ((Over.pullback a').map f).left := by
  subst h; rfl

open ZInQ.Contrib.SpreadOut.NF ReductGlue in
/-- **Spreading out an open immersion from the generic fibre** (EGA IV₃ 8.10.5, the open-immersion item,
proved in the tree as `egaIV_8_10_5_openImm_proof`, for `Spec L = lim Spec 𝓞_L[1/n!]`): a morphism of smooth,
separated, quasi-compact `𝓞_L`-schemes whose generic fibre is an isomorphism is an open immersion over every
DVR `O` of `L` in which `n!` is a unit, for some `n`. -/
theorem spread_openImm {L : Type} [Field L] [NumberField L] (X Y : Over (Spec (CommRingCat.of (𝓞 L))))
    [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [Smooth Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y)
    (hf : IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).map f)) :
    ∃ n : ℕ, ∀ (O : ValuationSubring L) [IsDiscreteValuationRing O], IsUnit (toOL O (sf L n)) →
      IsOpenImmersion ((Over.pullback (gO O)).map f).left := by
  let g0 : (specDiag L).obj (Opposite.op 0) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Rg L 0)))
  let Xi : Over ((specDiag L).obj (Opposite.op 0)) := (Over.pullback g0).obj X
  let Yi : Over ((specDiag L).obj (Opposite.op 0)) := (Over.pullback g0).obj Y
  let fi : Xi ⟶ Yi := (Over.pullback g0).map f
  have hX1 : LocallyOfFinitePresentation Xi.hom :=
    show LocallyOfFinitePresentation (pullback.snd X.hom g0) from inferInstance
  have hX2 : QuasiCompact Xi.hom := show QuasiCompact (pullback.snd X.hom g0) from inferInstance
  have hX3 : QuasiSeparated Xi.hom := show QuasiSeparated (pullback.snd X.hom g0) from inferInstance
  have hY1 : LocallyOfFinitePresentation Yi.hom :=
    show LocallyOfFinitePresentation (pullback.snd Y.hom g0) from inferInstance
  have hY2 : QuasiCompact Yi.hom := show QuasiCompact (pullback.snd Y.hom g0) from inferInstance
  have hY3 : QuasiSeparated Yi.hom := show QuasiSeparated (pullback.snd Y.hom g0) from inferInstance
  have hc0 : (specCone L).π.app (Opposite.op 0) ≫ g0 =
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)) := by
    show Spec.map (CommRingCat.ofHom (toL L 0)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Rg L 0))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact toL_alg L 0 x
  have hlim : IsOpenImmersion ((Over.pullback ((specCone L).π.app (Opposite.op 0))).map fi).left := by
    rw [← openImm_pb_comp, openImm_pb_congr hc0]
    haveI := hf
    change IsOpenImmersion ((Over.forget _).map
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).map f))
    infer_instance
  obtain ⟨j, a, hj⟩ := ZInQ.Contrib.EGAOpenImm.egaIV_8_10_5_openImm_proof ℕ (specDiag L) (specCone L)
    (specConeIsLimit L) (Opposite.op 0) Xi Yi hX1 hX2 hX3 hY1 hY2 hY3 fi hlim
  refine ⟨j.unop, fun O _ hu => ?_⟩
  let ℓ : Rg L j.unop →+* O := IsLocalization.Away.lift (sf L j.unop) hu
  have heq : gO O = Spec.map (CommRingCat.ofHom ℓ) ≫ ((specDiag L).map a ≫ g0) := by
    show Spec.map _ = Spec.map _ ≫ (Spec.map _ ≫ Spec.map _)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [tr_alg]
    exact congrArg Subtype.val (IsLocalization.Away.lift_eq (sf L j.unop) hu x).symm
  haveI := hj
  have h1 : IsOpenImmersion ((Over.pullback (Spec.map (CommRingCat.ofHom ℓ))).map
      ((Over.pullback ((specDiag L).map a)).map fi)).left :=
    ZInQ.H5Glue.isOpenImmersion_pullback_map _ _
  have h2 : IsOpenImmersion ((Over.pullback (Spec.map (CommRingCat.ofHom ℓ))).map
      ((Over.pullback ((specDiag L).map a ≫ g0)).map f)).left := by
    have e := openImm_pb_comp (Spec.map (CommRingCat.ofHom ℓ)) ((specDiag L).map a ≫ g0) f
    have e2 := openImm_pb_comp ((specDiag L).map a) g0 f
    sorry
  sorry

end SGA3Nbhd
