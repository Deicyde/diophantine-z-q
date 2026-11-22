import ZInQKernel.Contrib.OneProof.DirectWeil.RelativeModelPolarization
import ZInQKernel.Contrib.OneProof.FaltingsDict
import ZInQKernel.Contrib.OneProof.NeronBaseChangeStrictHenselization

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit CToPrinted
open scoped CategoryTheory.MonObj

namespace SZRaynaud.Relative

open ZInQ.Contrib.CloudR2Poincare.L2 (VeryAmple)

variable {K : Type} [Field K] {A : PkgI3.AbVar K}
  {O : ValuationSubring K} [IsDiscreteValuationRing O]

private theorem generic_openSubgroup_isIso (M : GroupModelO A O)
    {H : Over (Spec (.of O))} (i : H ⟶ M.G) [IsOpenImmersion i.left]
    (hi : Set.range i.left = idCompSet M.G) : IsIso ((Over.pullback (jO O)).map i) := by
  suffices h : IsIso ((Over.pullback (jO O)).map i).left by
    have : IsIso ((Over.forget _).map ((Over.pullback (jO O)).map i)) := h
    exact isIso_of_reflects_iso _ (Over.forget _)
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨ZInQ.H5Glue.isOpenImmersion_pullback_map _ i, ⟨fun z => ?_⟩⟩
  show z ∈ Set.range ((Over.pullback (jO O)).map i).left
  have hm : ((Over.pullback (jO O)).map i).left =
      pullback.map H.hom (jO O) M.G.hom (jO O) i.left (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left]
  rw [hm, Scheme.Pullback.range_map, hi]
  refine ⟨?_, ⟨_, rfl⟩⟩
  apply SGA3Nbhd.mem_idCompSet_groupModelO_generic M
  have hbase : M.G.hom (pullback.fst M.G.hom (jO O) z) =
      jO O (pullback.snd M.G.hom (jO O) z) := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  rw [hbase]
  intro h
  have hp := congrArg PrimeSpectrum.asIdeal h
  change Ideal.comap (algebraMap O K) (pullback.snd M.G.hom (jO O) z).asIdeal =
    IsLocalRing.maximalIdeal O at hp
  have h0 : (pullback.snd M.G.hom (jO O) z).asIdeal = ⊥ :=
    (Ideal.eq_bot_or_top _).resolve_right (pullback.snd M.G.hom (jO O) z).isPrime.ne_top
  rw [h0, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective O K)] at hp
  exact (IsDiscreteValuationRing.not_a_field O) hp.symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 450000 in
/-- A line on the identity component of the given model, very ample on its
actual generic fibre. The identification with the original abelian variety
is the one obtained from the open subgroup inclusion. -/
theorem exists_identityModelLine [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)]
    (M : GroupModelO A O) :
    ∃ (H : GroupModelO A O) (i : H.G ⟶ M.G) (L : H.G.left.Modules),
      IsOpenImmersion i.left ∧ IsMonHom i ∧ Set.range i.left = idCompSet M.G ∧
      GeometricallyIntegral H.G.hom ∧ ((Over.pullback (jO O)).map i ≫ M.gen.hom = H.gen.hom) ∧
      L.IsInvertible ∧ VeryAmple ((Over.pullback (jO O)).obj H.G).hom
        ((Scheme.Modules.pullback (pullback.fst H.G.hom (jO O))).obj L) := by
  let F := Over.pullback (jO O)
  have hConnected : ConnectedSpace ↥(pullback M.G.hom (jO O)) := by
    have : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
    have hA : ConnectedSpace ↥A.X.left := inferInstance
    exact (Scheme.homeoOfIso ((Over.forget _).mapIso M.gen)).connectedSpace_iff.mpr hA
  obtain ⟨H, hGrp, i, hi, hopen, hsmooth, hGeom, hqc, hr⟩ :=
    NeronDVR.exists_identitySubgroup_dvr M.G (algebraMap O K)
      (FaithfulSMul.algebraMap_injective O K) hConnected
  have : IsIso (F.map i) := generic_openSubgroup_isIso M i hr
  have hsep : IsSeparated H.hom := by
    rw [← Over.w i]
    infer_instance
  let e : F.obj H ≅ A.X := asIso (F.map i) ≪≫ M.gen
  let : GrpObj (F.obj H) := Functor.grpObjObj
  let : GrpObj (F.obj M.G) := Functor.grpObjObj
  have := M.gen_hom
  have : IsProper (Generic (K := K) H).hom := by
    change IsProper (F.obj H).hom
    rw [← Over.w e.hom]
    infer_instance
  obtain ⟨L, hL, hv⟩ := exists_modelLine_genericVeryAmple (K := K) H
  let Hmodel : GroupModelO A O :=
    { G := H
      gen := e
      gen_hom := by
        change IsMonHom (F.map i ≫ M.gen.hom)
        infer_instance }
  exact ⟨Hmodel, i, L, hopen, hi, hr, hGeom, rfl, hL, hv⟩

/-- The actual restriction of the model bundle to the abelian variety,
using the model's specified generic-fibre identification. -/
def genericModelLine (M : GroupModelO A O) (L : M.G.left.Modules) : A.X.left.Modules :=
  (Scheme.Modules.pullback M.gen.inv.left).obj
    ((Scheme.Modules.pullback (pullback.fst M.G.hom (jO O))).obj L)

omit [IsDiscreteValuationRing O] in
theorem veryAmple_genericModelLine (M : GroupModelO A O) (L : M.G.left.Modules)
    (hL : VeryAmple ((Over.pullback (jO O)).obj M.G).hom
      ((Scheme.Modules.pullback (pullback.fst M.G.hom (jO O))).obj L)) :
    VeryAmple A.X.hom (genericModelLine M L) := by
  have : IsIso M.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).mapIso M.gen).inv)
  simpa only [genericModelLine, Over.w M.gen.inv] using hL.closedRestriction M.gen.inv.left

/-- A polarization on the identity component of the Néron model over the
strict henselization inside the chosen algebraic closure. -/
theorem exists_inertiaFieldModelLine {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (M : GroupModelO A O) (hM : M.IsNeronModel) :
    let E := GapSHPair.inertiaField (K := K) w
    let V := GapSHPair.wE (K := K) w
    let N := ReductGlue.bcDVR (GapSHPair.hE_eq w hw) M
    N.IsNeronModel ∧
      ∃ (H : GroupModelO (A.baseChange E) V) (i : H.G ⟶ N.G) (L : H.G.left.Modules),
        IsOpenImmersion i.left ∧ IsMonHom i ∧ Set.range i.left = idCompSet N.G ∧
        GeometricallyIntegral H.G.hom ∧ ((Over.pullback (jO V)).map i ≫ N.gen.hom = H.gen.hom) ∧
        L.IsInvertible ∧ VeryAmple (A.baseChange E).X.hom (genericModelLine H L) := by
  dsimp only
  let E := GapSHPair.inertiaField (K := K) w
  let V := GapSHPair.wE (K := K) w
  let hV := GapSHPair.hE_eq w hw
  let N := ReductGlue.bcDVR hV M
  have hsh := GapSHPair.isSHSep_inertia w hw
  have : IsDiscreteValuationRing V := hsh.1.1
  have : HenselianLocalRing V := hsh.1.2.1
  have : IsSepClosed (IsLocalRing.ResidueField V) := hsh.1.2.2
  have hN : N.IsNeronModel :=
    NeronSH.neronBaseChangeStrictHenselization_proof K O E V hV hsh A M hM
  obtain ⟨H, i, L, hOpen, hHom, hr, hGeom, hgen, hInv, hVery⟩ := exists_identityModelLine N
  exact ⟨hN, H, i, L, hOpen, hHom, hr, hGeom, hgen, hInv, veryAmple_genericModelLine H L hVery⟩

end SZRaynaud.Relative
