import ZInQKernel.Contrib.OneProof.SZThm33.GeometricComparisonTateSurjectivity
import ZInQKernel.Contrib.OneProof.SZThm33.IdentityTateComparison
import ZInQKernel.Contrib.OneProof.SZThm33.SemiabelianTorsionDominance
import ZInQKernel.Contrib.OneProof.SZThm33.SemistableDimensions

/-! Level-two inertia action makes the canonical comparison dominant on
the geometric identity components after a semistable finite extension. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace Topology
open ReductSplit ReductGlue SmoothGroup ZInQ.HeightSplit CToPrinted
open ZInQ.FaltingsRestate (isCommMonObj_groupModelO)
open ZInQ.SemistableDimensions
open scoped IsMulCommutative

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 180000
set_option linter.style.haveILetI false

namespace SZRaynaud.Ambient

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [IsAlgClosure K Ω] [IsAlgClosure E Ω] [IsAlgClosed Ω]
  {O : ValuationSubring K} {P : ValuationSubring E} {w : ValuationSubring Ω}
  [IsDiscreteValuationRing O] [IsDiscreteValuationRing P]
  (hw : w.comap (algebraMap K Ω) = O) (hp : w.comap (algebraMap E Ω) = P)
  (hP : P.comap (algebraMap K E) = O)
  (A : PkgI3.AbVar K) (M : GroupModelO A O) (hM : M.IsNeronModel)
  (N : GroupModelO (A.baseChange E) P) (hN : N.IsNeronModel)
  (ℓ : ℕ) [Fact ℓ.Prime] (hu : IsUnit (ℓ : O))

attribute [local instance] isCommMonObj_groupModelO isCommMonObj_geomSpecialFibre
local instance : IsMonHom (neronModelComparison (bcDVR hP M) N hN) := neronModelComparison_hom (bcDVR hP M) N hN

private theorem comm_of_openSubgroup
    {k₀ : Type} [Field k₀] {X Y : Over (Spec (.of k₀))}
    [GrpObj X] [GrpObj Y] [IsCommMonObj Y] (i : X ⟶ Y)
    [IsOpenImmersion i.left] [IsMonHom i] : IsCommMonObj X := by
  letI : Mono i := Over.mono_of_mono_left i
  apply (isCommMonObj_iff_isMulCommutative X).mpr
  intro T
  refine ⟨⟨fun a b => (cancel_mono i).mp ?_⟩⟩
  rw [MonObj.mul_comp, MonObj.mul_comp, mul_comm]

private theorem isIso_generic_openIdentity
    {K : Type} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
    {A : PkgI3.AbVar K} (M : GroupModelO A O)
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
  rw [hm]
  have hmap := Scheme.Pullback.range_map (f := H.hom) (g := jO O) M.G.hom (jO O)
    i.left (𝟙 (Spec (.of K))) (𝟙 (Spec (.of O))) (by simp) (by simp)
  change (z : (pullback M.G.hom (jO O) : Scheme)) ∈ _
  rw [hmap, hi]
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
include hw hp hM hu in
/-- The two geometric identity components are integral and of the same
dimension. If the extended Néron model is semistable, the canonical
comparison is dominant on them under the level-two inertia hypothesis. -/
theorem dominant_identity_comparison_of_levelTwo
    (hNss : N.IsSemistable)
    (hTwo : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → ∀ t : VΩ A Ω ℓ,
      galVΩ A ℓ σ (galVΩ A ℓ σ t - t) = galVΩ A ℓ σ t - t) :
    ∃ (H : GroupModelO (A.baseChange E) P) (a₀ : H.G ⟶ (bcDVR hP M).G)
      (U : Over (Spec (.of (ResBarO P)))) (_ : GrpObj U)
      (b : U ⟶ geomSpecialFibre N) (f : geomSpecialFibre H ⟶ U),
      IsOpenImmersion a₀.left ∧ IsMonHom a₀ ∧ IsIso ((Over.pullback (jO P)).map a₀) ∧
      IsIntegral (geomSpecialFibre H).left ∧ IsIntegral U.left ∧ IsOpenImmersion b.left ∧
      IsMonHom b ∧ IsMonHom f ∧ f ≫ b = geomSpecialModelMap H N (a₀ ≫ (neronModelComparison (bcDVR hP M) N hN)) ∧
      topologicalKrullDim (geomSpecialFibre H).left = topologicalKrullDim U.left ∧
      IsDominant f.left := by
  obtain ⟨U, hU, b, hb, hbM, hbConn, B, π, hπM, hπFlat, hπSurj, r, e, he, hk, hn⟩ := hNss
  letI : GrpObj U := hU
  haveI : IsOpenImmersion b.left := hb
  haveI : IsMonHom b := hbM
  haveI : ConnectedSpace U.left := hbConn
  haveI : IsMonHom π := hπM
  haveI : Flat π.left := hπFlat
  haveI : Surjective π.left := hπSurj
  haveI : IsCommMonObj U := comm_of_openSubgroup b
  haveI : Smooth (geomSpecialFibre N).hom :=
    show Smooth (pullback.snd N.G.hom (Spec.map (CommRingCat.ofHom (algebraMap P (ResBarO P))))) by infer_instance
  haveI : Smooth U.hom := by rw [← Over.w b]; infer_instance
  haveI : GeometricallyConnected U.hom :=
    AlgebraicGeometry.geometricallyConnected_of_connectedSpace_of_section
      U.hom (η[U]).left (Over.w η[U])
  haveI : GeometricallyIntegral U.hom := TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral _
  haveI : IsIntegral U.left := GeometricallyIntegral.isIntegral_of_subsingleton U.hom
  have connM : ConnectedSpace ↥(pullback (bcDVR hP M).G.hom (jO P)) := by
    haveI : IsIntegral (A.baseChange E).X.left := GeometricallyIntegral.isIntegral_of_subsingleton (A.baseChange E).X.hom
    have hConn : ConnectedSpace (A.baseChange E).X.left := inferInstance
    exact (Scheme.homeoOfIso ((Over.forget _).mapIso (bcDVR hP M).gen)).connectedSpace_iff.mpr hConn
  obtain ⟨H, hH, a₀, ha₀M, ha₀, hHsm, hHgeom, hHqc, hHrange⟩ :=
    NeronDVR.exists_identitySubgroup_dvr (bcDVR hP M).G (algebraMap P E)
      (show Function.Injective (algebraMap P E) from Subtype.val_injective) connM
  letI : GrpObj H := hH
  haveI : IsMonHom a₀ := ha₀M
  haveI : IsOpenImmersion a₀.left := ha₀
  haveI : GeometricallyIntegral H.hom := hHgeom
  haveI : Smooth H.hom := hHsm
  haveI : QuasiCompact H.hom := hHqc
  haveI : IsSeparated H.hom := by rw [← Over.w a₀]; infer_instance
  haveI : IsIso ((Over.pullback (jO P)).map a₀) := isIso_generic_openIdentity (bcDVR hP M) a₀ hHrange
  let J := Over.pullback (jO P)
  letI : GrpObj (J.obj H) := Functor.grpObjObj
  letI : GrpObj (J.obj (bcDVR hP M).G) := Functor.grpObjObj
  haveI : IsMonHom (bcDVR hP M).gen.hom := (bcDVR hP M).gen_hom
  let H' : GroupModelO (A.baseChange E) P :=
    { G := H
      gen := asIso (J.map a₀) ≪≫ (bcDVR hP M).gen
      gen_hom := by change IsMonHom (J.map a₀ ≫ (bcDVR hP M).gen.hom); infer_instance }
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap P (ResBarO P))))
  let X := geomSpecialFibre H'
  let a : X ⟶ geomSpecialFibre (bcDVR hP M) := F.map a₀
  haveI : IsOpenImmersion a.left := ZInQ.H5Glue.isOpenImmersion_pullback_map (Spec.map (CommRingCat.ofHom (algebraMap P (ResBarO P)))) a₀
  haveI : IsMonHom a := Functor.map.instIsMonHom (F := F) H (bcDVR hP M).G a₀
  haveI : GeometricallyIntegral X.hom :=
    show GeometricallyIntegral (pullback.snd H.hom (Spec.map (CommRingCat.ofHom (algebraMap P (ResBarO P))))) by infer_instance
  haveI : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.hom
  haveI : IsCommMonObj X := comm_of_openSubgroup a
  haveI : LocallyOfFiniteType (geomSpecialFibre (bcDVR hP M)).hom :=
    show LocallyOfFiniteType (pullback.snd (bcDVR hP M).G.hom (Spec.map (CommRingCat.ofHom (algebraMap P (ResBarO P))))) by infer_instance
  haveI : LocallyOfFiniteType (geomSpecialFibre N).hom := inferInstance
  haveI : QuasiCompact (geomSpecialFibre (bcDVR hP M)).hom :=
    show QuasiCompact (pullback.snd (bcDVR hP M).G.hom (Spec.map (CommRingCat.ofHom (algebraMap P (ResBarO P))))) by infer_instance
  haveI : QuasiCompact (geomSpecialFibre N).hom :=
    show QuasiCompact (pullback.snd N.G.hom (Spec.map (CommRingCat.ofHom (algebraMap P (ResBarO P))))) by infer_instance
  haveI : LocallyOfFiniteType X.hom := by rw [← Over.w a]; infer_instance
  haveI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  haveI : QuasiCompact X.hom := DictModels.RaynaudOr.quasiCompact_of_openImm a
  haveI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  haveI : IsNoetherian X.left := {}
  haveI : QuasiCompact U.hom := DictModels.RaynaudOr.quasiCompact_of_openImm b
  obtain ⟨f, hf, hfM⟩ := exists_map_connectedOpenSubgroup (geomSpecialModelMap (bcDVR hP M) N (neronModelComparison (bcDVR hP M) N hN)) a b
  haveI : IsMonHom f := hfM
  haveI : QuasiCompact f.left := inferInstance
  have hβ := geomSpecialComparison_rationalTate_surjective_of_levelTwo E hw hp hP A M hM
    N hN ℓ hu hTwo
  have huP : IsUnit (ℓ : P) := by
    simpa only [map_natCast] using hu.map (ReductSplit.comapHom hP)
  have hℓ : (ℓ : (ResBarO P)) ≠ 0 := by
    simpa only [map_natCast] using (huP.map (algebraMap P (ResBarO P))).ne_zero
  have hfT := rationalTate_surjective_connectedOpenSubgroup (ℓ := ℓ) (geomSpecialModelMap (bcDVR hP M) N (neronModelComparison (bcDVR hP M) N hN)) a b f hf hβ
  obtain ⟨n, hA, hX⟩ := geometricIdentity_relDim (bcDVR hP M) X a
  obtain ⟨g, d, hA', hUdim, hB, -⟩ :=
    semistable_dimensions_of_split_presentation N U b B π r e he hk hn
  haveI : SmoothOfRelativeDimension n X.hom := hX
  have hdim : topologicalKrullDim X.left = topologicalKrullDim U.left := by
    rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension X.hom n, hUdim, ← hA, hA']
  have hdom := dominant_of_splitSemiabelian_rationalTate_surjective f B d hB π hℓ e
    (he (ResBarO P)) (hk (ResBarO P)) hn hfT
  have hf' : f ≫ b = geomSpecialModelMap H' N (a₀ ≫ (neronModelComparison (bcDVR hP M) N hN)) := by
    rw [hf]
    exact (F.map_comp a₀ (neronModelComparison (bcDVR hP M) N hN)).symm
  exact ⟨H', a₀, U, hU, b, f, ha₀, ha₀M, inferInstance, inferInstance, inferInstance,
    hb, hbM, hfM, hf', hdim, hdom⟩

#print axioms dominant_identity_comparison_of_levelTwo

end SZRaynaud.Ambient
