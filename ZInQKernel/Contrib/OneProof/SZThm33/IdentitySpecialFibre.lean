import ZInQKernel.Contrib.OneProof.DirectWeil.IdentityModelPolarization
import ZInQKernel.Contrib.OneProof.SZRaynaud

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open ReductSplit ReductGlue CToPrinted

namespace SZRaynaud

variable {K : Type} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {A : PkgI3.AbVar K}

/-- Geometric semistability persists over the chosen strict henselization. -/
theorem strictModel_isSemistable {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (M : GroupModelO A O) (hM : M.IsSemistable) : (bcDVR (GapSHPair.hE_eq w hw) M).IsSemistable := by
  let V := GapSHPair.wE (K := K) w
  let hV := GapSHPair.hE_eq w hw
  have hsh := GapSHPair.isSHSep_inertia w hw
  have : IsDiscreteValuationRing V := hsh.1.1
  have hAlg : letI := (resMap hV).toAlgebra
      Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField V) := by
    let := (resMap hV).toAlgebra
    have : Algebra.IsSeparable (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField V) := hsh.2.2.2
    exact Algebra.IsSeparable.isAlgebraic _ _
  exact (isSemistable_bcDVR_iff hV hAlg M).mp hM

section Identity

variable (H M : GroupModelO A O)

/-- The geometric closed-fibre embedding obtained from a relative model map. -/
abbrev geomSpecialModelMap (i : H.G ⟶ M.G) : geomSpecialFibre H ⟶ geomSpecialFibre M :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))).map i

/-- The geometric special fibre of the relative identity subgroup has image
equal to the connected component of the identity. -/
theorem geomSpecialModelMap_range_identity (i : H.G ⟶ M.G) [IsOpenImmersion i.left]
    (hi : Set.range i.left = idCompSet M.G) :
    Set.range (geomSpecialModelMap H M i).left =
      connectedComponent ((η[geomSpecialFibre M]).left (default : Spec (.of (ResBarO O)))) := by
  let d := Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O)))
  have hm : ((Over.pullback d).map i).left =
      pullback.map H.G.hom d M.G.hom d i.left (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left]
  change Set.range ((Over.pullback d).map i).left = _
  rw [hm, Scheme.Pullback.range_map]
  have hId : Set.range ((𝟙 (Spec (.of (ResBarO O)))) : Spec (.of (ResBarO O)) ⟶ _) = Set.univ :=
    Set.range_eq_univ.mpr fun x => ⟨x, rfl⟩
  have hOpen : IsOpen (idCompSet M.G) := hi ▸ i.left.isOpenEmbedding.isOpen_range
  rw [hId, Set.preimage_univ, Set.inter_univ, hi,
    SGA3Nbhd.idComp_baseChange' geomConnOfRationalPoint_proof d M.G hOpen]
  exact ZInQ.SemiAbDescend.idCompSet_eq_cc (geomSpecialFibre M) default

/-- Any open connected subgroup used in a semistable presentation is the
geometric special fibre of the relative identity open subgroup. -/
theorem exists_geomIdentityIso (i : H.G ⟶ M.G) [IsOpenImmersion i.left] [IsMonHom i]
    (hi : Set.range i.left = idCompSet M.G)
    {U : Over (Spec (.of (ResBarO O)))} [GrpObj U] [ConnectedSpace U.left]
    (j : U ⟶ geomSpecialFibre M) [IsOpenImmersion j.left] [IsMonHom j] :
    ∃ e : U ≅ geomSpecialFibre H, IsMonHom e.hom ∧ e.hom ≫ geomSpecialModelMap H M i = j := by
  let f := geomSpecialModelMap H M i
  have : IsOpenImmersion f.left := ZInQ.H5Glue.isOpenImmersion_pullback_map
    (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O)))) i
  have : LocallyOfFiniteType (geomSpecialFibre M).hom :=
    show LocallyOfFiniteType (pullback.snd M.G.hom _) by infer_instance
  have hr : Set.range j.left = Set.range f.left :=
    (ZInQ.SemistabAssembly.range_eq_connectedComponent j).trans
      (geomSpecialModelMap_range_identity H M i hi).symm
  let e₀ := IsOpenImmersion.isoOfRangeEq j.left f.left hr
  have he₀ : e₀.hom ≫ f.left = j.left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let e : U ≅ geomSpecialFibre H := Over.isoMk e₀ (by
    rw [← Over.w f, ← Category.assoc, he₀, Over.w])
  have he : e.hom ≫ f = j := Over.OverMorphism.ext he₀
  have : Mono f := ⟨fun _ _ h => Over.OverMorphism.ext ((cancel_mono f.left).mp
    (by simpa using congrArg CommaMorphism.left h))⟩
  have : IsMonHom f := Functor.map.instIsMonHom (F := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O)))))) H.G M.G i
  have : IsMonHom (e.hom ≫ f) := he.symm ▸ inferInstanceAs (IsMonHom j)
  exact ⟨e, AVGlue.isMonHom_of_comp_mono e.hom f, he⟩

end Identity

end SZRaynaud
