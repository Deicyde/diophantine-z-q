import ZInQKernel.Contrib.OneProof.FaltingsDict
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace
import Mathlib.AlgebraicGeometry.AffineSpace

/-! Dimension of a semistable geometric special fibre and its torus and abelian quotient. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit CToPrinted ZInQ.HeightSplit ZInQ.SemiAbDescend
open scoped BigOperators

set_option linter.style.haveILetI false

namespace ZInQ.SemistableDimensions

/-- The split torus represented by the localized polynomial ring is smooth
of relative dimension equal to its rank. -/
theorem torus_relDim {k : Type} [Field k] (r : ℕ) :
    SmoothOfRelativeDimension r (algPt k (TorusRing k r)).hom := by
  let P := MvPolynomial (Fin r) k
  let R := TorusRing k r
  let p := Spec.map (CommRingCat.ofHom (algebraMap k P))
  let j := Spec.map (CommRingCat.ofHom (algebraMap P R))
  haveI : IsOpenImmersion j :=
    IsOpenImmersion.of_isLocalization (∏ i : Fin r, MvPolynomial.X i : P)
  haveI : SmoothOfRelativeDimension r p := by
    change SmoothOfRelativeDimension r (Spec.map (CommRingCat.ofHom (algebraMap k P)))
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension r)]
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    rw [CommRingCat.hom_ofHom, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    simpa [P] using Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial k (Fin r)
  have h : Spec.map (CommRingCat.ofHom (algebraMap k R)) = j ≫ p := by
    change _ = Spec.map (CommRingCat.ofHom (algebraMap P R)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k P))
    rw [← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq k P R]
  change SmoothOfRelativeDimension r (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  rw [h]
  simpa only [zero_add] using (inferInstance : SmoothOfRelativeDimension (0 + r) (j ≫ p))

/-- An affine functor-of-points presentation of a kernel by split torus
coordinates identifies the scheme kernel with that split torus. -/
theorem torus_kerObj_iso {k : Type} [Field k]
    {U B : Over (Spec (CommRingCat.of k))} [GrpObj U] [GrpObj B]
    (π : U ⟶ B) (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U))
    (he : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    (hk : ∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range)
    (hn : ∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
      (t : Fin r → Rˣ), e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t) :
    Nonempty (algPt k (TorusRing k r) ≅ kerObj π) := by
  let L := TorusRing k r
  have H : e L (tUniv r) ≫ π = toUnit _ ≫ η[B] :=
    (hk L _).mpr ⟨tUniv r, rfl⟩
  let j : algPt k L ⟶ kerObj π := pullback.lift (e L (tUniv r)) (toUnit _) H
  have hj : j ≫ pullback.fst π η[B] = e L (tUniv r) := pullback.lift_fst _ _ _
  have hmap (R : Type) [CommRing R] [Algebra k R] (f : L →ₐ[k] R) :
      algPtMap f ≫ e L (tUniv r) = e R (fun i => Units.map (f : L →* R) (tUniv r i)) :=
    (hn L R f (tUniv r)).symm
  have hb (R : Type) [CommRing R] [Algebra k R] :
      Function.Bijective (fun a : algPt k R ⟶ algPt k L => a ≫ j) := by
    constructor
    · intro a b hab
      obtain ⟨a', rfl⟩ := exists_algPtMap a
      obtain ⟨b', rfl⟩ := exists_algPtMap b
      have heq := congrArg (· ≫ pullback.fst π η[B]) hab
      simp only [Category.assoc, hj, hmap] at heq
      have hcoords := he R heq
      rw [algHom_ext_torus a' b' (fun i => by
        simpa using congrArg (fun t => ((t i : Rˣ) : R)) hcoords)]
    · intro b
      have hb' : (b ≫ pullback.fst π η[B]) ≫ π = 1 := by
        rw [Category.assoc, pullback.condition, ← Category.assoc,
          toUnit_unique (b ≫ pullback.snd π η[B]) (toUnit _)]
        rfl
      obtain ⟨t, ht⟩ := (hk R _).mp hb'
      refine ⟨algPtMap (torusLift t), ?_⟩
      apply pullback.hom_ext
      · simp only [Category.assoc, hj, hmap]
        rw [← ht]
        congr 1
        funext i
        ext
        exact torusLift_tUniv t i
      · exact toUnit_unique _ _
  haveI : IsIso j := isIso_of_bijective_affine j (bijective_affine_of_algPt j hb)
  exact ⟨asIso j⟩

/-- The relative smooth dimension of a faithfully flat quotient with split
torus kernel is the rank of the kernel. -/
theorem torus_quotient_relDim {k : Type} [Field k]
    {U B : Over (Spec (CommRingCat.of k))} [GrpObj U] [GrpObj B]
    (π : U ⟶ B) [IsMonHom π] [Flat π.left] [Surjective π.left] [QuasiCompact π.left]
    (r : ℕ) (E : algPt k (TorusRing k r) ≅ kerObj π) :
    SmoothOfRelativeDimension r π.left := by
  have hker : (kerObj π).hom = E.inv.left ≫ (algPt k (TorusRing k r)).hom :=
    (Over.w E.inv).symm
  haveI : SmoothOfRelativeDimension r (kerObj π).hom := by
    rw [hker]
    haveI : IsIso E.inv.left :=
      inferInstanceAs (IsIso ((Over.forget _).mapIso E).inv)
    haveI : SmoothOfRelativeDimension r (algPt k (TorusRing k r)).hom := torus_relDim r
    simpa only [zero_add] using (inferInstance :
      SmoothOfRelativeDimension (0 + r) (E.inv.left ≫ (algPt k (TorusRing k r)).hom))
  have HP : IsPullback (fst U (kerObj π)).left
      (fst U (kerObj π) * (snd U (kerObj π) ≫ pullback.fst π η[B])).left
      π.left π.left := (isPullback_shear π).map (Over.forget _)
  haveI : SmoothOfRelativeDimension r (fst U (kerObj π)).left :=
    show SmoothOfRelativeDimension r (pullback.fst U.hom (kerObj π).hom) by infer_instance
  exact ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.SmoothOfRelativeDimension.of_isPullback_of_flat_of_surjective r HP

set_option backward.isDefEq.respectTransparency false in
private theorem smoothRelDim_of_meeting_chart {k : Type} [Field k] {X S : Scheme.{0}}
    (f : X ⟶ S) [Smooth f] (t : Spec (CommRingCat.of k) ⟶ S)
    {Y : Scheme.{0}} (i : Y ⟶ pullback f t) [IsOpenImmersion i] [ConnectedSpace Y]
    (V : X.Opens) {n : ℕ} (hn : SmoothOfRelativeDimension n (V.ι ≫ f))
    (hV : Nonempty (i ⁻¹ᵁ (pullback.fst f t ⁻¹ᵁ V) : Y.Opens)) :
    SmoothOfRelativeDimension n (i ≫ pullback.snd f t) := by
  let g := pullback.snd f t
  let W := pullback.fst f t ⁻¹ᵁ V
  let U := i ⁻¹ᵁ W
  letI : Nonempty U := hV
  haveI : SmoothOfRelativeDimension n (W.ι ≫ g) :=
    MorphismProperty.of_isPullback
      ((isPullback_morphismRestrict (pullback.fst f t) V).paste_vert
        (IsPullback.of_hasPullback f t)) hn
  have hU : SmoothOfRelativeDimension n (U.ι ≫ i ≫ g) := by
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    haveI : IsOpenImmersion (i ∣_ W) := inferInstance
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) ((i ∣_ W) ≫ W.ι ≫ g))
  haveI : Smooth (i ≫ g) := inferInstance
  obtain ⟨m, hm⟩ :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace
      (i ≫ g)
  haveI : SmoothOfRelativeDimension m (i ≫ g) := hm
  have hmU : SmoothOfRelativeDimension m (U.ι ≫ i ≫ g) := by
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + m) (U.ι ≫ (i ≫ g)))
  obtain rfl := SmoothOfRelativeDimension.eq_of_field (U.ι ≫ i ≫ g) hmU hU
  exact hm

set_option backward.isDefEq.respectTransparency false in
/-- A smooth chart at the closed unit gives the same dimension on the generic
abelian fibre and on its open connected geometric special subgroup. -/
theorem geometricIdentity_relDim {K : Type} [Field K] {O : ValuationSubring K}
    [IsDiscreteValuationRing O] {A : PkgI3.AbVar K} (G : GroupModelO A O)
    (U : Over (Spec (CommRingCat.of (ResBarO O)))) [GrpObj U] [ConnectedSpace U.left]
    (i : U ⟶ geomSpecialFibre G) [IsOpenImmersion i.left] [IsMonHom i] :
    ∃ n : ℕ, A.dim = n ∧ SmoothOfRelativeDimension n U.hom := by
  let S := Spec (CommRingCat.of O)
  let f := G.G.hom
  let fUnit : S ⟶ G.G.left := (η[G.G] : 𝟙_ (Over S) ⟶ G.G).left
  let x := fUnit (IsLocalRing.closedPoint O)
  obtain ⟨V₀, V, -, -, hx, hle, n, hn⟩ :=
    Smooth.exists_smoothOfRelativeDimension_resLE f x
  have hrank : SmoothOfRelativeDimension n (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f hle]
    exact smoothOfRelativeDimension_comp (n := n) (m := 0) _ _
  have hunit (s : S) : fUnit s ∈ V :=
    ((IsLocalRing.specializes_closedPoint s).map fUnit.continuous).mem_open V.2 hx
  let J := Over.pullback (jO O)
  letI : GrpObj (J.obj G.G) := Functor.grpObjObj
  haveI : ConnectedSpace (pullback f (jO O) : Scheme) := by
    haveI : IrreducibleSpace A.X.left :=
      GeometricallyIrreducible.irreducibleSpace_of_subsingleton A.X.hom
    exact (Scheme.homeoOfIso ((Over.forget _).mapIso G.gen)).connectedSpace_iff.mpr
      (inferInstance : ConnectedSpace A.X.left)
  let ηJ : Spec (CommRingCat.of K) ⟶ pullback f (jO O) :=
    (η[J.obj G.G] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ _).left
  have hηJ : ηJ ≫ pullback.fst f (jO O) = jO O ≫ fUnit :=
    unit_bc_fst (jO O) G.G
  have hMeetJ : Nonempty ((𝟙 (pullback f (jO O))) ⁻¹ᵁ
      (pullback.fst f (jO O) ⁻¹ᵁ V) : (pullback f (jO O)).Opens) := by
    let a : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
    refine ⟨⟨ηJ a, ?_⟩⟩
    change (ηJ ≫ pullback.fst f (jO O)) a ∈ V
    rw [hηJ]
    exact hunit (jO O a)
  have hJ := smoothRelDim_of_meeting_chart f (jO O) (𝟙 _) V hrank hMeetJ
  haveI : SmoothOfRelativeDimension n (pullback.snd f (jO O)) := by simpa using hJ
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (pullback.snd f (jO O)) n
  have hA : A.dim = n := (ZInQ.FaltingsRestate.genericFibre_dim_eq G).symm.trans hdim
  let k := ResBarO O
  let d := Spec.map (CommRingCat.ofHom (algebraMap O k))
  let ηU : Spec (CommRingCat.of k) ⟶ U.left :=
    (η[U] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ U).left
  have hηU : (ηU ≫ i.left) ≫ pullback.fst f d = d ≫ fUnit := by
    have h : ηU ≫ i.left = (η[geomSpecialFibre G]).left :=
      congrArg CommaMorphism.left (IsMonHom.one_hom i)
    rw [h]
    exact unit_bc_fst d G.G
  have hMeetU : Nonempty (i.left ⁻¹ᵁ (pullback.fst f d ⁻¹ᵁ V) : U.left.Opens) := by
    let a : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
    refine ⟨⟨ηU a, ?_⟩⟩
    change ((ηU ≫ i.left) ≫ pullback.fst f d) a ∈ V
    rw [hηU]
    exact hunit (d a)
  have hUdim := smoothRelDim_of_meeting_chart f d i.left V hrank hMeetU
  have hfU : i.left ≫ pullback.snd f d = U.hom := Over.w i
  exact ⟨n, hA, hfU ▸ hUdim⟩

set_option backward.isDefEq.respectTransparency false in
/-- The generic dimension equals the dimension of the geometric connected
special subgroup. This dimension is the abelian quotient dimension plus
the rank of the actual split torus in the semistable presentation. -/
theorem semistable_dimensions_of_split_presentation {K : Type} [Field K] {O : ValuationSubring K}
    [IsDiscreteValuationRing O] {A : PkgI3.AbVar K} (G : GroupModelO A O)
    (U : Over (Spec (CommRingCat.of (ResBarO O)))) [GrpObj U] [ConnectedSpace U.left]
    (i : U ⟶ geomSpecialFibre G) [IsOpenImmersion i.left] [IsMonHom i]
    (B : PkgI3.AbVar (ResBarO O)) (π : U ⟶ B.X) [IsMonHom π] [Flat π.left] [Surjective π.left]
    (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (ResBarO O) R],
      (Fin r → Rˣ) →* (algPt (ResBarO O) R ⟶ U))
    (he : ∀ (R : Type) [CommRing R] [Algebra (ResBarO O) R], Function.Injective (e R))
    (hk : ∀ (R : Type) [CommRing R] [Algebra (ResBarO O) R] (u : algPt (ResBarO O) R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range)
    (hn : ∀ (R S : Type) [CommRing R] [Algebra (ResBarO O) R] [CommRing S] [Algebra (ResBarO O) S]
      (f : R →ₐ[ResBarO O] S) (t : Fin r → Rˣ),
      e S (fun j => Units.map (f : R →* S) (t j)) = algPtMap f ≫ e R t) :
    ∃ g b : ℕ, A.dim = g ∧ topologicalKrullDim U.left = g ∧ B.dim = b ∧ g = b + r := by
  obtain ⟨g, hA, hU⟩ := geometricIdentity_relDim G U i
  haveI : SmoothOfRelativeDimension g U.hom := hU
  haveI : LocallyOfFiniteType (geomSpecialFibre G).hom :=
    show LocallyOfFiniteType (pullback.snd G.G.hom _) by infer_instance
  haveI : QuasiCompact (geomSpecialFibre G).hom :=
    show QuasiCompact (pullback.snd G.G.hom _) by infer_instance
  haveI : QuasiCompact U.hom := DictModels.RaynaudOr.quasiCompact_of_openImm i
  haveI : LocallyOfFiniteType U.hom := by rw [← Over.w i]; infer_instance
  haveI : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  haveI : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace U.hom
  haveI : IsNoetherian U.left := {}
  haveI : QuasiCompact π.left := inferInstance
  obtain ⟨E⟩ := torus_kerObj_iso π r e he hk hn
  haveI : SmoothOfRelativeDimension r π.left := torus_quotient_relDim π r E
  haveI : IrreducibleSpace B.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton B.X.hom
  obtain ⟨b, hB⟩ :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace
      B.X.hom
  haveI : SmoothOfRelativeDimension b B.X.hom := hB
  have hSum : SmoothOfRelativeDimension (r + b) U.hom := by
    rw [← Over.w π]
    infer_instance
  refine ⟨g, b, hA, topologicalKrullDim_eq_of_smoothOfRelativeDimension U.hom g,
    topologicalKrullDim_eq_of_smoothOfRelativeDimension B.X.hom b, ?_⟩
  exact (SmoothOfRelativeDimension.eq_of_field U.hom hU hSum).trans (Nat.add_comm _ _)

end ZInQ.SemistableDimensions
