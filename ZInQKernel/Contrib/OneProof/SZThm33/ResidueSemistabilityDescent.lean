import ZInQKernel.Contrib.OneProof.SZThm33.SemiabelianQuotientDescent

/-! Geometric semistability gives a torus presentation over the original
residue field. The descent of the identity component follows Jack McCarthy's
`SemiAbelianDescendsPerfect.lean` and `ChevalleyFree.lean`. Here the
toric kernel descends over an arbitrary residue field. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.HeightSplit ZInQ.ChevFree ZInQ.SemiAbDescend DictModels.RaynaudOr ReductSplit

set_option linter.style.haveILetI false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

namespace SZRaynaud

open CToPrinted in
/-- A smooth connected geometric semiabelian identity component descends
as a semiabelian identity component over any field. -/
theorem hasSemiAbelianIdCompTorus_of_geometric
    (k : Type) [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (hbar : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj G) := Functor.grpObjObj
      HasSemiAbelianIdentityComponent ((Over.pullback (sφ (φbar k))).obj G)) :
    HasSemiAbelianIdCompTorus G := by
  have hG : AVGlue.GeomConnOfRationalPoint := geomConnOfRationalPoint_proof
  let φ := φbar k
  let F := Over.pullback (sφ φ)
  letI : GrpObj (F.obj G) := Functor.grpObjObj
  obtain ⟨U', _, inc', hoi', hmh', hcon', B', π', hπm', hfl', hsu', r, e', he_inj', he_ker', he_nat'⟩ :=
    hbar
  haveI := hoi'
  haveI : LocallyOfFiniteType (F.obj G).hom := by
    change LocallyOfFiniteType (pullback.snd G.hom (sφ φ)); infer_instance
  haveI : QuasiCompact (F.obj G).hom := by
    change QuasiCompact (pullback.snd G.hom (sφ φ)); infer_instance
  -- (a) `G⁰` over `k`
  have hW := isSubgroupOpen_W0 G hG
  letI : GrpObj (OpenSub.G0 (W0 G)) := OpenSub.grpG0 hW
  have hinc : IsMonHom (OpenSub.incl (W0 G)) := OpenSub.isMonHom_incl hW
  let U := OpenSub.G0 (W0 G)
  let incl : U ⟶ G := OpenSub.incl (W0 G)
  haveI : IsOpenImmersion incl.left := inferInstanceAs (IsOpenImmersion (W0 G).ι)
  haveI : LocallyOfFiniteType ((W0 G).ι ≫ G.hom) := inferInstance
  haveI : QuasiCompact ((W0 G).ι ≫ G.hom) := quasiCompact_of_openImm incl
  haveI : LocallyOfFiniteType U.hom := inferInstanceAs (LocallyOfFiniteType ((W0 G).ι ≫ G.hom))
  haveI : QuasiCompact U.hom := inferInstanceAs (QuasiCompact ((W0 G).ι ≫ G.hom))
  have hconnU : ConnectedSpace U.left := connectedSpace_W0 G
  letI : GrpObj (F.obj U) := Functor.grpObjObj
  have hconnFU : ConnectedSpace (F.obj U).left :=
    connectedSpace_pullback_idComp hG G (W0 G) rfl (AlgebraicClosure k) (sφ φ)
  haveI : QuasiCompact (F.obj U).hom := by
    change QuasiCompact (pullback.snd U.hom (sφ φ)); infer_instance
  -- (b) `U' = (G⁰)_{k̄}` inside `G_{k̄}`
  let p := pullback.fst G.hom (sφ φ)
  have hsq := pbmap_isPullback (sφ φ) U G incl
  haveI hFinc : IsOpenImmersion (F.map incl).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq (inferInstanceAs (IsOpenImmersion (W0 G).ι))
  have hrangeU : Set.range (F.map incl).left = p ⁻¹' (idCompSet G) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      show p ((F.map incl).left y) ∈ idCompSet G
      rw [← Scheme.Hom.comp_apply, ← hsq.w, Scheme.Hom.comp_apply]
      have : incl.left (pullback.fst U.hom (sφ φ) y) ∈ Set.range (W0 G).ι := ⟨_, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    · intro hx
      have hx' : p x ∈ Set.range (W0 G).ι := by rw [Scheme.Opens.range_ι]; exact hx
      obtain ⟨u, hu⟩ := hx'
      obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := incl.left) (g := p) u x hu
      refine ⟨hsq.isoPullback.inv z, ?_⟩
      rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_snd, hz2]
  let pt : (𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure k))))).left :=
    (default : Spec (CommRingCat.of (AlgebraicClosure k)))
  let ebar := (η[F.obj G] : 𝟙_ _ ⟶ F.obj G).left pt
  have he1 : ebar ∈ Set.range inc'.left :=
    ⟨(η[U'] : 𝟙_ _ ⟶ U').left pt, by rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom inc']⟩
  have he2 : ebar ∈ p ⁻¹' idCompSet G := by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, unit_bc_fst, Scheme.Hom.comp_apply]
    exact idCompSet_one G _
  have hclo : IsClopen (p ⁻¹' idCompSet G) :=
    ⟨(isClosed_idCompSet G).preimage p.continuous, (isOpen_idCompSet G).preimage p.continuous⟩
  have hsub1 : Set.range inc'.left ⊆ p ⁻¹' idCompSet G :=
    (isConnected_range inc'.left.continuous).isPreconnected.subset_isClopen hclo ⟨ebar, he1, he2⟩
  have hR'clo : IsClopen (Set.range inc'.left) :=
    ⟨isClosed_range_openSubgroup inc', inc'.left.isOpenEmbedding.isOpen_range⟩
  have hpre : _root_.IsPreconnected (p ⁻¹' idCompSet G) := by
    rw [← hrangeU]; exact (isConnected_range (F.map incl).left.continuous).isPreconnected
  have hsub2 : p ⁻¹' idCompSet G ⊆ Set.range inc'.left :=
    hpre.subset_isClopen hR'clo ⟨ebar, he2, he1⟩
  have heq : Set.range (F.map incl).left = Set.range inc'.left := by
    rw [hrangeU]; exact hsub2.antisymm hsub1
  let isoS := IsOpenImmersion.isoOfRangeEq (F.map incl).left inc'.left heq
  have hfac : isoS.hom ≫ inc'.left = (F.map incl).left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let φU : F.obj U ≅ U' := Over.isoMk isoS (by
    have h1 : U'.hom = inc'.left ≫ (F.obj G).hom := (Over.w inc').symm
    rw [h1, ← Category.assoc, hfac]; exact Over.w (F.map incl))
  have hφU : φU.hom ≫ inc' = F.map incl := by
    apply Over.OverMorphism.ext; exact hfac
  haveI : Mono inc' := ⟨fun g h hgh => Over.OverMorphism.ext ((cancel_mono inc'.left).mp
    (by simpa using congrArg CommaMorphism.left hgh))⟩
  haveI : IsMonHom (φU.hom ≫ inc') := by rw [hφU]; infer_instance
  haveI : IsMonHom φU.hom := isMonHom_of_comp_mono φU.hom inc'
  haveI : IsMonHom (φU.inv ≫ φU.hom) := by rw [Iso.inv_hom_id]; infer_instance
  haveI : IsMonHom φU.inv := isMonHom_of_comp_mono φU.inv φU.hom
  -- (c) the kernels of `π'` and of `φU ≫ π'` are split tori
  have hkerπ' := isSmoothConnAffineKer_of_torus π' r e' he_inj' he_ker' he_nat'
  let e2 : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ F.obj U) :=
    fun R _ _ => (IsMonHom.monoidHom φU.inv (algPt _ R)).comp (e' R)
  have he2_apply : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] (t : Fin r → Rˣ),
      e2 R t = e' R t ≫ φU.inv := fun _ _ _ _ => rfl
  have he_inj2 : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      Function.Injective (e2 R) := by
    intro R _ _ t₁ t₂ h
    rw [he2_apply, he2_apply] at h
    exact he_inj' R ((cancel_mono φU.inv).mp h)
  have he_ker2 : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ F.obj U), u ≫ (φU.hom ≫ π') = 1 ↔ u ∈ (e2 R).range := by
    intro R _ _ u
    rw [← Category.assoc, he_ker' R (u ≫ φU.hom)]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by rw [he2_apply, ht, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, by rw [he2_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩
  have he_nat2 : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e2 S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e2 R t := by
    intro R S _ _ _ _ f t
    rw [he2_apply, he2_apply, he_nat', Category.assoc]
  -- (d) smoothness: `U'`, `(G⁰)_{k̄}`, `G⁰`
  haveI : LocallyOfFiniteType U'.hom := by rw [← Over.w inc']; infer_instance
  haveI : QuasiCompact U'.hom := quasiCompact_of_openImm inc'
  haveI : IsLocallyNoetherian U'.left := LocallyOfFiniteType.isLocallyNoetherian U'.hom
  haveI : CompactSpace U'.left := QuasiCompact.compactSpace_of_compactSpace U'.hom
  haveI : IsNoetherian U'.left := {}
  have hsmU' : Smooth U'.hom := smooth_of_smoothKer π' hfl' hsu' inferInstance hkerπ'.1
  have hsmFU : Smooth (F.obj U).hom := by
    rw [← Over.w φU.hom]
    haveI : IsIso φU.hom.left := by change IsIso ((Over.forget _).map φU.hom); infer_instance
    infer_instance
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (sφ φ) :=
    ⟨⟨⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩, inferInstance⟩, inferInstance⟩
  have hsmU : Smooth U.hom :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := U.hom) (g := sφ φ) hQ hsmFU
  -- (e) descent of the quotient `(B', φU ≫ π')` to `k`
  haveI : IsIso φU.hom.left := by change IsIso ((Over.forget _).map φU.hom); infer_instance
  have hfl2 : Flat (φU.hom ≫ π').left := by
    haveI := hfl'; change Flat (φU.hom.left ≫ π'.left); infer_instance
  have hsu2 : Surjective (φU.hom ≫ π').left := by
    haveI := hsu'; change Surjective (φU.hom.left ≫ π'.left); infer_instance
  obtain ⟨B, π, hπm, hπfl, hπsu, huniq⟩ :=
    descend_semiabelian_quotient k U hsmU inferInstance hconnU B' (φU.hom ≫ π') inferInstance hfl2 hsu2 r e2 he_inj2 he_ker2 he_nat2
  haveI := hπm
  letI : GrpObj (F.obj B.X) := Functor.grpObjObj
  -- (f) assemble
  refine ⟨U, inferInstance, incl, inferInstanceAs (IsOpenImmersion (W0 G).ι), hinc, hconnU, B, π, hπm,
    hπfl, hπsu, r, fun R _ _ => (Φ φ U R).toMonoidHom.comp (e2 R), ?_, ?_, ?_⟩
  · intro R _ _
    exact (Φ φ U R).injective.comp (he_inj2 R)
  · intro R _ _ u
    letI := algK φ R
    have h1 : u ≫ π = 1 ↔ (Φ φ U R).symm u ≫ F.map π = 1 := by
      constructor
      · intro h
        apply (Φ φ B.X R).injective
        rw [Φ_comp, MulEquiv.apply_symm_apply, h, map_one]
      · intro h
        have := congrArg (Φ φ B.X R) h
        rwa [Φ_comp, MulEquiv.apply_symm_apply, map_one] at this
    rw [h1, huniq, he_ker2]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by simp [ht]⟩
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply] at ht
      rw [← ht, MulEquiv.symm_apply_apply]
  · intro R S _ _ _ _ f t
    letI := algK φ R
    letI := algK φ S
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [he_nat2 R S f t, Φ_natural]


open ReductGlue in
set_option backward.isDefEq.respectTransparency false in
/-- The geometric special fibre is semiabelian exactly when the residue
special fibre has a semiabelian identity component with a torus kernel. -/
theorem isSemistableResT_of_geometric {K : Type} [Field K]
    {O : ValuationSubring K} {A : PkgI3.AbVar K} (M : GroupModelO A O)
    (h : M.IsSemistable) : IsSemistableResT M := by
  let G := UnipotentForward.specialFibre M
  haveI : LocallyOfFiniteType G.hom :=
    show LocallyOfFiniteType (pullback.snd M.G.hom (UnipotentForward.sRes O)) by infer_instance
  haveI : QuasiCompact G.hom :=
    show QuasiCompact (pullback.snd M.G.hom (UnipotentForward.sRes O)) by infer_instance
  let E := pbCompIso _ _ _ (spec_bar_comp O) (Grp.mk M.G)
  letI : GrpObj ((Over.pullback (sφ (φbar (IsLocalRing.ResidueField O)))).obj G) := Functor.grpObjObj
  have hbar := @hasSemiAbelian_of_iso _ _ (geomSpecialFibre M)
    ((Over.pullback (sφ (φbar (IsLocalRing.ResidueField O)))).obj G)
    Functor.grpObjObj Functor.grpObjObj (isoX E).symm E.inv.hom.isMonHom_hom h
  exact hasSemiAbelianIdCompTorus_of_geometric _ G hbar

#print axioms hasSemiAbelianIdCompTorus_of_geometric
#print axioms isSemistableResT_of_geometric

end SZRaynaud
