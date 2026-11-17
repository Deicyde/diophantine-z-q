import ZInQKernel.Contrib.OneProof.PicDictionary
import ZInQKernel.Contrib.OneProof.GeomConnOfRationalPoint
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Group.Translations
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Geometrically.Irreducible

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Topology TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace IdCompLFT

/-! ## Part A: topology -/

section Top

variable {X : Type*} [TopologicalSpace X]

/-- The union of two open irreducible sets that meet is irreducible (copy of gt-sga3's lemma). -/
theorem isIrreducible_union_of_open {V W : Set X} (hV : IsIrreducible V) (hW : IsIrreducible W)
    (hVo : IsOpen V) (_hWo : IsOpen W) (hVW : (V ∩ W).Nonempty) : IsIrreducible (V ∪ W) := by
  refine ⟨hV.nonempty.mono Set.subset_union_left, ?_⟩
  intro u v hu hv hu' hv'
  have toV : ∀ {u : Set X}, IsOpen u → ((V ∪ W) ∩ u).Nonempty → (V ∩ u).Nonempty := by
    intro u hu h
    obtain ⟨z, hz | hz, hzu⟩ := h
    · exact ⟨z, hz, hzu⟩
    · obtain ⟨y, hyW, hyu, hyV⟩ := hW.2 u V hu hVo ⟨z, hz, hzu⟩ (hVW.mono fun a h => ⟨h.2, h.1⟩)
      exact ⟨y, hyV, hyu⟩
  obtain ⟨y, hyV, hyu, hyv⟩ := hV.2 u v hu hv (toV hu hu') (toV hv hv')
  exact ⟨y, Or.inl hyV, hyu, hyv⟩

/-- In a noetherian space connected components are open (copy of gt-rigidity's lemma). -/
theorem isOpen_cc_of_noetherianSpace [NoetherianSpace X] (x : X) :
    IsOpen (connectedComponent x) := by
  classical
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := X)
  have hc : (connectedComponent x)ᶜ =
      ⋃₀ {Z ∈ irreducibleComponents X | Z ∩ connectedComponent x = ∅} := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_ofPred_eq]
    constructor
    · intro hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩,
        mem_irreducibleComponent⟩
      by_contra hne
      obtain ⟨z, hzZ, hzC⟩ := Set.nonempty_iff_ne_empty.2 hne
      apply hy
      have hZc : irreducibleComponent y ⊆ connectedComponent z :=
        (IsIrreducible.isConnected (isIrreducible_irreducibleComponent (x := y))).isPreconnected
          |>.subset_connectedComponent hzZ
      rw [connectedComponent_eq hzC]
      exact hZc mem_irreducibleComponent
    · rintro ⟨Z, ⟨-, hZC⟩, hyZ⟩ hyC
      exact (Set.eq_empty_iff_forall_notMem.1 hZC) y ⟨hyZ, hyC⟩
  rw [← isClosed_compl_iff, hc]
  exact (hfin.subset (fun Z hZ => hZ.1)).isClosed_sUnion
    (fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1)

/-- If every point has an open irreducible neighbourhood, a connected space is irreducible. -/
theorem irreducibleSpace_of_nbhd [ConnectedSpace X]
    (h : ∀ x : X, ∃ V : Set X, IsOpen V ∧ IsIrreducible V ∧ x ∈ V) : IrreducibleSpace X := by
  -- any two points lie in a common open irreducible set
  have h2 : ∀ x y : X, ∃ V : Set X, IsOpen V ∧ IsIrreducible V ∧ x ∈ V ∧ y ∈ V := by
    intro x
    let R : Set X := {y | ∃ V : Set X, IsOpen V ∧ IsIrreducible V ∧ x ∈ V ∧ y ∈ V}
    have hRo : IsOpen R := by
      rw [isOpen_iff_forall_mem_open]
      rintro y ⟨V, hVo, hVi, hxV, hyV⟩
      exact ⟨V, fun z hz => ⟨V, hVo, hVi, hxV, hz⟩, hVo, hyV⟩
    have hRc : IsClosed R := by
      rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro y hy
      obtain ⟨W, hWo, hWi, hyW⟩ := h y
      refine ⟨W, ?_, hWo, hyW⟩
      rintro z hzW ⟨V, hVo, hVi, hxV, hzV⟩
      exact hy ⟨V ∪ W, hVo.union hWo,
        isIrreducible_union_of_open hVi hWi hVo hWo ⟨z, hzV, hzW⟩, Or.inl hxV,
        Or.inr hyW⟩
    have hxR : x ∈ R := by
      obtain ⟨V, hVo, hVi, hxV⟩ := h x
      exact ⟨V, hVo, hVi, hxV, hxV⟩
    have hR : R = Set.univ := (isClopen_iff.mp ⟨hRc, hRo⟩).resolve_left (Set.nonempty_of_mem hxR).ne_empty
    intro y
    have : y ∈ R := hR ▸ Set.mem_univ y
    exact this
  rw [irreducibleSpace_def]
  refine ⟨Set.univ_nonempty, ?_⟩
  rintro u v hu hv ⟨a, -, ha⟩ ⟨b, -, hb⟩
  obtain ⟨V, hVo, hVi, haV, hbV⟩ := h2 a b
  obtain ⟨z, -, hzu, hzv⟩ := hVi.2 u v hu hv ⟨a, haV, ha⟩ ⟨b, hbV, hb⟩
  exact ⟨z, Set.mem_univ z, hzu, hzv⟩

end Top

/-- In a locally noetherian scheme connected components are open (copy of gt-rigidity's lemma). -/
theorem isOpen_cc_of_isLocallyNoetherian (T : Scheme.{0}) [IsLocallyNoetherian T] (t : T) :
    IsOpen (connectedComponent t) := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  have : IsNoetherianRing Γ(T, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : NoetherianSpace V := noetherianSpace_of_isAffineOpen V hV
  refine ⟨Subtype.val '' connectedComponent (⟨y, hyV⟩ : V), ?_, ?_, ⟨⟨y, hyV⟩,
    mem_connectedComponent, rfl⟩⟩
  · rw [connectedComponent_eq hy]
    exact (isConnected_connectedComponent.image _
      continuous_subtype_val.continuousOn).isPreconnected.subset_connectedComponent
      ⟨⟨y, hyV⟩, mem_connectedComponent, rfl⟩
  · exact V.isOpen.isOpenMap_subtype_val _
      (isOpen_cc_of_noetherianSpace (X := V) ⟨y, hyV⟩)

/-- A nonempty locally noetherian scheme has a nonempty open irreducible subset. -/
theorem exists_open_irred (T : Scheme.{0}) [IsLocallyNoetherian T] (t : T) :
    ∃ V : Set T, IsOpen V ∧ IsIrreducible V := by
  obtain ⟨U, hU, htU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := t) trivial
  have : IsNoetherianRing Γ(T, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hN : NoetherianSpace U := noetherianSpace_of_isAffineOpen U hU
  obtain ⟨o, ho, hne, hoZ⟩ := @NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
    U _ hN (irreducibleComponent (⟨t, htU⟩ : U))
    (irreducibleComponent_mem_irreducibleComponents (⟨t, htU⟩ : U))
  have hoi : IsIrreducible o :=
    ⟨hne, (isIrreducible_irreducibleComponent (x := (⟨t, htU⟩ : U))).2.open_subset ho hoZ⟩
  exact ⟨Subtype.val '' o, U.isOpen.isOpenMap_subtype_val _ ho,
    hoi.image _ continuous_subtype_val.continuousOn⟩

/-! ## Part B: group schemes over an algebraically closed field -/

section AlgClosed

variable {L : Type} [Field L] [IsAlgClosed L] (H : Over (Spec (CommRingCat.of L))) [GrpObj H]
  [LocallyOfFiniteType H.hom]

/-- The rational point at a closed point. -/
def ptOf (x : H.left) (hx : IsClosed {x}) : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ H :=
  Over.homMk (pointOfClosedPoint H.hom x hx) (by simp [pointOfClosedPoint_comp])

theorem ptOf_apply (x : H.left) (hx : IsClosed {x}) (p : (𝟙_ (Over (Spec (CommRingCat.of L)))).left) :
    (ptOf H x hx).left p = x :=
  pointOfClosedPoint_apply H.hom x hx p

/-- **Translations act transitively on closed points.** -/
theorem exists_translate (x y : H.left) (hx : IsClosed {x}) (hy : IsClosed {y}) :
    ∃ T : H ⟶ H, IsIso T.left ∧ T.left x = y := by
  let sx := ptOf H x hx
  let sy := ptOf H y hy
  let g := sy * sx⁻¹
  refine ⟨GrpObj.mulLeft H g, GrpObj.isIso_mulLeft_left H g, ?_⟩
  have hT : sx ≫ GrpObj.mulLeft H g = sy := by
    rw [GrpObj.mulLeft_eq_mul, MonObj.comp_mul, ← Category.assoc,
      toUnit_unique (sx ≫ toUnit H) (𝟙 _), Category.id_comp, Category.comp_id]
    simp only [g, inv_mul_cancel_right]
  let p : (𝟙_ (Over (Spec (CommRingCat.of L)))).left := IsLocalRing.closedPoint L
  have h1 : (GrpObj.mulLeft H g).left (sx.left p) = sy.left p := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hT]
  rwa [ptOf_apply, ptOf_apply] at h1

/-- **Every point of a group scheme locally of finite type over an algebraically closed field has an open
irreducible neighbourhood.** -/
theorem nbhd_of_algClosed (x : H.left) : ∃ V : Set H.left, IsOpen V ∧ IsIrreducible V ∧ x ∈ V := by
  haveI : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom
  haveI : JacobsonSpace H.left := LocallyOfFiniteType.jacobsonSpace H.hom
  let S : Set H.left := {x | ∃ V : Set H.left, IsOpen V ∧ IsIrreducible V ∧ x ∈ V}
  have hSo : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨V, hVo, hVi, hyV⟩
    exact ⟨V, fun z hz => ⟨V, hVo, hVi, hz⟩, hVo, hyV⟩
  -- `S` is nonempty
  let p : (𝟙_ (Over (Spec (CommRingCat.of L)))).left := IsLocalRing.closedPoint L
  obtain ⟨V₀, hV₀o, hV₀i⟩ := exists_open_irred H.left ((η[H] : 𝟙_ _ ⟶ H).left p)
  have hSne : S.Nonempty := by
    obtain ⟨z, hz⟩ := hV₀i.nonempty
    exact ⟨z, V₀, hV₀o, hV₀i, hz⟩
  obtain ⟨x₀, hx₀S, hx₀c⟩ := nonempty_inter_closedPoints hSne hSo.isLocallyClosed
  -- every closed point is in `S`
  have hcl : ∀ y : H.left, IsClosed {y} → y ∈ S := by
    intro y hy
    obtain ⟨T, hTi, hTy⟩ := exists_translate H x₀ y hx₀c hy
    obtain ⟨V, hVo, hVi, hxV⟩ := hx₀S
    haveI := hTi
    refine ⟨T.left '' V, T.left.isOpenMap _ hVo, hVi.image _ T.left.continuous.continuousOn,
      ⟨x₀, hxV, hTy⟩⟩
  by_contra hx
  obtain ⟨y, hyS, hyc⟩ := nonempty_inter_closedPoints (Z := Sᶜ) ⟨x, hx⟩
    hSo.isClosed_compl.isLocallyClosed
  exact hyS (hcl y hyc)

end AlgClosed

/-! ## Part C: geometric irreducibility of a geometrically connected open of a group scheme -/

section GeomIrr

variable {K : Type} [Field K] (G : Over (Spec (CommRingCat.of K))) [GrpObj G]
  [LocallyOfFiniteType G.hom]

/-- Over an algebraically closed field `L`, the base change of a geometrically connected open `V` of `G` is
irreducible. -/
theorem irreducible_of_algClosed (V : G.left.Opens) [GeometricallyConnected (V.ι ≫ G.hom)]
    {L : Type} [Field L] [IsAlgClosed L] (a : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    {P : Scheme.{0}} (fst : P ⟶ V) (snd : P ⟶ Spec (CommRingCat.of L))
    (sq : IsPullback fst snd (V.ι ≫ G.hom) a) : IrreducibleSpace P := by
  have : ConnectedSpace P := GeometricallyConnected.geometrically_connectedSpace a fst snd sq
  let H : Over (Spec (CommRingCat.of L)) := (Over.pullback a).obj G
  letI : GrpObj H := Functor.grpObjObj
  haveI : LocallyOfFiniteType H.hom :=
    show LocallyOfFiniteType (pullback.snd G.hom a) from inferInstance
  let j : P ⟶ pullback G.hom a := pullback.lift (fst ≫ V.ι) snd
    (by rw [Category.assoc]; exact sq.w)
  have hsq : IsPullback fst j V.ι (pullback.fst G.hom a) := by
    refine IsPullback.of_bot ?_ (by simp [j]) (IsPullback.of_hasPullback G.hom a)
    simpa [j] using sq
  haveI : IsOpenImmersion j := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq
    inferInstance
  apply irreducibleSpace_of_nbhd
  intro z
  obtain ⟨W, hWo, hWi, hzW⟩ := nbhd_of_algClosed H (j z)
  exact ⟨j ⁻¹' W, hWo.preimage j.continuous, ⟨⟨z, hzW⟩, hWi.2.preimage j.isOpenEmbedding⟩, hzW⟩

/-- **A geometrically connected open `V` of a group scheme locally of finite type over `K` is geometrically
irreducible.** -/
theorem geometricallyIrreducible_of_geometricallyConnected (V : G.left.Opens)
    [GeometricallyConnected (V.ι ≫ G.hom)] : GeometricallyIrreducible (V.ι ≫ G.hom) := by
  refine ⟨fun {Ω} _ point P fst snd sq => ?_⟩
  let L := AlgebraicClosure Ω
  let ψ : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of Ω) :=
    Spec.map (CommRingCat.ofHom (algebraMap Ω L))
  haveI : Surjective ψ := ⟨fun y => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  have sq2 : IsPullback (pullback.fst snd ψ ≫ fst) (pullback.snd snd ψ) (V.ι ≫ G.hom)
      (ψ ≫ point) := (IsPullback.of_hasPullback snd ψ).paste_horiz sq
  have : IrreducibleSpace (pullback snd ψ : Scheme.{0}) :=
    irreducible_of_algClosed G V (ψ ≫ point) _ _ sq2
  exact Function.Surjective.irreducibleSpace (pullback.fst snd ψ).continuous
    (pullback.fst snd ψ).surjective

end GeomIrr

/-! ## Part D: the identity component -/

section Main

variable {K : Type} [Field K] (G : Over (Spec (CommRingCat.of K))) [GrpObj G]

theorem e_comp : (η[G] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G).left ≫ G.hom = 𝟙 _ :=
  Over.w (η[G] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G)

theorem lift_one_one_mul :
    (lift (η[G] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G) η[G] ≫ μ[G] :
      𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G) = η[G] := by
  have h1 : (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G) = η[G] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rw [← h1, ← Hom.mul_def, _root_.mul_one]

theorem eta_inv :
    ((η[G] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G) ≫ (𝟙 G)⁻¹ :
      𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G) = η[G] := by
  have h1 : (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G) = η[G] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rw [GrpObj.comp_inv, Category.comp_id, ← h1, inv_one]

end Main

/-- **SGA 3 VI_A 2.4 / Stacks 0B7R, proved.** For a group scheme `G` locally of finite type over a field `K`,
its identity component is open, closed under the group law and the inverse, and geometrically irreducible. -/
theorem identityComponentLFT_proof : PicDict.IdentityComponentLFT := by
  intro K _ G _ hG
  haveI : LocallyOfFiniteType G.hom := hG
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  let s₀ : (𝟙_ (Over (Spec (CommRingCat.of K)))).left := IsLocalRing.closedPoint K
  let η' := (η[G] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G).left
  let e := η' s₀
  let V : G.left.Opens := ⟨connectedComponent e, isOpen_cc_of_isLocallyNoetherian G.left e⟩
  have hVC : (V : Set G.left) = T09Pic.identityComponent G := by
    ext x
    constructor
    · intro hx; exact ⟨s₀, hx⟩
    · rintro ⟨s, hs⟩
      rwa [Subsingleton.elim s s₀] at hs
  have hηV : ∀ s, η' s ∈ V := fun s => by
    rw [Subsingleton.elim s s₀]; exact mem_connectedComponent
  -- `V` is geometrically connected (Stacks 04KV)
  haveI : ConnectedSpace V := Subtype.connectedSpace isConnected_connectedComponent
  let sV : Spec (CommRingCat.of K) ⟶ V := IsOpenImmersion.lift V.ι η' (by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨s, rfl⟩; exact hηV s)
  have hsV : sV ≫ V.ι ≫ G.hom = 𝟙 _ := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact e_comp G
  haveI hgc : GeometricallyConnected (V.ι ≫ G.hom) :=
    geometricallyConnected_of_connectedSpace_of_section (V.ι ≫ G.hom) sV hsV
  refine ⟨V, hVC, ?_, ?_, geometricallyIrreducible_of_geometricallyConnected G V⟩
  · -- multiplication
    intro z h1 h2
    let q := V.ι ≫ G.hom
    have : ConnectedSpace ↥(pullback q q) := inferInstance
    let j : pullback q q ⟶ pullback G.hom G.hom :=
      pullback.map q q G.hom G.hom V.ι V.ι (𝟙 _) (by simp [q]) (by simp [q])
    have hrange : Set.range j = pullback.fst G.hom G.hom ⁻¹' Set.range V.ι ∩
        pullback.snd G.hom G.hom ⁻¹' Set.range V.ι := Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _
    let C := (μ[G] : G ⊗ G ⟶ G).left '' Set.range j
    have hCc : _root_.IsPreconnected C :=
      (isPreconnected_range j.continuous).image _ (μ[G] : G ⊗ G ⟶ G).left.continuous.continuousOn
    have heC : e ∈ C := by
      refine ⟨(lift (η[G] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G) η[G]).left s₀, ?_, ?_⟩
      · rw [hrange, Scheme.Opens.range_ι]
        constructor
        · show (lift (η[G] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G) η[G] ≫ fst G G).left s₀ ∈ V
          rw [lift_fst]; exact hηV s₀
        · show (lift (η[G] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G) η[G] ≫ snd G G).left s₀ ∈ V
          rw [lift_snd]; exact hηV s₀
      · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_one_one_mul]
    have hzC : (μ[G] : G ⊗ G ⟶ G).left z ∈ C := by
      refine ⟨z, ?_, rfl⟩
      rw [hrange, Scheme.Opens.range_ι]
      exact ⟨h1, h2⟩
    exact hCc.subset_connectedComponent heC hzC
  · -- inverse
    intro g hg
    let iv := ((𝟙 G)⁻¹ : G ⟶ G).left
    have hc : _root_.IsPreconnected (iv '' connectedComponent e) :=
      isConnected_connectedComponent.isPreconnected.image _ iv.continuous.continuousOn
    have he : e ∈ iv '' connectedComponent e := by
      refine ⟨e, mem_connectedComponent, ?_⟩
      show ((𝟙 G)⁻¹ : G ⟶ G).left ((η[G] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G).left s₀) = e
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, eta_inv]
    exact hc.subset_connectedComponent he ⟨g, hg, rfl⟩

end IdCompLFT

/-- The statement, by its exact type. -/
example : PicDict.IdentityComponentLFT := IdCompLFT.identityComponentLFT_proof

#print axioms IdCompLFT.identityComponentLFT_proof
