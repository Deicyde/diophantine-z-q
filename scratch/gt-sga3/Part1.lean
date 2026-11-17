import ZInQKernel.OneProof.H.TailZ19
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Morphisms.SmoothSourceDescent
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.RingTheory.RegularLocalRing.Domain

open CategoryTheory AlgebraicGeometry Limits Topology TopologicalSpace

namespace SGA3IdComp

/-! ## Part 1: topology -/

section Top

variable {X : Type*} [TopologicalSpace X]

/-- The union of two open irreducible sets that meet is irreducible. -/
theorem isIrreducible_union_of_open {V W : Set X} (hV : IsIrreducible V) (hW : IsIrreducible W)
    (hVo : IsOpen V) (_hWo : IsOpen W) (hVW : (V ∩ W).Nonempty) : IsIrreducible (V ∪ W) := by
  refine ⟨hV.nonempty.mono Set.subset_union_left, ?_⟩
  intro u v hu hv hu' hv'
  -- `u` meets `V` iff it meets `W`
  have toV : ∀ {u : Set X}, IsOpen u → ((V ∪ W) ∩ u).Nonempty → (V ∩ u).Nonempty := by
    intro u hu h
    obtain ⟨z, hz | hz, hzu⟩ := h
    · exact ⟨z, hz, hzu⟩
    · obtain ⟨y, hyW, hyu, hyV⟩ := hW.2 u V hu hVo ⟨z, hz, hzu⟩ (hVW.mono fun a h => ⟨h.2, h.1⟩)
      exact ⟨y, hyV, hyu⟩
  obtain ⟨y, hyV, hyu, hyv⟩ := hV.2 u v hu hv (toV hu hu') (toV hv hv')
  exact ⟨y, Or.inl hyV, hyu, hyv⟩

/-- In a space where every point has an open compact irreducible neighbourhood, any two points of a
connected component lie in a common open compact irreducible set. -/
theorem exists_irred_of_mem_connectedComponent
    (h : ∀ x : X, ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ IsIrreducible V ∧ x ∈ V)
    {x y : X} (hy : y ∈ connectedComponent x) :
    ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ IsIrreducible V ∧ x ∈ V ∧ y ∈ V := by
  let R : Set X := {y | ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ IsIrreducible V ∧ x ∈ V ∧ y ∈ V}
  have hRo : IsOpen R := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨V, hVo, hVc, hVi, hxV, hyV⟩
    exact ⟨V, fun z hz => ⟨V, hVo, hVc, hVi, hxV, hz⟩, hVo, hyV⟩
  have hRc : IsClosed R := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨W, hWo, hWc, hWi, hyW⟩ := h y
    refine ⟨W, ?_, hWo, hyW⟩
    rintro z hzW ⟨V, hVo, hVc, hVi, hxV, hzV⟩
    exact hy ⟨V ∪ W, hVo.union hWo, hVc.union hWc,
      isIrreducible_union_of_open hVi hWi hVo hWo ⟨z, hzV, hzW⟩, Or.inl hxV, Or.inr hyW⟩
  have hxR : x ∈ R := by
    obtain ⟨V, hVo, hVc, hVi, hxV⟩ := h x
    exact ⟨V, hVo, hVc, hVi, hxV, hxV⟩
  exact (IsClopen.connectedComponent_subset ⟨hRc, hRo⟩ hxR) hy

/-- In a noetherian quasi-sober space, a point whose generizations form a preirreducible set has an
open irreducible neighbourhood. -/
theorem exists_isOpen_isIrreducible_of_generizations [NoetherianSpace X] [QuasiSober X] (x : X)
    (hx : IsPreirreducible {y : X | y ⤳ x}) :
    ∃ V : Set X, IsOpen V ∧ IsIrreducible V ∧ x ∈ V := by
  have hgen : IsIrreducible {y : X | y ⤳ x} := ⟨⟨x, specializes_rfl⟩, hx⟩
  obtain ⟨Z, hZ, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hgen
  -- every irreducible component containing `x` is `Z`
  have huniq : ∀ Z' ∈ irreducibleComponents X, x ∈ Z' → Z' = Z := by
    intro Z' hZ' hxZ'
    have hirr : IsIrreducible Z' := hZ'.1
    have hgp : IsGenericPoint hirr.genericPoint Z' := by
      have := hirr.isGenericPoint_genericPoint_closure
      rwa [(isClosed_of_mem_irreducibleComponents Z' hZ').closure_eq] at this
    have hη : hirr.genericPoint ⤳ x := by
      rw [specializes_iff_mem_closure, hgp.def]
      exact hxZ'
    have hZ'Z : Z' ⊆ Z := by
      rw [← hgp.def]
      exact (isClosed_of_mem_irreducibleComponents Z hZ).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr (hsub hη))
    exact ((hZ'.2 hZ.1 hZ'Z).antisymm hZ'Z).symm
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  let V : Set X := (⋃₀ (irreducibleComponents X \ {Z}))ᶜ
  have hVo : IsOpen V := by
    show IsOpen (⋃₀ (irreducibleComponents X \ {Z}))ᶜ
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hfin.sdiff.isClosed_biUnion fun W hW => isClosed_of_mem_irreducibleComponents W hW.1
  have hxV : x ∈ V := by
    rintro ⟨Z', ⟨hZ', hne⟩, hxZ'⟩
    exact hne (huniq Z' hZ' hxZ')
  have hVZ : V ⊆ Z := by
    intro y hy
    obtain ⟨Z', hZ', hyZ'⟩ := Set.mem_sUnion.mp (sUnion_irreducibleComponents (X := X) ▸ Set.mem_univ y)
    by_cases h : Z' = Z
    · exact h ▸ hyZ'
    · exact absurd ⟨Z', ⟨hZ', h⟩, hyZ'⟩ hy
  exact ⟨V, hVo, hZ.1.2.subset_irreducible ⟨x, hxV⟩ hVo le_rfl hVZ, hxV⟩

end Top

/-! ## Part 2: schemes whose stalks are domains -/

section Sch

/-- In a locally noetherian scheme whose stalks are domains, every point has an open, compact,
irreducible neighbourhood. -/
theorem exists_irred_nbhd (X : Scheme.{0}) [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (x : X) :
    ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ IsIrreducible V ∧ x ∈ V := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hN : NoetherianSpace U := noetherianSpace_of_isAffineOpen U hU
  -- the generizations of `x` form an irreducible set
  have hgenX : IsIrreducible {y : X | y ⤳ x} := by
    rw [← Scheme.range_fromSpecStalk]
    have := hX x
    have hi := (IrreducibleSpace.isIrreducible_univ (Spec (X.presheaf.stalk x))).image _
      (X.fromSpecStalk x).continuous.continuousOn
    rwa [Set.image_univ] at hi
  have hemb : IsOpenEmbedding (Subtype.val : U → X) := U.isOpen.isOpenEmbedding_subtypeVal
  have : QuasiSober U := hemb.quasiSober
  let x' : U := ⟨x, hxU⟩
  have hgenU : IsPreirreducible {y : U | y ⤳ x'} := by
    have h := hgenX.2.preimage hemb
    convert h using 1
    ext y
    exact (hemb.isInducing.specializes_iff).symm
  obtain ⟨V', hV'o, hV'i, hxV'⟩ := @exists_isOpen_isIrreducible_of_generizations U _ hN _ x' hgenU
  exact ⟨Subtype.val '' V', hemb.isOpenMap _ hV'o,
    (@NoetherianSpace.isCompact U _ hN V').image continuous_subtype_val,
    hV'i.image _ continuous_subtype_val.continuousOn, ⟨x', hxV', rfl⟩⟩

end Sch

end SGA3IdComp

/-! ## Part 3: smooth schemes over a field -/

namespace SGA3IdComp

open MonoidalCategory CartesianMonoidalCategory MonObj

/-- A scheme smooth over a field has open, compact, irreducible neighbourhoods. -/
theorem exists_irred_nbhd_of_smooth {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] (x : X) :
    ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ IsIrreducible V ∧ x ∈ V := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact exists_irred_nbhd X (fun y => by
    have := Smooth.isRegularLocalRing_stalk f y
    infer_instance) x

/-- In a scheme smooth over a field, two points of one connected component lie in a common open,
compact, irreducible set. -/
theorem exists_irred_of_smooth {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] {x y : X} (hy : y ∈ connectedComponent x) :
    ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ IsIrreducible V ∧ x ∈ V ∧ y ∈ V :=
  exists_irred_of_mem_connectedComponent (exists_irred_nbhd_of_smooth f) hy

/-- Three points of one connected component lie in a common open, compact, irreducible set. -/
theorem exists_irred3_of_smooth {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] {x y z : X} (hy : y ∈ connectedComponent x)
    (hz : z ∈ connectedComponent x) :
    ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ IsIrreducible V ∧ x ∈ V ∧ y ∈ V ∧ z ∈ V := by
  obtain ⟨V₁, h1o, h1c, h1i, hx1, hy1⟩ := exists_irred_of_smooth f hy
  obtain ⟨V₂, h2o, h2c, h2i, hx2, hz2⟩ := exists_irred_of_smooth f hz
  exact ⟨V₁ ∪ V₂, h1o.union h2o, h1c.union h2c,
    isIrreducible_union_of_open h1i h2i h1o h2o ⟨x, hx1, hx2⟩, Or.inl hx1, Or.inl hy1, Or.inr hz2⟩

/-- A morphism from a compact scheme to the spectrum of a field is quasi-compact. -/
theorem quasiCompact_to_field {k : Type} [Field k] {X : Scheme.{0}} [CompactSpace X]
    (f : X ⟶ Spec (CommRingCat.of k)) : QuasiCompact f := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro U _
  rcases Set.eq_empty_or_nonempty (U : Set (Spec (CommRingCat.of k))) with h | ⟨y, hy⟩
  · have : (f ⁻¹ᵁ U : Set X) = ∅ := by
      ext z; simp only [Scheme.Hom.coe_preimage, Set.mem_preimage, Set.mem_empty_iff_false,
        iff_false]; intro hz; rw [h] at hz; exact hz
    rw [this]; exact isCompact_empty
  · have : (f ⁻¹ᵁ U : Set X) = Set.univ := by
      ext z; simp only [Scheme.Hom.coe_preimage, Set.mem_preimage, Set.mem_univ, iff_true]
      rwa [Subsingleton.elim (f z) y]
    rw [this]; exact isCompact_univ

/-- **Geometric connectedness of an open irreducible piece of a smooth scheme with a rational point**
(from the bundle leaf `AVGlue.GeomConnOfRationalPoint`, Stacks 04KV). -/
theorem geomConn_open (hG : AVGlue.GeomConnOfRationalPoint) {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (V : X.Opens) (hVc : IsCompact (V : Set X))
    (hVi : IsIrreducible (V : Set X)) (s : Spec (CommRingCat.of k) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (hsV : Set.range s ⊆ V) : GeometricallyConnected (V.ι ≫ f) := by
  have : CompactSpace V := isCompact_iff_compactSpace.mp hVc
  have : ConnectedSpace V := Subtype.connectedSpace hVi.isConnected
  refine hG k V (V.ι ≫ f) (IsOpenImmersion.lift V.ι s (by rwa [Scheme.Opens.range_ι])) ?_
    inferInstance (quasiCompact_to_field _) ‹_›
  rw [← Category.assoc, IsOpenImmersion.lift_fac, hs]

end SGA3IdComp

/-! ## Part 4: the identity component through fibres -/

namespace SGA3IdComp

open MonoidalCategory CartesianMonoidalCategory MonObj CToPrinted

section Grp

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

theorem e_comp : (η[G] : 𝟙_ (Over S) ⟶ G).left ≫ G.hom = 𝟙 S := Over.w (η[G] : 𝟙_ (Over S) ⟶ G)

theorem hom_e (s : S) : G.hom ((η[G] : 𝟙_ (Over S) ⟶ G).left s) = s := by
  rw [← Scheme.Hom.comp_apply, e_comp]; rfl

/-- The unit section of the fibre `G_t`. -/
noncomputable def eF (t : S) : Spec (S.residueField t) ⟶ G.hom.fiber t :=
  pullback.lift (S.fromSpecResidueField t ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left) (𝟙 _)
    (by rw [Category.assoc, e_comp, Category.comp_id, Category.id_comp])

theorem eF_fiberι (t : S) : eF G t ≫ G.hom.fiberι t =
    S.fromSpecResidueField t ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := pullback.lift_fst _ _ _

theorem eF_fac (t : S) : eF G t ≫ G.hom.fiberToSpecResidueField t = 𝟙 _ := pullback.lift_snd _ _ _

theorem fiberι_eF (t : S) (p : Spec (S.residueField t)) :
    G.hom.fiberι t (eF G t p) = (η[G] : 𝟙_ (Over S) ⟶ G).left t := by
  rw [← Scheme.Hom.comp_apply, eF_fiberι, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

/-- A point of `G⁰` over `t` lies, in the fibre `G_t`, in the connected component of the unit. -/
theorem mem_cc_of_mem_idCompSet (x : G.left) (hx : x ∈ idCompSet G) (t : S) (ht : G.hom x = t)
    (x' : G.hom.fiber t) (hx' : G.hom.fiberι t x' = x) (p : Spec (S.residueField t)) :
    x' ∈ connectedComponent (eF G t p) := by
  subst ht
  let t := G.hom x
  let φ := G.hom.fiberHomeo t
  have het : (η[G] : 𝟙_ (Over S) ⟶ G).left t ∈ G.hom ⁻¹' {t} := hom_e G t
  have hx2 : x ∈ connectedComponentIn (G.hom ⁻¹' {t}) ((η[G] : 𝟙_ (Over S) ⟶ G).left t) := hx
  rw [connectedComponentIn_eq_image het] at hx2
  obtain ⟨y, hy, hyx⟩ := hx2
  have hφx : φ x' = y := Subtype.ext (by rw [Scheme.Hom.fiberHomeo_apply, hx', hyx])
  have hφe : φ (eF G t p) = ⟨_, het⟩ := Subtype.ext (by rw [Scheme.Hom.fiberHomeo_apply, fiberι_eF])
  have hC : _root_.IsConnected (φ ⁻¹' connectedComponent (⟨_, het⟩ : G.hom ⁻¹' {t})) :=
    φ.isConnected_preimage.mpr isConnected_connectedComponent
  refine hC.isPreconnected.subset_connectedComponent ?_ ?_
  · rw [Set.mem_preimage, hφe]; exact mem_connectedComponent
  · rw [Set.mem_preimage, hφx]; exact hy

/-- A preconnected set inside the fibre over `t` containing `e(t)` lies in `G⁰`. -/
theorem subset_idCompSet (C : Set G.left) (hC : _root_.IsPreconnected C) (t : S)
    (hsub : C ⊆ G.hom ⁻¹' {t}) (he : (η[G] : 𝟙_ (Over S) ⟶ G).left t ∈ C) : C ⊆ idCompSet G := by
  intro y hy
  have h1 := hC.subset_connectedComponentIn he hsub hy
  have h2 : G.hom y = t := hsub hy
  show y ∈ connectedComponentIn (G.hom ⁻¹' {G.hom y}) ((η[G] : 𝟙_ (Over S) ⟶ G).left (G.hom y))
  rw [h2]; exact h1

theorem lift_one_one_mul : (lift (η[G] : 𝟙_ (Over S) ⟶ G) η[G] ≫ μ[G] : 𝟙_ (Over S) ⟶ G) = η[G] := by
  have h1 : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rw [← h1, ← Hom.mul_def, _root_.mul_one]

/-- The point `(e(t), e(t))` of `G ×_S G`. -/
theorem fst_lift_one_one (t : S) :
    pullback.fst G.hom G.hom ((lift (η[G] : 𝟙_ (Over S) ⟶ G) η[G]).left t) =
      (η[G] : 𝟙_ (Over S) ⟶ G).left t := by
  rw [← Scheme.Hom.comp_apply]
  exact congrArg (fun h => h.left t) (lift_fst (η[G] : 𝟙_ (Over S) ⟶ G) η[G])

theorem snd_lift_one_one (t : S) :
    pullback.snd G.hom G.hom ((lift (η[G] : 𝟙_ (Over S) ⟶ G) η[G]).left t) =
      (η[G] : 𝟙_ (Over S) ⟶ G).left t := by
  rw [← Scheme.Hom.comp_apply]
  exact congrArg (fun h => h.left t) (lift_snd (η[G] : 𝟙_ (Over S) ⟶ G) η[G])

theorem mu_lift_one_one (t : S) :
    (μ[G] : G ⊗ G ⟶ G).left ((lift (η[G] : 𝟙_ (Over S) ⟶ G) η[G]).left t) =
      (η[G] : 𝟙_ (Over S) ⟶ G).left t := by
  rw [← Scheme.Hom.comp_apply]
  exact congrArg (fun h => h.left t) (lift_one_one_mul G)

theorem hom_mu (w : (G ⊗ G).left) :
    G.hom ((μ[G] : G ⊗ G ⟶ G).left w) = G.hom (pullback.fst G.hom G.hom w) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  exact congrArg (fun h => h w) (congrArg (fun k => k.base) (Over.w (μ[G] : G ⊗ G ⟶ G)))

omit [GrpObj G] in
theorem fiberι_mem (t : S) (y : G.hom.fiber t) : G.hom (G.hom.fiberι t y) = t := by
  have : G.hom.fiberι t y ∈ Set.range (G.hom.fiberι t) := ⟨y, rfl⟩
  rw [Scheme.Hom.range_fiberι] at this
  exact this

omit [GrpObj G] in
theorem exists_fiber_pt (t : S) (x : G.left) (hx : G.hom x = t) :
    ∃ x' : G.hom.fiber t, G.hom.fiberι t x' = x := by
  have : x ∈ Set.range (G.hom.fiberι t) := by rw [Scheme.Hom.range_fiberι]; exact hx
  exact this

/-- **Step 2: `G⁰` is closed under the group law** (for any base `S`; from the bundle leaf
`AVGlue.GeomConnOfRationalPoint`). -/
theorem mul_mem (hG : AVGlue.GeomConnOfRationalPoint) [Smooth G.hom] (z : (G ⊗ G).left)
    (h1 : (fst G G).left z ∈ idCompSet G) (h2 : (snd G G).left z ∈ idCompSet G) :
    (μ[G] : G ⊗ G ⟶ G).left z ∈ idCompSet G := by
  let a := (fst G G).left z
  let b := (snd G G).left z
  let t := G.hom a
  have hb : G.hom b = t := by
    show G.hom (pullback.snd G.hom G.hom z) = G.hom (pullback.fst G.hom G.hom z)
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  obtain ⟨a', ha'⟩ := exists_fiber_pt G t a rfl
  obtain ⟨b', hb'⟩ := exists_fiber_pt G t b hb
  let p : Spec (S.residueField t) := IsLocalRing.closedPoint _
  have ha'c := mem_cc_of_mem_idCompSet G a h1 t rfl a' ha' p
  have hb'c := mem_cc_of_mem_idCompSet G b h2 t hb b' hb' p
  let φF := G.hom.fiberToSpecResidueField t
  have hsm : Smooth φF := show Smooth (pullback.snd G.hom (S.fromSpecResidueField t)) from inferInstance
  have hlft : LocallyOfFiniteType φF :=
    show LocallyOfFiniteType (pullback.snd G.hom (S.fromSpecResidueField t)) from inferInstance
  obtain ⟨V, hVo, hVc, hVi, heV, haV, hbV⟩ := @exists_irred3_of_smooth _ _ _ φF hsm _ _ _ ha'c hb'c
  let Q : (G.hom.fiber t).Opens := ⟨V, hVo⟩
  let q := Q.ι ≫ φF
  have hsV : Set.range (eF G t) ⊆ (Q : Set (G.hom.fiber t)) := by
    rintro _ ⟨p', rfl⟩; rw [Subsingleton.elim p' p]; exact heV
  have hq : GeometricallyConnected q := @geomConn_open hG _ _ _ φF hlft Q hVc hVi (eF G t) (eF_fac G t) hsV
  have : ConnectedSpace Q := Subtype.connectedSpace hVi.isConnected
  have : ConnectedSpace ↥(pullback q q) := inferInstance
  let ι' := Q.ι ≫ G.hom.fiberι t
  have hι' : q ≫ S.fromSpecResidueField t = ι' ≫ G.hom := by
    simp only [q, ι', φF, Category.assoc, Scheme.Hom.fiber_fac]
  let j : pullback q q ⟶ pullback G.hom G.hom :=
    pullback.map q q G.hom G.hom ι' ι' (S.fromSpecResidueField t) hι' hι'
  have hrange : Set.range j = pullback.fst G.hom G.hom ⁻¹' Set.range ι' ∩
      pullback.snd G.hom G.hom ⁻¹' Set.range ι' := Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _
  have hQr : ∀ y' ∈ V, G.hom.fiberι t y' ∈ Set.range ι' := fun y' hy' => ⟨⟨y', hy'⟩, rfl⟩
  let C := (μ[G] : G ⊗ G ⟶ G).left '' Set.range j
  have hCc : _root_.IsPreconnected C :=
    (isPreconnected_range j.continuous).image _ (μ[G] : G ⊗ G ⟶ G).left.continuous.continuousOn
  have hCsub : C ⊆ G.hom ⁻¹' {t} := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hrange] at hw
    obtain ⟨y, hy⟩ := hw.1
    show G.hom ((μ[G] : G ⊗ G ⟶ G).left w) = t
    rw [hom_mu, ← hy]
    exact fiberι_mem G t _
  have heC : (η[G] : 𝟙_ (Over S) ⟶ G).left t ∈ C := by
    refine ⟨(lift (η[G] : 𝟙_ (Over S) ⟶ G) η[G]).left t, ?_, mu_lift_one_one G t⟩
    rw [hrange]
    have : (η[G] : 𝟙_ (Over S) ⟶ G).left t ∈ Set.range ι' := by
      rw [← fiberι_eF G t p]; exact hQr _ heV
    exact ⟨by rw [Set.mem_preimage, fst_lift_one_one]; exact this,
      by rw [Set.mem_preimage, snd_lift_one_one]; exact this⟩
  have hzC : (μ[G] : G ⊗ G ⟶ G).left z ∈ C := by
    refine ⟨z, ?_, rfl⟩
    rw [hrange]
    have h1 := hQr _ haV
    have h2 := hQr _ hbV
    rw [ha'] at h1
    rw [hb'] at h2
    exact ⟨h1, h2⟩
  exact subset_idCompSet G C hCc t hCsub heC hzC

/-- The division map `(a, b) ↦ a b⁻¹` of `G`. -/
noncomputable abbrev divG : G ⊗ G ⟶ G := fst G G * (snd G G)⁻¹

/-- `(a, a) ↦ e`: for a point `a : T → G`, `lift a a ≫ divG = e`. -/
theorem lift_self_divG {T : Scheme.{0}} (a : T ⟶ G.left) :
    pullback.lift a a rfl ≫ (divG G).left = a ≫ G.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  let A : Over.mk (a ≫ G.hom) ⟶ G := Over.homMk a rfl
  have h : lift A A ≫ divG G = toUnit _ ≫ η[G] := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, _root_.mul_inv_cancel, Hom.one_def]
  have h2 := congrArg (fun k => k.left) h
  simp only [Over.comp_left, Over.lift_left, Over.toUnit_left] at h2
  simpa [A, Category.assoc] using h2

/-- `(a b⁻¹) b = a`. -/
theorem lift_divG_snd_mul : lift (divG G) (snd G G) ≫ μ[G] = fst G G := by
  rw [← Hom.mul_def, divG, inv_mul_cancel_right]

/-- **Step 3** (the translation argument in the fibre over `κ(x)`): for an open `U ∋ e(s)` (all `s`) and
`x ∈ G⁰`, there is a point `w` of `G ×_S G` with first coordinate `x`, second coordinate in `U`, and
`w₁ w₂⁻¹ ∈ U`. -/
theorem exists_point (hG : AVGlue.GeomConnOfRationalPoint) [Smooth G.hom] (U : Set G.left)
    (hUo : IsOpen U) (heU : ∀ s, (η[G] : 𝟙_ (Over S) ⟶ G).left s ∈ U) (x : G.left)
    (hx : x ∈ idCompSet G) :
    ∃ w : (G ⊗ G).left, (fst G G).left w = x ∧ (snd G G).left w ∈ U ∧ (divG G).left w ∈ U := by
  let t := G.hom x
  obtain ⟨x', hx'⟩ := exists_fiber_pt G t x rfl
  let p : Spec (S.residueField t) := IsLocalRing.closedPoint _
  have hx'c := mem_cc_of_mem_idCompSet G x hx t rfl x' hx' p
  let φF := G.hom.fiberToSpecResidueField t
  have hsm : Smooth φF := show Smooth (pullback.snd G.hom (S.fromSpecResidueField t)) from inferInstance
  have hlft : LocallyOfFiniteType φF :=
    show LocallyOfFiniteType (pullback.snd G.hom (S.fromSpecResidueField t)) from inferInstance
  obtain ⟨V, hVo, hVc, hVi, heV, hxV⟩ := @exists_irred_of_smooth _ _ _ φF hsm _ _ hx'c
  let Q : (G.hom.fiber t).Opens := ⟨V, hVo⟩
  let q := Q.ι ≫ φF
  have hsV : Set.range (eF G t) ⊆ (Q : Set (G.hom.fiber t)) := by
    rintro _ ⟨p', rfl⟩; rw [Subsingleton.elim p' p]; exact heV
  have hq : GeometricallyConnected q :=
    @geomConn_open hG _ _ _ φF hlft Q hVc hVi (eF G t) (eF_fac G t) hsV
  let ι' := Q.ι ≫ G.hom.fiberι t
  have hι' : q ≫ S.fromSpecResidueField t = ι' ≫ G.hom := by
    simp only [q, ι', φF, Category.assoc, Scheme.Hom.fiber_fac]
  have hQr : ∀ y' ∈ V, G.hom.fiberι t y' ∈ Set.range ι' := fun y' hy' => ⟨⟨y', hy'⟩, rfl⟩
  -- the field `K = κ(x')` and the point `x̃ : Spec K → G`
  let xF := (G.hom.fiber t).fromSpecResidueField x'
  let xt := xF ≫ G.hom.fiberι t
  let c := xF ≫ φF
  have hc : c ≫ S.fromSpecResidueField t = 𝟙 _ ≫ xt ≫ G.hom := by
    simp only [c, xt, φF, Category.assoc, Scheme.Hom.fiber_fac, Category.id_comp]
  have hxt : ∀ r, xt r = x := by
    intro r
    have : xF r = x' := (G.hom.fiber t).fromSpecResidueField_apply x' r
    simp only [xt, Scheme.Hom.comp_apply, this, hx']
  let pK : Spec ((G.hom.fiber t).residueField x') := IsLocalRing.closedPoint _
  -- `H = G ×_S Spec K`, smooth over `Spec K`
  let gH := pullback.snd G.hom (xt ≫ G.hom)
  have hsmH : Smooth gH := inferInstance
  let eH : Spec ((G.hom.fiber t).residueField x') ⟶ pullback G.hom (xt ≫ G.hom) :=
    pullback.lift (xt ≫ G.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left) (𝟙 _)
      (by simp only [Category.assoc, e_comp, Category.comp_id, Category.id_comp])
  let δ : Spec ((G.hom.fiber t).residueField x') ⟶ pullback G.hom (xt ≫ G.hom) :=
    pullback.lift xt (𝟙 _) (by rw [Category.id_comp])
  have hfst_eH : pullback.fst G.hom (xt ≫ G.hom) (eH pK) = (η[G] : 𝟙_ (Over S) ⟶ G).left t := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      hxt]
  have hfst_δ : pullback.fst G.hom (xt ≫ G.hom) (δ pK) = x := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, hxt]
  -- `eH` and `δ` lie in one connected component of `H`
  have hconn : δ pK ∈ connectedComponent (eH pK) := by
    have : ConnectedSpace ↥(pullback q c) := inferInstance
    let jH : pullback q c ⟶ pullback G.hom (xt ≫ G.hom) :=
      pullback.map q c G.hom (xt ≫ G.hom) ι' (𝟙 _) (S.fromSpecResidueField t) hι' hc
    have hrange : Set.range jH = pullback.fst G.hom (xt ≫ G.hom) ⁻¹' Set.range ι' ∩
        pullback.snd G.hom (xt ≫ G.hom) ⁻¹' Set.range (𝟙 (Spec ((G.hom.fiber t).residueField x'))) :=
      Scheme.Pullback.range_map q c G.hom (xt ≫ G.hom) ι' (𝟙 _) (S.fromSpecResidueField t) hι' hc
    refine (isPreconnected_range jH.continuous).subset_connectedComponent ?_ ?_
    · rw [hrange]
      refine ⟨?_, ⟨_, rfl⟩⟩
      rw [Set.mem_preimage, hfst_eH, ← fiberι_eF G t p]
      exact hQr _ heV
    · rw [hrange]
      refine ⟨?_, ⟨_, rfl⟩⟩
      rw [Set.mem_preimage, hfst_δ, ← hx']
      exact hQr _ hxV
  obtain ⟨W, hWo, -, hWi, heW, hδW⟩ := @exists_irred_of_smooth _ _ _ gH hsmH _ _ hconn
  -- the map `H → G ×_S G`, `(g, ·) ↦ (x, g)`
  let φ : pullback G.hom (xt ≫ G.hom) ⟶ pullback G.hom G.hom :=
    pullback.lift (pullback.snd _ _ ≫ xt) (pullback.fst _ _)
      ((Category.assoc _ _ _).trans pullback.condition.symm)
  let A := pullback.fst G.hom (xt ≫ G.hom) ⁻¹' U
  let B := (φ ≫ (divG G).left) ⁻¹' U
  have hA : IsOpen A := hUo.preimage (pullback.fst G.hom (xt ≫ G.hom)).continuous
  have hB : IsOpen B := hUo.preimage (φ ≫ (divG G).left).continuous
  have heA : eH pK ∈ A := by
    show pullback.fst G.hom (xt ≫ G.hom) (eH pK) ∈ U
    rw [hfst_eH]; exact heU t
  have hδB : δ pK ∈ B := by
    show (φ ≫ (divG G).left) (δ pK) ∈ U
    have h1 : δ ≫ φ = pullback.lift xt xt rfl := by
      apply pullback.hom_ext
      · simp [φ, δ]
      · simp [φ, δ]
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, h1, lift_self_divG]
    simp only [Scheme.Hom.comp_apply]
    exact heU _
  obtain ⟨h, hhW, hhA, hhB⟩ := hWi.2 A B hA hB ⟨eH pK, heW, heA⟩ ⟨δ pK, hδW, hδB⟩
  refine ⟨φ h, ?_, ?_, hhB⟩
  swap
  · show pullback.snd G.hom G.hom (φ h) ∈ U
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
    exact hhA
  show pullback.fst G.hom G.hom (φ h) = x
  rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hxt]

end Grp

end SGA3IdComp

namespace SGA3IdComp

open MonoidalCategory CartesianMonoidalCategory MonObj CToPrinted

/-- **LEAF `SGA3_VIB_3_10_Nbhd`** (SGA 3 I, Exp. VI_B, Thm. 3.10; EGA IV₃ 15.6.5; numbers UNVERIFIED; a
consequence of the printed theorem, weaker): for a smooth group scheme `G → S` and `s ∈ S`, the union `G⁰`
of the identity components of the fibres contains an open neighbourhood of `e(s)`. -/
def SGA3_VIB_3_10_Nbhd : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (s : S),
    ∃ U : Set G.left, IsOpen U ∧ (η[G] : 𝟙_ (Over S) ⟶ G).left s ∈ U ∧ U ⊆ idCompSet G

/-- **SGA 3 VI_B 3.10 from its neighbourhood form** and the bundle leaf `AVGlue.GeomConnOfRationalPoint`
(Stacks 04KV). -/
theorem sga3_VIB_3_10_of_nbhd (hN : SGA3_VIB_3_10_Nbhd) (hG : AVGlue.GeomConnOfRationalPoint) :
    SGA3_VIB_3_10 := by
  intro S G _ _
  choose U hUo heU hUs using hN S G
  let U0 := ⋃ s, U s
  have hU0o : IsOpen U0 := isOpen_iUnion hUo
  have heU0 : ∀ s, (η[G] : 𝟙_ (Over S) ⟶ G).left s ∈ U0 := fun s => Set.mem_iUnion.mpr ⟨s, heU s⟩
  have hU0s : U0 ⊆ idCompSet G := Set.iUnion_subset hUs
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨w, hw1, hw2, hw3⟩ := exists_point G hG U0 hU0o heU0 x hx
  refine ⟨(fst G G).left '' ((snd G G).left ⁻¹' U0 ∩ (divG G).left ⁻¹' U0), ?_, ?_,
    ⟨w, ⟨hw2, hw3⟩, hw1⟩⟩
  · rintro _ ⟨w', ⟨h2, h3⟩, rfl⟩
    have hm := mul_mem G hG ((lift (divG G) (snd G G)).left w')
      (by rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]; exact hU0s h3)
      (by rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]; exact hU0s h2)
    rwa [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_divG_snd_mul] at hm
  · have hopen : IsOpenMap (pullback.fst G.hom G.hom) := (pullback.fst G.hom G.hom).isOpenMap
    exact hopen _ ((hU0o.preimage (snd G G).left.continuous).inter
      (hU0o.preimage (divG G).left.continuous))

end SGA3IdComp
#print axioms SGA3IdComp.sga3_VIB_3_10_of_nbhd
