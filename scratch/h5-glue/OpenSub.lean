import ZInQKernel.HDecomp.Faltings.Leaves

/-! # h5-glue: open subgroup models are isomorphic on generic fibres

`genericIso_of_openImmersion`: if `f : 𝒰 → 𝒢` is a morphism of group models of `A_L` whose
underlying morphism of schemes is an open immersion, then its generic fibre
`f_L : 𝒰_L → 𝒢_L` is an isomorphism. Proof: `f_L` is an open immersion (base change); through the
identifications `gen` it becomes an open immersion `A_L → A_L` over `L`, which is universally
closed (`A_L` is proper, so separated), has nonempty open and closed image in the irreducible
`A_L` (geometrically irreducible over the one-point `Spec L`), hence is surjective, hence an
isomorphism. No group structure is used. -/

set_option linter.style.haveILetI false

namespace ZInQ.H5Glue

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- `Spec L → Spec 𝓞_L`. -/
noncomputable abbrev jL (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

/-- The base change of an open immersion along any `j` is an open immersion (for `Over.pullback`). -/
theorem isOpenImmersion_pullback_map {S S' : Scheme.{0}} (j : S' ⟶ S) {U G : Over S} (f : U ⟶ G)
    [IsOpenImmersion f.left] : IsOpenImmersion ((Over.pullback j).map f).left := by
  have t : IsPullback (pullback.fst G.hom j) (pullback.snd G.hom j) G.hom j :=
    IsPullback.of_hasPullback _ _
  have p : pullback.fst U.hom j ≫ f.left = ((Over.pullback j).map f).left ≫ pullback.fst G.hom j := by
    simp
  have s : IsPullback (pullback.fst U.hom j) (((Over.pullback j).map f).left ≫ pullback.snd G.hom j)
      (f.left ≫ G.hom) j := by
    have e1 : ((Over.pullback j).map f).left ≫ pullback.snd G.hom j = pullback.snd U.hom j := by
      simp
    have e2 : f.left ≫ G.hom = U.hom := Over.w f
    rw [e1, e2]
    exact IsPullback.of_hasPullback _ _
  have sq := IsPullback.of_bot s p t
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq ‹_›

/-- An open immersion `h : X → X` over `Spec L` of an abelian variety is an isomorphism. -/
theorem isIso_of_openImmersion_self (B : AbVar L) (h : B.X ⟶ B.X) [IsOpenImmersion h.left] :
    IsIso h := by
  have hw : h.left ≫ B.X.hom = B.X.hom := Over.w h
  haveI : UniversallyClosed (h.left ≫ B.X.hom) := by rw [hw]; infer_instance
  haveI : UniversallyClosed h.left := UniversallyClosed.of_comp_of_isSeparated h.left B.X.hom
  haveI : IrreducibleSpace B.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton B.X.hom
  have hrange : Set.range h.left = Set.univ := by
    have hc : IsClosed (Set.range h.left) := h.left.isClosedMap.isClosed_range
    have ho : IsOpen (Set.range h.left) := h.left.isOpenEmbedding.isOpen_range
    obtain ⟨x⟩ := (inferInstance : Nonempty B.X.left)
    exact IsClopen.eq_univ ⟨hc, ho⟩ ⟨h.left x, x, rfl⟩
  haveI : Surjective h.left := ⟨fun y => by
    have : y ∈ Set.range h.left := hrange ▸ Set.mem_univ y
    exact this⟩
  haveI : IsIso h.left := (isIso_iff_isOpenImmersion_and_surjective h.left).mpr ⟨‹_›, ‹_›⟩
  haveI : IsIso ((Over.forget _).map h) := inferInstanceAs (IsIso h.left)
  exact isIso_of_reflects_iso h (Over.forget _)

/-- **Open subgroup models agree generically** (proved). -/
theorem genericIso_of_openImmersion (𝒰 𝒢 : GroupModel A L) (f : 𝒰.G ⟶ 𝒢.G)
    [IsOpenImmersion f.left] : IsIso ((Over.pullback (jL L)).map f) := by
  let F := Over.pullback (jL L)
  let e₁ : F.obj 𝒰.G ≅ (A.baseChange L).X := 𝒰.gen
  let e₂ : F.obj 𝒢.G ≅ (A.baseChange L).X := 𝒢.gen
  haveI : IsOpenImmersion (F.map f).left := isOpenImmersion_pullback_map (jL L) f
  let h : (A.baseChange L).X ⟶ (A.baseChange L).X := e₁.inv ≫ F.map f ≫ e₂.hom
  haveI : IsIso e₁.inv.left := Functor.map_isIso (Over.forget _) e₁.inv
  haveI : IsIso e₂.hom.left := Functor.map_isIso (Over.forget _) e₂.hom
  haveI : IsOpenImmersion h.left := by
    show IsOpenImmersion (e₁.inv.left ≫ (F.map f).left ≫ e₂.hom.left)
    infer_instance
  haveI := isIso_of_openImmersion_self (A.baseChange L) h
  have : F.map f = e₁.hom ≫ h ≫ e₂.inv := by
    simp only [h, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [this]
  infer_instance

end ZInQ.H5Glue

#print axioms ZInQ.H5Glue.isOpenImmersion_pullback_map
#print axioms ZInQ.H5Glue.isIso_of_openImmersion_self
#print axioms ZInQ.H5Glue.genericIso_of_openImmersion
