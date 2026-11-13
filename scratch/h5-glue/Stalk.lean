import ZInQKernel.HDecomp.Faltings.Leaves

/-! # h5-glue: a generic isomorphism of group models is an isomorphism on the local ring at `ξ`

`stalkIso_of_genericIso`: if `f : 𝒢 → 𝒩` is a morphism of group models whose generic fibre is an
isomorphism, then `f` induces an isomorphism `𝒪_{𝒩,f(ξ)} → 𝒪_{𝒢,ξ}` at the identity `ξ` of the
generic fibre; `map_genericUnit`: a homomorphism sends `ξ_𝒢` to `ξ_𝒩`. Together:
`𝒩.genStalk ≅ 𝒢.genStalk` along `f`, the algebraic core of the glue `HeightAntitone`.

The lemmas `GenericFibreStalkIso`, `genericFibreStalkIso` (local rings of the generic fibre) and
`fst_genericFibreUnit` (the projection sends the identity of `𝒢_L` to `ξ`) are copied verbatim
from `scratch/hodge-lattice/HodgeLattice.lean` §9-§10 (task hodge-lattice), where they were proved. -/

namespace ZInQ.H5Glue
open NumberField CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj TensorProduct
open DefFaltings
open PkgI3 (AbVar)

/-- `Spec L → Spec 𝓞_L`. -/
noncomputable abbrev toGeneric (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

/-! ### Copied from hodge-lattice §9 -/

/-- **(S')** The projection `X_L = X ×_{𝓞_L} L → X` induces isomorphisms on local rings. -/
def GenericFibreStalkIso : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (X : Over (Spec (CommRingCat.of (𝓞 L))))
    (x : (genericFibre L X).left), IsIso ((pullback.fst X.hom (toGeneric L)).stalkMap x)

section
variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

theorem fst_genericFibre_unit :
    letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
    (η[genericFibre L 𝒢.G] : 𝟙_ _ ⟶ genericFibre L 𝒢.G).left ≫
      pullback.fst 𝒢.G.hom (toGeneric L) = toGeneric L ≫ 𝒢.unitSection := by
  let _ : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
  change (Functor.LaxMonoidal.ε (Over.pullback (toGeneric L)) ≫
    (Over.pullback (toGeneric L)).map η[𝒢.G]).left ≫ pullback.fst 𝒢.G.hom (toGeneric L) = _
  rw [Over.comp_left, Category.assoc]
  have h1 : ((Over.pullback (toGeneric L)).map η[𝒢.G]).left ≫
      pullback.fst 𝒢.G.hom (toGeneric L) =
      pullback.fst _ (toGeneric L) ≫ (η[𝒢.G] : 𝟙_ _ ⟶ 𝒢.G).left := by
    simp
  rw [h1, ← Category.assoc]
  have h2 : (Functor.LaxMonoidal.ε (Over.pullback (toGeneric L))).left ≫
      pullback.snd ((𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom) (toGeneric L) = 𝟙 _ :=
    Over.w (Functor.LaxMonoidal.ε (Over.pullback (toGeneric L)))
  have hc := pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom)
    (g := toGeneric L)
  have hc' : pullback.fst ((𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom) (toGeneric L) =
      pullback.snd _ _ ≫ toGeneric L := by
    rw [← hc]; exact (Category.comp_id _).symm
  rw [hc', ← Category.assoc, h2, Category.id_comp]
  rfl

omit [NumberField L] in
theorem toGeneric_pt [NumberField L] :
    (toGeneric L) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L) = genericPt L := by
  change PrimeSpectrum.comap (algebraMap (𝓞 L) L) ⟨⊥, Ideal.isPrime_bot⟩ = _
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.mem_bot, genericPt]
  exact map_eq_zero_iff _ (IsFractionRing.injective (𝓞 L) L)

/-- The identity `ξ_L` of the generic fibre. -/
noncomputable def genericFibreUnit : (genericFibre L 𝒢.G).left :=
  letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
  (η[genericFibre L 𝒢.G] : 𝟙_ _ ⟶ genericFibre L 𝒢.G).left
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L)

theorem fst_genericFibreUnit :
    pullback.fst 𝒢.G.hom (toGeneric L) (genericFibreUnit 𝒢) = 𝒢.genericUnit := by
  have h := congrArg (fun φ => φ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L))
    (fst_genericFibre_unit 𝒢)
  exact ((Scheme.Hom.comp_apply _ _ _).symm.trans h).trans
    ((Scheme.Hom.comp_apply _ _ _).trans (congrArg (fun y => 𝒢.unitSection y) (toGeneric_pt (L := L))))

end

/-! ### Copied from hodge-lattice §10 -/

/-- Bijectivity of ring maps respects isomorphisms. -/
theorem bijective_respectsIso :
    RingHom.RespectsIso (fun {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) =>
      Function.Bijective f) :=
  ⟨fun f e hf => e.bijective.comp hf, fun f e hf => hf.comp e.bijective⟩

local notation "Pb" => stalkwise (fun {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) =>
      Function.Bijective f)

/-- `Spec (A ⊗_R K) → Spec A` has bijective stalk maps when `K` is a localization of `R`. -/
theorem stalkwise_tensor_localization (R : Type) [CommRing R] (K : Type) [CommRing K]
    [Algebra R K] (M : Submonoid R) [IsLocalization M K] (A : Type) [CommRing A] [Algebra R A] :
    Pb (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] K)))) := by
  have := stalkwise_respectsIso bijective_respectsIso
  set M' := Algebra.algebraMapSubmonoid A M
  let e : A ⊗[R] K ≃ₐ[A] Localization M' := IsLocalization.algEquiv M' _ _
  have hfac : CommRingCat.ofHom (algebraMap A (A ⊗[R] K)) =
      CommRingCat.ofHom (algebraMap A (Localization M')) ≫
        CommRingCat.ofHom e.symm.toAlgHom.toRingHom := by
    ext a
    simp
  have : IsIso (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) :=
    ⟨⟨CommRingCat.ofHom e.toAlgHom.toRingHom,
      CommRingCat.hom_ext (RingHom.ext fun y => e.apply_symm_apply y),
      CommRingCat.hom_ext (RingHom.ext fun y => e.symm_apply_apply y)⟩⟩
  rw [hfac, Spec.map_comp]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  intro x
  have h := isIso_specMap_stalkMap_localization (CommRingCat.of A) M' x
  exact (ConcreteCategory.isIso_iff_bijective _).mp h

/-- On an affine chart: `Spec A ×_{𝓞_L} Spec L → Spec A` has bijective stalk maps. -/
theorem stalkwise_fst_toGeneric {L : Type} [Field L] [NumberField L] {A : CommRingCat}
    (g : Spec A ⟶ Spec (CommRingCat.of (𝓞 L))) : (Pb) (pullback.fst g (toGeneric L)) := by
  have : (Pb).RespectsIso := stalkwise_respectsIso bijective_respectsIso
  let φ := Spec.preimage g
  letI : Algebra (𝓞 L) A := φ.hom.toAlgebra
  have hg : g = Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) A)) := by
    rw [← Spec.map_preimage g]; rfl
  have he2 : (pullback.congrHom hg rfl).hom ≫ pullback.fst _ _ = pullback.fst g (toGeneric L) := by
    simp [pullback.congrHom]
  rw [← he2]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  rw [← pullbackSpecIso_hom_fst' (𝓞 L) A L]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  exact stalkwise_tensor_localization (𝓞 L) L (nonZeroDivisors (𝓞 L)) A

/-- **`GenericFibreStalkIso` holds**: base change along `Spec L → Spec 𝓞_L` does not change local
rings (Zariski-local on the target; on an affine chart it is `Spec (A ⊗_{𝓞_L} L) → Spec A`, a
localization). -/
theorem genericFibreStalkIso : GenericFibreStalkIso := by
  intro L _ _ X x
  have : (Pb).RespectsIso := stalkwise_respectsIso bijective_respectsIso
  have : IsZariskiLocalAtTarget (Pb) :=
    stalkwiseIsZariskiLocalAtTarget_of_respectsIso bijective_respectsIso
  suffices H : (Pb) (pullback.fst X.hom (toGeneric L)) from
    (ConcreteCategory.isIso_iff_bijective _).mpr (H x)
  refine IsZariskiLocalAtTarget.of_openCover X.left.affineOpenCover.openCover ?_
  intro i
  show (Pb) (pullback.snd (pullback.fst X.hom (toGeneric L)) (X.left.affineOpenCover.f i))
  have he : (pullbackSymmetry (pullback.fst X.hom (toGeneric L)) (X.left.affineOpenCover.f i) ≪≫
      pullbackRightPullbackFstIso X.hom (toGeneric L) (X.left.affineOpenCover.f i)).hom ≫
        pullback.fst (X.left.affineOpenCover.f i ≫ X.hom) (toGeneric L) =
      pullback.snd (pullback.fst X.hom (toGeneric L)) (X.left.affineOpenCover.f i) := by
    simp
  rw [← he]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  exact stalkwise_fst_toGeneric _


/-! ### New -/

section New
variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- A homomorphism of group models sends the identity `ξ` of the generic fibre to `ξ`. -/
theorem map_genericUnit (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    f.left 𝒢.genericUnit = 𝒩.genericUnit := by
  have h : 𝒢.unitSection ≫ f.left = 𝒩.unitSection := by
    have := congrArg CommaMorphism.left (IsMonHom.one_hom (f := f))
    exact (Over.comp_left (f := η[𝒢.G]) (g := f)).symm.trans this
  have h2 := congrArg (fun φ => φ (genericPt L)) h
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans h2

/-- **A generic isomorphism induces an isomorphism of local rings at `ξ`.** -/
theorem stalkIso_of_genericIso (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G)
    [hF : IsIso ((Over.pullback (toGeneric L)).map f)] :
    IsIso (f.left.stalkMap 𝒢.genericUnit) := by
  have hsq : pullback.fst 𝒢.G.hom (toGeneric L) ≫ f.left =
      ((Over.pullback (toGeneric L)).map f).left ≫ pullback.fst 𝒩.G.hom (toGeneric L) := by
    simp
  haveI : IsIso ((Over.pullback (toGeneric L)).map f).left := by
    have := Functor.map_isIso (Over.forget _) ((Over.pullback (toGeneric L)).map f)
    exact this
  haveI : IsIso (((Over.pullback (toGeneric L)).map f).left.stalkMap (genericFibreUnit 𝒢)) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
  haveI : IsIso ((pullback.fst 𝒢.G.hom (toGeneric L)).stalkMap (genericFibreUnit 𝒢)) :=
    genericFibreStalkIso L 𝒢.G _
  haveI : IsIso ((pullback.fst 𝒩.G.hom (toGeneric L)).stalkMap
      (((Over.pullback (toGeneric L)).map f).left (genericFibreUnit 𝒢))) :=
    genericFibreStalkIso L 𝒩.G _
  have h1 := Scheme.Hom.stalkMap_comp (pullback.fst 𝒢.G.hom (toGeneric L)) f.left
    (genericFibreUnit 𝒢)
  have h2 := Scheme.Hom.stalkMap_comp ((Over.pullback (toGeneric L)).map f).left
    (pullback.fst 𝒩.G.hom (toGeneric L)) (genericFibreUnit 𝒢)
  have h3 := Scheme.Hom.stalkMap_congr_hom _ _ hsq (genericFibreUnit 𝒢)
  have hc : IsIso ((pullback.fst 𝒢.G.hom (toGeneric L) ≫ f.left).stalkMap (genericFibreUnit 𝒢)) := by
    rw [h3, h2]
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) ?_
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ ‹_› ‹_›
  haveI : IsIso (f.left.stalkMap ((pullback.fst 𝒢.G.hom (toGeneric L)) (genericFibreUnit 𝒢)) ≫
      (pullback.fst 𝒢.G.hom (toGeneric L)).stalkMap (genericFibreUnit 𝒢)) := by
    rw [← h1]; exact hc
  haveI := IsIso.of_isIso_comp_right
    (f.left.stalkMap ((pullback.fst 𝒢.G.hom (toGeneric L)) (genericFibreUnit 𝒢)))
    ((pullback.fst 𝒢.G.hom (toGeneric L)).stalkMap (genericFibreUnit 𝒢))
  rw [← fst_genericFibreUnit 𝒢]
  infer_instance

end New

end ZInQ.H5Glue

#print axioms ZInQ.H5Glue.genericFibreStalkIso
#print axioms ZInQ.H5Glue.map_genericUnit
#print axioms ZInQ.H5Glue.stalkIso_of_genericIso
