import ZInQKernel.Contrib.OneProof.UnipotentForward

/-!
# `ReductGlue.RaynaudSemistableSH` from Raynaud's criterion with a reading-robust conclusion (task dict-models)

The research field `raynaudSemistableSH` (`ReductGlue.RaynaudSemistableSH`, TailZ14) concludes
`SemistableNeronModels A O`: semistability read on the *geometric* special fibre `𝒩 ×_O κ̄`. If SGA 7 IX defines
semistable reduction over the residue field `k(s)` itself (Déf. 2.2/3.1, as recalled), the print gives the `k(s)`
form, and the step to `κ̄` needs base change of a semi-abelian group to `κ̄` and Stacks 04KV (the 11-16
dictionary pass counted that against the row).

This file:

* states the `k(s)` form faithfully, with a general torus: `HasSemiAbelianIdCompTorus G` (an open connected subgroup
  `U ⊆ G`, a faithfully flat homomorphism `π : U → B` onto an abelian variety over `k`, whose kernel becomes split
  over `k̄`: `ker(U(R) → B(R)) ≅ (Rˣ)^r` naturally in `k̄`-algebras `R`, i.e. `(ker π)_{k̄} ≅ 𝔾_m^r`, the definition
  of a torus over a field); unipotent-b's `UnipotentForward.IsSemistableRes` (split torus over `k(s)`) implies it
  (`isSemistableResT_of_res`);
* states the new LEAF `RaynaudSemistableSHOr`: the field's hypotheses, with the conclusion the disjunction of the
  `k(s)` form and the field's geometric form, so either reading of the print gives it by `Or.inl`/`Or.inr`;
* PROVES the ascent `k(s)` form `⇒` geometric form (`isSemistable_of_resT`) from the bundle leaf
  `AVGlue.GeomConnOfRationalPoint` (Stacks 04KV), for every DVR and every residue field;
* proves the field, exactly: `raynaudSemistableSH_of_or : RaynaudSemistableSHOr → GeomConnOfRationalPoint →
  ReductGlue.RaynaudSemistableSH`.

The transport lemmas (`Φ`, `ιR`, …) are reduct-glue's (TailZ14, `section Transport`, for field isomorphisms),
generalized to a field extension `φ : k →+* k'`; connectedness of `U_{k'}` is the only new input (04KV).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit ReductGlue ZInQ.HeightSplit

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace DictModels.RaynaudOr

/-! ## §1. Transport along a field extension -/

section Transport

variable {k k' : Type} [Field k] [Field k'] (φ : k →+* k')

/-- `Spec φ : Spec k' → Spec k`. -/
noncomputable abbrev sφ : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom φ)

/-- The base change square of `Over.pullback`. -/
theorem pbmap_isPullback {S T : Scheme.{0}} (g : T ⟶ S) (X Y : Over S) (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom g) ((Over.pullback g).map f).left f.left
      (pullback.fst Y.hom g) := by
  refine IsPullback.of_bot ?_ (by simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback Y.hom g)
  simpa only [Over.pullback_map_left, pullback.lift_snd, f.w] using
    IsPullback.of_hasPullback X.hom g

theorem homEquiv_mul' (X : Over (Spec (CommRingCat.of k'))) (Y : Over (Spec (CommRingCat.of k)))
    [GrpObj Y] (p q : (Over.map (sφ φ)).obj X ⟶ Y) :
    letI : GrpObj ((Over.pullback (sφ φ)).obj Y) := Functor.grpObjObj
    (Over.mapPullbackAdj (sφ φ)).homEquiv X Y (p * q) =
      (Over.mapPullbackAdj (sφ φ)).homEquiv X Y p * (Over.mapPullbackAdj (sφ φ)).homEquiv X Y q := by
  letI : GrpObj ((Over.pullback (sφ φ)).obj Y) := Functor.grpObjObj
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- A `k'`-algebra as a `k`-algebra through `φ`. -/
@[reducible] noncomputable def algK (R : Type) [CommRing R] [Algebra k' R] : Algebra k R :=
  ((algebraMap k' R).comp φ).toAlgebra

/-- `Over.map (Spec φ) (Spec R / k') ≅ Spec R / k`. -/
noncomputable def ιR (R : Type) [CommRing R] [Algebra k' R] :
    letI := algK φ R
    (Over.map (sφ φ)).obj (algPt k' R) ≅ algPt k R :=
  letI := algK φ R
  Over.isoMk (Iso.refl _) (by
    simp only [Over.map_obj_hom, Iso.refl_hom, algPt, Over.mk_hom]
    erw [Category.id_comp]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])

/-- `(Spec R / k' ⟶ U_{k'}) ≃* (Spec R / k ⟶ U)`. -/
noncomputable def Φ (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (R : Type) [CommRing R]
    [Algebra k' R] :
    letI := algK φ R
    letI : GrpObj ((Over.pullback (sφ φ)).obj U) := Functor.grpObjObj
    (algPt k' R ⟶ (Over.pullback (sφ φ)).obj U) ≃* (algPt k R ⟶ U) :=
  letI := algK φ R
  letI : GrpObj ((Over.pullback (sφ φ)).obj U) := Functor.grpObjObj
  { toFun p := (ιR φ R).inv ≫ ((Over.mapPullbackAdj (sφ φ)).homEquiv _ _).symm p
    invFun x := (Over.mapPullbackAdj (sφ φ)).homEquiv _ _ ((ιR φ R).hom ≫ x)
    left_inv p := by
      simp only
      rw [Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]
    right_inv x := by
      simp only
      rw [Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]
    map_mul' p q := by
      obtain ⟨p', rfl⟩ := ((Over.mapPullbackAdj (sφ φ)).homEquiv _ U).surjective p
      obtain ⟨q', rfl⟩ := ((Over.mapPullbackAdj (sφ φ)).homEquiv _ U).surjective q
      rw [← homEquiv_mul', Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
        MonObj.comp_mul] }

theorem Φ_comp (U V : Over (Spec (CommRingCat.of k))) [GrpObj U] [GrpObj V] (R : Type) [CommRing R]
    [Algebra k' R] (u : algPt k' R ⟶ (Over.pullback (sφ φ)).obj U) (g : U ⟶ V) :
    letI := algK φ R
    letI : GrpObj ((Over.pullback (sφ φ)).obj U) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback (sφ φ)).obj V) := Functor.grpObjObj
    Φ φ V R (u ≫ (Over.pullback (sφ φ)).map g) = Φ φ U R u ≫ g := by
  show (ιR φ R).inv ≫ ((Over.mapPullbackAdj (sφ φ)).homEquiv _ _).symm
      (u ≫ (Over.pullback (sφ φ)).map g) =
    ((ιR φ R).inv ≫ ((Over.mapPullbackAdj (sφ φ)).homEquiv _ _).symm u) ≫ g
  rw [Adjunction.homEquiv_naturality_right_symm, Category.assoc]

theorem Φ_natural (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (R S : Type) [CommRing R]
    [Algebra k' R] [CommRing S] [Algebra k' S] (f : R →ₐ[k'] S)
    (u : algPt k' R ⟶ (Over.pullback (sφ φ)).obj U) :
    letI := algK φ R
    letI := algK φ S
    letI : GrpObj ((Over.pullback (sφ φ)).obj U) := Functor.grpObjObj
    Φ φ U S (algPtMap f ≫ u) =
      algPtMap (k := k) ({ (f : R →+* S) with commutes' := fun a => f.commutes (φ a) } : R →ₐ[k] S)
        ≫ Φ φ U R u := by
  show (ιR φ S).inv ≫ ((Over.mapPullbackAdj (sφ φ)).homEquiv _ _).symm (algPtMap f ≫ u) = _ ≫
    (ιR φ R).inv ≫ ((Over.mapPullbackAdj (sφ φ)).homEquiv _ _).symm u
  rw [Adjunction.homEquiv_naturality_left_symm, ← Category.assoc, ← Category.assoc]
  congr 1

end Transport

/-! ## §2. The `k(s)` form with a general torus -/

/-- `k → k̄`. -/
noncomputable abbrev φbar (k : Type) [Field k] : k →+* AlgebraicClosure k :=
  algebraMap k (AlgebraicClosure k)

/-- **Semi-abelian identity component over `k`, with a torus that need not be split over `k`** (SGA 7 IX Déf. 2.2,
read over `k`; SGA 3 IX 1.1 / Borel 8.2 for "torus": a group scheme `T` over a field with `T_{k̄} ≅ 𝔾_m^r`;
locators UNVERIFIED). There is an open connected subgroup scheme `U ⊆ G` (the identity component) and a faithfully
flat homomorphism `π : U → B` onto an abelian variety `B` over `k` whose kernel is a torus, in the functor of points
over `k̄`: for every `k̄`-algebra `R` (a `k`-algebra through `k → k̄`) a group isomorphism `(Rˣ)^r ≅ ker(U(R) → B(R))`,
natural in `k̄`-algebra maps (by Yoneda, `(ker π)_{k̄} ≅ 𝔾_m^r`). Weaker than `HasSemiAbelianIdentityComponent`
(split torus over `k`), which asks the same for every `k`-algebra. -/
def HasSemiAbelianIdCompTorus {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] : Prop :=
  ∃ (U : Over (Spec (CommRingCat.of k))) (_ : GrpObj U) (inc : U ⟶ G),
    IsOpenImmersion inc.left ∧ IsMonHom inc ∧ ConnectedSpace U.left ∧
    ∃ (B : PkgI3.AbVar k) (π : U ⟶ B.X), IsMonHom π ∧ Flat π.left ∧ Surjective π.left ∧
    ∃ (r : ℕ) (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
        letI := algK (φbar k) R
        (Fin r → Rˣ) →* (algPt k R ⟶ U)),
      (∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R], Function.Injective (e R)) ∧
      (∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
        letI := algK (φbar k) R
        ∀ u : algPt k R ⟶ U, u ≫ π = 1 ↔ u ∈ (e R).range) ∧
      (∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
        [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
        letI := algK (φbar k) R
        letI := algK (φbar k) S
        e S (fun i => Units.map (f : R →* S) (t i)) =
          algPtMap (k := k) ({ (f : R →+* S) with commutes' := fun a => f.commutes (φbar k a) } :
            R →ₐ[k] S) ≫ e R t)

/-- The split-torus form over `k` gives the general-torus form. -/
theorem hasSemiAbelianIdCompTorus_of_split {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] (h : HasSemiAbelianIdentityComponent G) : HasSemiAbelianIdCompTorus G := by
  obtain ⟨U, hU, inc, hoi, hmh, hcon, B, π, hπm, hfl, hsu, r, e, he_inj, he_ker, he_nat⟩ := h
  exact ⟨U, hU, inc, hoi, hmh, hcon, B, π, hπm, hfl, hsu, r,
    fun R _ _ => @e R _ (algK (φbar k) R), fun R _ _ => @he_inj R _ (algK (φbar k) R),
    fun R _ _ => @he_ker R _ (algK (φbar k) R),
    fun R S _ _ _ _ f t =>
      letI := algK (φbar k) R
      letI := algK (φbar k) S
      he_nat R S ({ (f : R →+* S) with commutes' := fun a => f.commutes (φbar k a) } : R →ₐ[k] S) t⟩

/-! ## §3. Ascent to `k̄` -/

/-- An open immersion into a scheme of finite type over a field gives a quasi-compact scheme over the field. -/
theorem quasiCompact_of_openImm {k : Type} [Field k] {U G : Over (Spec (CommRingCat.of k))} (inc : U ⟶ G)
    [IsOpenImmersion inc.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] : QuasiCompact U.hom := by
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  haveI : IsNoetherian G.left := {}
  have hU : U.hom = inc.left ≫ G.hom := (Over.w inc).symm
  rw [hU]
  infer_instance

/-- **The `k(s)` form gives the geometric form**: base change along `k → k̄` of a group scheme of finite type
whose identity component is an extension of an abelian variety by a torus has semi-abelian identity component (with
a split torus). Uses the bundle leaf `GeomConnOfRationalPoint` (Stacks 04KV) for the connectedness of `U_{k̄}`. -/
theorem hasSemiAbelian_pullback_bar (hGC : AVGlue.GeomConnOfRationalPoint) {k : Type} [Field k]
    (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (h : HasSemiAbelianIdCompTorus G) :
    letI : GrpObj ((Over.pullback (sφ (φbar k))).obj G) := Functor.grpObjObj
    HasSemiAbelianIdentityComponent ((Over.pullback (sφ (φbar k))).obj G) := by
  obtain ⟨U, hU, inc, hoi, hmh, hcon, B, π, hπm, hfl, hsu, r, e, he_inj, he_ker, he_nat⟩ := h
  let φ := φbar k
  let F := Over.pullback (sφ φ)
  letI : GrpObj (F.obj G) := Functor.grpObjObj
  letI : GrpObj (F.obj U) := Functor.grpObjObj
  letI : GrpObj (F.obj B.X) := Functor.grpObjObj
  haveI : IsOpenImmersion inc.left := hoi
  -- `U` is geometrically connected (Stacks 04KV)
  have hUlft : LocallyOfFiniteType U.hom := by
    have hU' : U.hom = inc.left ≫ G.hom := (Over.w inc).symm
    rw [hU']; infer_instance
  haveI : QuasiCompact U.hom := quasiCompact_of_openImm inc
  have hsec : (η[U] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ U).left ≫ U.hom = 𝟙 _ := by
    rw [Over.w]; rfl
  haveI hgc : GeometricallyConnected U.hom :=
    hGC k U.left U.hom (η[U] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ U).left hsec hUlft inferInstance hcon
  let B' : PkgI3.AbVar (AlgebraicClosure k) :=
    { X := F.obj B.X
      grp := Functor.grpObjObj
      proper := by change IsProper (pullback.snd B.X.hom (sφ φ)); infer_instance
      smooth := by change Smooth (pullback.snd B.X.hom (sφ φ)); infer_instance
      geomInt := by change GeometricallyIntegral (pullback.snd B.X.hom (sφ φ)); infer_instance }
  refine ⟨F.obj U, inferInstance, F.map inc, ?_, inferInstance, ?_, B', F.map π, inferInstance, ?_,
    ?_, r, fun R _ _ => (Φ φ U R).symm.toMonoidHom.comp (e R), ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) (pbmap_isPullback _ _ _ inc) hoi
  · exact GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd U.hom (sφ φ))
  · exact MorphismProperty.of_isPullback (P := @Flat) (pbmap_isPullback _ _ _ π) hfl
  · exact MorphismProperty.of_isPullback (P := @Surjective) (pbmap_isPullback _ _ _ π) hsu
  · intro R _ _
    exact (Φ φ U R).symm.injective.comp (he_inj R)
  · intro R _ _ u
    letI := algK φ R
    have h1 : u ≫ F.map π = 1 ↔ Φ φ U R u ≫ π = 1 := by
      rw [← Φ_comp]
      constructor
      · intro h; rw [h, map_one]
      · intro h; exact (Φ φ B.X R).injective (by rw [h, map_one])
    rw [h1, he_ker]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by simp [ht]⟩
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply] at ht
      rw [← ht, MulEquiv.apply_symm_apply]
  · intro R S _ _ _ _ f t
    letI := algK φ R
    letI := algK φ S
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    apply (Φ φ U S).injective
    rw [MulEquiv.apply_symm_apply, Φ_natural, MulEquiv.apply_symm_apply]
    exact he_nat R S f t

/-! ## §4. Néron models -/

section Neron

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {O : ValuationSubring K}

/-- **Semistable special fibre over `k(s)`, general torus** (SGA 7 IX Déf. 2.2/3.1 read over `k(s)`; locators
UNVERIFIED): the identity component of `𝒩 ×_O k(s)` is an extension of an abelian variety by a torus. -/
def IsSemistableResT (𝒩 : GroupModelO A O) : Prop :=
  HasSemiAbelianIdCompTorus (UnipotentForward.specialFibre 𝒩)

/-- unipotent-b's split-torus `k(s)` form gives the general-torus form. -/
theorem isSemistableResT_of_res (𝒩 : GroupModelO A O) (h : UnipotentForward.IsSemistableRes 𝒩) :
    IsSemistableResT 𝒩 :=
  hasSemiAbelianIdCompTorus_of_split _ h

theorem spec_bar_comp (O : ValuationSubring K) :
    sφ (φbar (IsLocalRing.ResidueField O)) ≫ UnipotentForward.sRes O =
      Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- **Ascent: the `k(s)` form implies the geometric form** (every DVR, every residue field), from Stacks 04KV. -/
theorem isSemistable_of_resT (hGC : AVGlue.GeomConnOfRationalPoint) (𝒩 : GroupModelO A O)
    (h : IsSemistableResT 𝒩) : 𝒩.IsSemistable := by
  unfold GroupModelO.IsSemistable
  haveI : LocallyOfFiniteType (UnipotentForward.specialFibre 𝒩).hom := by
    change LocallyOfFiniteType (pullback.snd 𝒩.G.hom (UnipotentForward.sRes O)); infer_instance
  haveI : QuasiCompact (UnipotentForward.specialFibre 𝒩).hom := by
    change QuasiCompact (pullback.snd 𝒩.G.hom (UnipotentForward.sRes O)); infer_instance
  have h2 := hasSemiAbelian_pullback_bar hGC (UnipotentForward.specialFibre 𝒩) h
  let E := pbCompIso _ _ _ (spec_bar_comp O) (Grp.mk 𝒩.G)
  exact @hasSemiAbelian_of_iso _ _ _ (geomSpecialFibre 𝒩) Functor.grpObjObj _
      (isoX E) (inferInstanceAs (IsMonHom E.hom.hom.hom)) h2

end Neron

/-! ## §5. The leaf and the field -/

/-- **LEAF `RaynaudSemistableSHOr`** (Raynaud's criterion, SGA 7 I, Exp. IX, Prop. 4.7, over a strictly henselian
DVR; number UNVERIFIED, no network). *Printed* (as recalled): `m ≥ 3` invertible on `S`, `A_K` with all points of
order `m` rational over `K`: then `A_K` has semistable reduction. *Lean form*: the field
`ReductGlue.RaynaudSemistableSH` word for word, with the conclusion weakened to the disjunction of the two readings
of "semistable reduction": over `k(s)` (`IsSemistableResT`, general torus) for every Néron model, or on the
geometric special fibre (`SemistableNeronModels`, the field's conclusion). Whichever reading the print has, the
leaf is the print by or-introduction. Other open readings, unchanged (UNVERIFIED): the print may require `m > 3`,
or state a Galois-form conclusion; the base may be a general trait (then this is a specialization). -/
def RaynaudSemistableSHOr : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O → ∀ (A : PkgI3.AbVar K) (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    (∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel → IsSemistableResT 𝒩) ∨ SemistableNeronModels A O

/-- The field implies the new leaf (so the leaf is never stronger than the field). -/
theorem or_of_field (h : ReductGlue.RaynaudSemistableSH) : RaynaudSemistableSHOr :=
  fun K _ O _ hS A m hm hu ht => Or.inr (h K O hS A m hm hu ht)

/-- **The field `raynaudSemistableSH`, exactly**, from the reading-robust leaf and the bundle leaf
`GeomConnOfRationalPoint` (Stacks 04KV). -/
theorem raynaudSemistableSH_of_or (h : RaynaudSemistableSHOr) (hGC : AVGlue.GeomConnOfRationalPoint) :
    ReductGlue.RaynaudSemistableSH := by
  intro K _ O _ hS A m hm hu ht
  rcases h K O hS A m hm hu ht with h1 | h2
  · exact fun 𝒩 h𝒩 => isSemistable_of_resT hGC 𝒩 (h1 𝒩 h𝒩)
  · exact h2

end DictModels.RaynaudOr

end
