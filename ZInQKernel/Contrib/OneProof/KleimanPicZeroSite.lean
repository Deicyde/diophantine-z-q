import ZInQKernel.Contrib.OneProof.KleimanPicZero954
import ZInQKernel.Contrib.OneProof.KleimanPicZeroProperQuot

/-!
# Kleiman 9.5.4 over Kleiman's own site (kleiman-site)

`KleimanSection2.KleimanPicZeroProper954` (`Contrib/OneProof/KleimanPicZero954.lean`) quantifies over schemes
representing `picardFunctorLN f`: the tree's `picardFunctor f` (the fppf sheafification of `T ↦ Pic(X ×_S T)` on
**all** `S`-schemes) restricted to locally Noetherian `S`-schemes. Kleiman, *The Picard scheme* (FGA Explained,
Ch. 9; arXiv math/0504020), sheafifies on the **site of locally Noetherian `S`-schemes** itself. This file proves the
two agree and restates the leaf over Kleiman's site:

* `fppfPrecoverageLN S`, `fppfTopologyLN S`: the fppf topology on locally Noetherian `S`-schemes (covering families:
  jointly surjective families of flat morphisms locally of finite presentation);
* the inclusion `(LocNoeth S).ι` into `Over S` is continuous (an fppf pullback of locally Noetherian schemes is
  locally Noetherian, so the inclusion preserves the pullbacks of covering families) and cocontinuous (every member
  of an fppf cover of a locally Noetherian scheme is locally Noetherian);
* `sheafifyRestrictIso F`, for every presheaf `F` on `Over S`: the sheafification on Kleiman's site of `F` restricted
  to locally Noetherian schemes is the restriction of the big-site sheafification of `F` (the restricted `toSheafify`
  is locally bijective, by `Presheaf.isLocally{Injective,Surjective}_whisker` for a cocontinuous functor, onto a
  sheaf, by continuity), with `toSheafify_sheafifyRestrictIso`;
* `kleimanPicardSheafSiteQ f`: Kleiman's `Pic_{(X/S)(fppf)}` literally (Def. 9.2.2): the sheafification on Kleiman's
  site of `T ↦ Pic(X_T)/Pic(T)` (`KleimanSection.kleimanPicardPresheaf`); `kleimanPicardSheafSite f`: the
  sheafification on Kleiman's site of `T ↦ Pic(X_T)` (Kleiman's remark after Def. 9.2.2: the same sheaf);
* `kleimanIsoQ f`, `kleimanIso f`: both are isomorphic to `picardFunctorLN f`, compatibly with `toSheafify`
  (for `kleimanIsoQ`, composing with `KleimanSection.picardFunctorIsoKleiman`, proved, no section needed);
* `KleimanPicZeroProper954SiteQ` (**LEAF**, printed form) and `KleimanPicZeroProper954Site` (**LEAF**, printed form):
  Kleiman 9.5.4 with the Picard scheme representing Kleiman's sheaf on Kleiman's site; hypotheses otherwise those of
  `KleimanPicZeroProper954`;
* `kleimanPicZeroProper954_of_siteQ`, `kleimanPicZeroProper954_of_site`: each implies
  `KleimanSection2.KleimanPicZeroProper954` (the identity points correspond under the isomorphisms).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory

namespace KleimanSite

open Scheme KleimanSection2 T09Pic PkgI3 PkgI3.AbVar PicDict PicFix

variable {S : Scheme.{u}}

/-! ## Kleiman's site -/

/-- **The fppf precoverage on locally Noetherian `S`-schemes** (Kleiman, *The Picard scheme*, §9.1–9.2: the fppf
topology on the category of locally Noetherian `S`-schemes): a family is covering when its image in `Scheme` is
a jointly surjective family of flat morphisms locally of finite presentation (Mathlib's `fppfPrecoverage`). -/
def fppfPrecoverageLN (S : Scheme.{u}) : Precoverage (LocNoeth S).FullSubcategory :=
  fppfPrecoverage.comap ((LocNoeth S).ι ⋙ Over.forget S)

/-- **Kleiman's site**: the fppf topology on locally Noetherian `S`-schemes. -/
abbrev fppfTopologyLN (S : Scheme.{u}) : GrothendieckTopology (LocNoeth S).FullSubcategory :=
  (fppfPrecoverageLN S).toGrothendieck

lemma prop_of_mem {X : (LocNoeth S).FullSubcategory} {R : Presieve X} (hR : R ∈ fppfPrecoverageLN S X)
    {Y : (LocNoeth S).FullSubcategory} {g : Y ⟶ X} (hg : R g) :
    Flat g.hom.left ∧ LocallyOfFinitePresentation g.hom.left :=
  hR.2 (Presieve.map_map hg)

lemma locNoeth_pullback_of_right {X Y Z : (LocNoeth S).FullSubcategory} (g : Z ⟶ X) (f : Y ⟶ X)
    [LocallyOfFiniteType f.hom.left] : LocNoeth S (pullback g.hom f.hom) := by
  have h : IsPullback (pullback.fst g.hom f.hom).left (pullback.snd g.hom f.hom).left
      g.hom.left f.hom.left := (IsPullback.of_hasPullback g.hom f.hom).map (Over.forget S)
  have : LocallyOfFiniteType (pullback.fst g.hom f.hom).left :=
    MorphismProperty.of_isPullback h.flip ‹_›
  have : IsLocallyNoetherian Z.obj.left := Z.property
  exact LocallyOfFiniteType.isLocallyNoetherian (pullback.fst g.hom f.hom).left

lemma locNoeth_pullback_of_left {X Y Z : (LocNoeth S).FullSubcategory} (g : Z ⟶ X) (f : Y ⟶ X)
    [LocallyOfFiniteType g.hom.left] : LocNoeth S (pullback g.hom f.hom) := by
  have h : IsPullback (pullback.fst g.hom f.hom).left (pullback.snd g.hom f.hom).left
      g.hom.left f.hom.left := (IsPullback.of_hasPullback g.hom f.hom).map (Over.forget S)
  have : LocallyOfFiniteType (pullback.snd g.hom f.hom).left :=
    MorphismProperty.of_isPullback h ‹_›
  have : IsLocallyNoetherian Y.obj.left := Y.property
  exact LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g.hom f.hom).left

/-- The pullback in `Over S`, as a locally Noetherian `S`-scheme. -/
def pbLN {X Y Z : (LocNoeth S).FullSubcategory} (g : Z ⟶ X) (f : Y ⟶ X)
    (h : LocNoeth S (pullback g.hom f.hom)) : (LocNoeth S).FullSubcategory :=
  ⟨pullback g.hom f.hom, h⟩

lemma isPullback_pbLN {X Y Z : (LocNoeth S).FullSubcategory} (g : Z ⟶ X) (f : Y ⟶ X)
    (h : LocNoeth S (pullback g.hom f.hom)) :
    IsPullback (ObjectProperty.homMk (pullback.fst g.hom f.hom) : pbLN g f h ⟶ Z)
      (ObjectProperty.homMk (pullback.snd g.hom f.hom) : pbLN g f h ⟶ Y) g f :=
  IsPullback.of_map (LocNoeth S).ι (by ext1; exact pullback.condition)
    (IsPullback.of_hasPullback g.hom f.hom)

lemma preservesLimit_cospan {X Y Z : (LocNoeth S).FullSubcategory} (g : Z ⟶ X) (f : Y ⟶ X)
    (h : LocNoeth S (pullback g.hom f.hom)) : PreservesLimit (cospan g f) (LocNoeth S).ι :=
  (isPullback_pbLN g f h).preservesLimit_cospan_iff.mpr (IsPullback.of_hasPullback g.hom f.hom)

instance : (fppfPrecoverageLN S).HasPullbacks where
  hasPullbacks_of_mem {X Y R} f hR := by
    refine ⟨fun {Z g} hg ↦ ?_⟩
    have := (prop_of_mem hR hg).2
    exact (isPullback_pbLN g f (locNoeth_pullback_of_left g f)).hasPullback

instance : (fppfPrecoverageLN S).PullbacksPreservedBy (LocNoeth S).ι where
  preservesPairwisePullbacks_of_mem {X R} hR := by
    refine ⟨fun {Y Z f g} hf hg ↦ ?_⟩
    have := (prop_of_mem hR hf).2
    exact preservesLimit_cospan f g (locNoeth_pullback_of_left f g)

instance : (fppfPrecoverageLN S).IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} X Y f hf Z g P p₁ p₂ h := by
    have hf' := hf
    simp only [fppfPrecoverageLN, Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hf' ⊢
    refine Precoverage.mem_coverings_of_isPullback _ hf' (((LocNoeth S).ι ⋙ Over.forget S).map g)
      (fun i ↦ ((LocNoeth S).ι ⋙ Over.forget S).map (p₁ i))
      (fun i ↦ ((LocNoeth S).ι ⋙ Over.forget S).map (p₂ i)) fun i ↦ ?_
    have := (prop_of_mem hf (Presieve.ofArrows.mk i)).2
    have := preservesLimit_cospan g (f i) (locNoeth_pullback_of_right g (f i))
    exact ((h i).map (LocNoeth S).ι).map (Over.forget S)

/-- **Continuity**: restricting a sheaf on the big fppf site of `S` to locally Noetherian `S`-schemes gives a sheaf
on Kleiman's site. -/
instance isContinuous_ι : (LocNoeth S).ι.IsContinuous (fppfTopologyLN S) (fppfTopology.over S) := by
  rw [over_toGrothendieck_eq_toGrothendieck_comap_forget]
  exact Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy (F := (LocNoeth S).ι)
    (J := fppfPrecoverageLN S) (K := fppfPrecoverage.comap (Over.forget S))
    (h := le_of_eq (Precoverage.comap_comp _ _ _))

/-- Mathlib's fppf precoverage contains the isomorphisms. -/
lemma fppfPrecoverage_hasIsos : (fppfPrecoverage.{u}).HasIsos where
  mem_coverings_of_isIso f _ := by
    rw [fppfPrecoverage, singleton_mem_precoverage_iff]
    exact ⟨(inferInstance : Surjective f).surj, inferInstance, inferInstance⟩

attribute [local instance] fppfPrecoverage_hasIsos

/-- **Cocontinuity**: an fppf covering sieve of a locally Noetherian `S`-scheme contains an fppf covering family
whose members are locally Noetherian (locally of finite type over a locally Noetherian scheme). -/
instance isCocontinuous_ι : (LocNoeth S).ι.IsCocontinuous (fppfTopologyLN S) (fppfTopology.over S) where
  cover_lift {T R} hR := by
    rw [GrothendieckTopology.mem_over_iff] at hR
    obtain ⟨R0, hR0, hle⟩ :=
      (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition (J := fppfPrecoverage)).mp hR
    obtain ⟨ι, Y, f, rfl⟩ := R0.exists_eq_ofArrows
    have hR0' := hR0
    rw [fppfPrecoverage, ofArrows_mem_precoverage_iff] at hR0'
    have hLN : ∀ i, LocNoeth S (Over.mk (f i ≫ T.obj.hom)) := fun i ↦ by
      have : IsLocallyNoetherian ((LocNoeth S).ι.obj T).left := T.property
      have : LocallyOfFinitePresentation (f i) := (hR0'.2 i).2
      exact LocallyOfFiniteType.isLocallyNoetherian (f i)
    let V : ι → (LocNoeth S).FullSubcategory := fun i ↦ ⟨Over.mk (f i ≫ T.obj.hom), hLN i⟩
    let g : ∀ i, V i ⟶ T := fun i ↦ ObjectProperty.homMk (Over.homMk (f i))
    refine GrothendieckTopology.superset_covering _ ?_
      (Precoverage.generate_mem_toGrothendieck (R := Presieve.ofArrows V g) ?_)
    · rw [Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      change R (Over.homMk (f i) : Over.mk (f i ≫ T.obj.hom) ⟶ T.obj)
      rw [← Sieve.overEquiv_iff]
      exact hle _ (f i) (Presieve.ofArrows.mk i)
    · simp only [fppfPrecoverageLN, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
      exact hR0

/-! ## Sheafification on Kleiman's site versus restriction of the big-site sheafification -/

section General

variable (F : (Over S)ᵒᵖ ⥤ Type (u + 1))

/-- The restriction of `toSheafify` (big fppf site) to locally Noetherian `S`-schemes. -/
def restrictToSheafify : (LocNoeth S).ι.op ⋙ F ⟶ (LocNoeth S).ι.op ⋙ sheafify (fppfTopology.over S) F :=
  Functor.whiskerLeft (LocNoeth S).ι.op (toSheafify (fppfTopology.over S) F)

lemma isSheaf_restrict :
    Presheaf.IsSheaf (fppfTopologyLN S) ((LocNoeth S).ι.op ⋙ sheafify (fppfTopology.over S) F) :=
  (LocNoeth S).ι.op_comp_isSheaf _ (fppfTopology.over S)
    ((presheafToSheaf (fppfTopology.over S) (Type (u + 1))).obj F)

instance : Presheaf.IsLocallyInjective (fppfTopologyLN S) (restrictToSheafify F) :=
  Presheaf.isLocallyInjective_whisker _ (fppfTopology.over S) _ _

instance : Presheaf.IsLocallySurjective (fppfTopologyLN S) (restrictToSheafify F) :=
  Presheaf.isLocallySurjective_whisker _ (fppfTopology.over S) _ _

instance isIso_sheafify_restrictToSheafify :
    IsIso ((presheafToSheaf (fppfTopologyLN S) (Type (u + 1))).map (restrictToSheafify F)) :=
  ((fppfTopologyLN S).W_iff _).mp ((fppfTopologyLN S).W_of_isLocallyBijective _)

/-- **The comparison.** For every presheaf `F` on `S`-schemes, the sheafification on Kleiman's site of `F`
restricted to locally Noetherian `S`-schemes is the restriction of the fppf sheafification of `F` on all
`S`-schemes. -/
def sheafifyRestrictIso :
    sheafify (fppfTopologyLN S) ((LocNoeth S).ι.op ⋙ F) ≅
      (LocNoeth S).ι.op ⋙ sheafify (fppfTopology.over S) F :=
  (sheafToPresheaf _ _).mapIso (asIso ((presheafToSheaf (fppfTopologyLN S) (Type (u + 1))).map
    (restrictToSheafify F))) ≪≫ (isoSheafify (fppfTopologyLN S) (isSheaf_restrict F)).symm

lemma toSheafify_sheafifyRestrictIso :
    toSheafify (fppfTopologyLN S) ((LocNoeth S).ι.op ⋙ F) ≫ (sheafifyRestrictIso F).hom =
      restrictToSheafify F := by
  change toSheafify _ _ ≫ sheafifyMap _ (restrictToSheafify F) ≫
    (isoSheafify (fppfTopologyLN S) (isSheaf_restrict F)).inv = _
  rw [← toSheafify_naturality_assoc, ← isoSheafify_hom (fppfTopologyLN S) (isSheaf_restrict F),
    Iso.hom_inv_id, Category.comp_id]

end General

/-! ## Kleiman's Picard sheaves on Kleiman's site -/

/-- **Kleiman's `Pic_{(X/S)(fppf)}`, Def. 9.2.2 as printed**: the sheafification, on the site of locally Noetherian
`S`-schemes with the fppf topology, of the relative Picard functor `T ↦ Pic(X ×_S T) / Pic(T)`
(`KleimanSection.kleimanPicardPresheaf`). Numbering as reported from a reading of the arXiv text; UNVERIFIED on the
build host. -/
def kleimanPicardSheafSiteQ {X : Scheme.{u}} (f : X ⟶ S) : Sheaf (fppfTopologyLN S) (Type (u + 1)) :=
  (presheafToSheaf (fppfTopologyLN S) (Type (u + 1))).obj
    ((LocNoeth S).ι.op ⋙ KleimanSection.kleimanPicardPresheaf f)

/-- **Kleiman's `Pic_{(X/S)(fppf)}`, remark after Def. 9.2.2**: the sheafification, on the site of locally
Noetherian `S`-schemes with the fppf topology, of `T ↦ Pic(X ×_S T)`. -/
def kleimanPicardSheafSite {X : Scheme.{u}} (f : X ⟶ S) : Sheaf (fppfTopologyLN S) (Type (u + 1)) :=
  (presheafToSheaf (fppfTopologyLN S) (Type (u + 1))).obj ((LocNoeth S).ι.op ⋙ picardPresheaf f)

/-- Kleiman's sheaf of `T ↦ Pic(X_T)` on his site is the tree's `picardFunctorLN`. -/
def kleimanIso {X : Scheme.{u}} (f : X ⟶ S) : (kleimanPicardSheafSite f).obj ≅ picardFunctorLN f :=
  sheafifyRestrictIso (picardPresheaf f)

lemma toSheafify_kleimanIso {X : Scheme.{u}} (f : X ⟶ S) :
    toSheafify (fppfTopologyLN S) ((LocNoeth S).ι.op ⋙ picardPresheaf f) ≫ (kleimanIso f).hom =
      restrictToSheafify (picardPresheaf f) :=
  toSheafify_sheafifyRestrictIso (picardPresheaf f)

/-- Kleiman's sheaf of `T ↦ Pic(X_T)/Pic(T)` on his site is the tree's `picardFunctorLN` (the site comparison
composed with `KleimanSection.picardFunctorIsoKleiman`). -/
def kleimanIsoQ {X : Scheme.{u}} (f : X ⟶ S) : (kleimanPicardSheafSiteQ f).obj ≅ picardFunctorLN f :=
  sheafifyRestrictIso (KleimanSection.kleimanPicardPresheaf f) ≪≫
    Functor.isoWhiskerLeft (LocNoeth S).ι.op
      ((sheafToPresheaf _ _).mapIso (KleimanSection.picardFunctorIsoKleiman f).symm)

/-! ## Kleiman 9.5.4 over Kleiman's site -/

/-- **The identity point** of a scheme `P` representing Kleiman's sheaf `kleimanPicardSheafSite`: the `K`-point
classifying the class of `𝒪_X`. -/
def unitPtSite {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))} {P : Over (Spec (CommRingCat.of K))}
    {hP : LocNoeth _ P} (rep : (kleimanPicardSheafSite X.hom).obj.RepresentableBy ⟨P, hP⟩) :
    𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P :=
  (rep.homEquiv (X := unitLN K)).symm
    ((toSheafify (fppfTopologyLN _) ((LocNoeth _).ι.op ⋙ picardPresheaf X.hom)).app (op (unitLN K))
      (1 : (pullback X.hom (𝟙_ (Over (Spec (CommRingCat.of K)))).hom).Pic)) |>.hom

/-- **The identity component** `Pic⁰` of a scheme representing `kleimanPicardSheafSite`. -/
def identityComponentSite {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    {P : Over (Spec (CommRingCat.of K))} {hP : LocNoeth _ P}
    (rep : (kleimanPicardSheafSite X.hom).obj.RepresentableBy ⟨P, hP⟩) : Set P.left :=
  {x | ∃ s : (𝟙_ (Over (Spec (CommRingCat.of K)))).left, x ∈ connectedComponent ((unitPtSite rep).left s)}

/-- **The identity point** of a scheme `P` representing Kleiman's sheaf `kleimanPicardSheafSiteQ`: the `K`-point
classifying the class of `𝒪_X` (the unit of `Pic(X)/Pic(K)`). -/
def unitPtSiteQ {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))} {P : Over (Spec (CommRingCat.of K))}
    {hP : LocNoeth _ P} (rep : (kleimanPicardSheafSiteQ X.hom).obj.RepresentableBy ⟨P, hP⟩) :
    𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P :=
  (rep.homEquiv (X := unitLN K)).symm
    ((toSheafify (fppfTopologyLN _) ((LocNoeth _).ι.op ⋙ KleimanSection.kleimanPicardPresheaf X.hom)).app
      (op (unitLN K))
      (1 : (pullback X.hom (𝟙_ (Over (Spec (CommRingCat.of K)))).hom).Pic ⧸
        KleimanSection.picBase X.hom (𝟙_ (Over (Spec (CommRingCat.of K)))))) |>.hom

/-- **The identity component** `Pic⁰` of a scheme representing `kleimanPicardSheafSiteQ`. -/
def identityComponentSiteQ {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    {P : Over (Spec (CommRingCat.of K))} {hP : LocNoeth _ P}
    (rep : (kleimanPicardSheafSiteQ X.hom).obj.RepresentableBy ⟨P, hP⟩) : Set P.left :=
  {x | ∃ s : (𝟙_ (Over (Spec (CommRingCat.of K)))).left, x ∈ connectedComponent ((unitPtSiteQ rep).left s)}

/-- **LEAF (printed form).** Kleiman, *The Picard scheme* (FGA Explained, Ch. 9; arXiv math/0504020), Thm 9.5.4
(= Thm 5.4 of the arXiv numbering) with Def. 9.2.2 and Def. 9.4.1: for `X` projective and geometrically integral
over a field `K` (geometrically normal, needed there only for "`Pic⁰_{X/K}` is projective"), the identity component
`Pic⁰_{X/K}` of the Picard scheme is proper. Stated with: projective = a closed immersion `X → ℙ^N_K` over `K`;
geometrically integral and geometrically normal after every field extension; a `K`-point (an extra hypothesis);
`Pic_{(X/K)(fppf)}` = Kleiman's Def. 9.2.2 literally, the sheafification **on the site of locally Noetherian
`K`-schemes with the fppf topology** (`fppfTopologyLN`) of `T ↦ Pic(X_T)/Pic(T)`; the Picard scheme = any `P` locally
of finite type over `K` representing it on that site (unique up to unique isomorphism; Kleiman's `Pic_{X/K}` is one
by Thm 9.4.8); `Pic⁰` = any open `V` whose underlying set is the connected component of the point classifying
`𝒪_X`. Numbering and hypotheses as reported from a reading of the arXiv text; UNVERIFIED on the build host. -/
def KleimanPicZeroProper954SiteQ : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))),
    (∃ (N : Type) (_ : Finite N) (i : X.left ⟶ ℙ(N; Spec (CommRingCat.of K))),
      IsClosedImmersion i ∧ i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) = X.hom) →
    GeometricallyIntegral X.hom → geometrically IsNormalScheme X.hom →
    (∃ σ : Spec (CommRingCat.of K) ⟶ X.left, σ ≫ X.hom = 𝟙 _) →
    ∀ (P : Over (Spec (CommRingCat.of K))) (hP : LocallyOfFiniteType P.hom)
      (rep : (kleimanPicardSheafSiteQ X.hom).obj.RepresentableBy ⟨P, locNoeth_of_lft hP⟩) (V : P.left.Opens),
      (V : Set P.left) = identityComponentSiteQ rep → IsProper (V.ι ≫ P.hom)

/-- **LEAF (printed form).** As `KleimanPicZeroProper954SiteQ`, with `Pic_{(X/K)(fppf)}` the sheafification on
Kleiman's site of `T ↦ Pic(X_T)` (Kleiman's remark right after Def. 9.2.2: the same sheaf). -/
def KleimanPicZeroProper954Site : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))),
    (∃ (N : Type) (_ : Finite N) (i : X.left ⟶ ℙ(N; Spec (CommRingCat.of K))),
      IsClosedImmersion i ∧ i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) = X.hom) →
    GeometricallyIntegral X.hom → geometrically IsNormalScheme X.hom →
    (∃ σ : Spec (CommRingCat.of K) ⟶ X.left, σ ≫ X.hom = 𝟙 _) →
    ∀ (P : Over (Spec (CommRingCat.of K))) (hP : LocallyOfFiniteType P.hom)
      (rep : (kleimanPicardSheafSite X.hom).obj.RepresentableBy ⟨P, locNoeth_of_lft hP⟩) (V : P.left.Opens),
      (V : Set P.left) = identityComponentSite rep → IsProper (V.ι ≫ P.hom)

/-! ## The derivations -/

/-- A representation of the tree's restricted functor is a representation of Kleiman's sheaf of `Pic(X_T)`. -/
def repSite {X : Scheme.{u}} {f : X ⟶ S} {P : (LocNoeth S).FullSubcategory}
    (rep : (picardFunctorLN f).RepresentableBy P) : (kleimanPicardSheafSite f).obj.RepresentableBy P :=
  rep.ofIso (kleimanIso f).symm

/-- A representation of the tree's restricted functor is a representation of Kleiman's sheaf of
`Pic(X_T)/Pic(T)`. -/
def repSiteQ {X : Scheme.{u}} {f : X ⟶ S} {P : (LocNoeth S).FullSubcategory}
    (rep : (picardFunctorLN f).RepresentableBy P) : (kleimanPicardSheafSiteQ f).obj.RepresentableBy P :=
  rep.ofIso (kleimanIsoQ f).symm

lemma unitPtSite_repSite {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    {P : Over (Spec (CommRingCat.of K))} {hP : LocNoeth _ P}
    (rep : (picardFunctorLN X.hom).RepresentableBy ⟨P, hP⟩) : unitPtSite (repSite rep) = unitPt rep := by
  have key : (kleimanIso X.hom).hom.app (op (unitLN K))
      ((toSheafify (fppfTopologyLN _) ((LocNoeth _).ι.op ⋙ picardPresheaf X.hom)).app (op (unitLN K))
        (1 : (pullback X.hom (𝟙_ (Over (Spec (CommRingCat.of K)))).hom).Pic)) =
      (restrictToSheafify (picardPresheaf X.hom)).app (op (unitLN K))
        (1 : (pullback X.hom (𝟙_ (Over (Spec (CommRingCat.of K)))).hom).Pic) :=
    ConcreteCategory.congr_hom (congr_app (toSheafify_kleimanIso X.hom) (op (unitLN K)))
      (1 : (pullback X.hom (𝟙_ (Over (Spec (CommRingCat.of K)))).hom).Pic)
  unfold unitPtSite unitPt
  change (rep.homEquiv.symm ((kleimanIso X.hom).hom.app (op (unitLN K)) _)).hom = _
  rw [key]
  rfl

lemma unitPtSiteQ_repSiteQ {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    {P : Over (Spec (CommRingCat.of K))} {hP : LocNoeth _ P}
    (rep : (picardFunctorLN X.hom).RepresentableBy ⟨P, hP⟩) : unitPtSiteQ (repSiteQ rep) = unitPt rep := by
  set T : Over (Spec (CommRingCat.of K)) := 𝟙_ (Over (Spec (CommRingCat.of K)))
  -- the site comparison at the unit
  have key₁ : (sheafifyRestrictIso (KleimanSection.kleimanPicardPresheaf X.hom)).hom.app (op (unitLN K))
      ((toSheafify (fppfTopologyLN _) ((LocNoeth _).ι.op ⋙ KleimanSection.kleimanPicardPresheaf X.hom)).app
        (op (unitLN K)) (1 : (pullback X.hom T.hom).Pic ⧸ KleimanSection.picBase X.hom T)) =
      (toSheafify (fppfTopology.over _) (KleimanSection.kleimanPicardPresheaf X.hom)).app (op T)
        (1 : (pullback X.hom T.hom).Pic ⧸ KleimanSection.picBase X.hom T) :=
    ConcreteCategory.congr_hom
      (congr_app (toSheafify_sheafifyRestrictIso (KleimanSection.kleimanPicardPresheaf X.hom)) (op (unitLN K)))
      (1 : (pullback X.hom T.hom).Pic ⧸ KleimanSection.picBase X.hom T)
  -- the quotient comparison at the unit
  have key₂ : ((sheafToPresheaf _ _).mapIso (KleimanSection.picardFunctorIsoKleiman X.hom)).hom.app (op T)
      ((toSheafify (fppfTopology.over _) (picardPresheaf X.hom)).app (op T) (1 : (pullback X.hom T.hom).Pic)) =
      (toSheafify (fppfTopology.over _) (KleimanSection.kleimanPicardPresheaf X.hom)).app (op T)
        (1 : (pullback X.hom T.hom).Pic ⧸ KleimanSection.picBase X.hom T) :=
    (ConcreteCategory.congr_hom (congr_app (toSheafify_naturality (fppfTopology.over _)
      (KleimanSection.quot X.hom)) (op T)) (1 : (pullback X.hom T.hom).Pic)).symm
  have key₃ : ((sheafToPresheaf _ _).mapIso (KleimanSection.picardFunctorIsoKleiman X.hom)).inv.app (op T)
      ((toSheafify (fppfTopology.over _) (KleimanSection.kleimanPicardPresheaf X.hom)).app (op T)
        (1 : (pullback X.hom T.hom).Pic ⧸ KleimanSection.picBase X.hom T)) =
      (toSheafify (fppfTopology.over _) (picardPresheaf X.hom)).app (op T) (1 : (pullback X.hom T.hom).Pic) := by
    rw [← key₂]
    exact Iso.hom_inv_id_app_apply _ _ _
  unfold unitPtSiteQ unitPt
  change ((rep.homEquiv (X := unitLN K)).symm ((((sheafToPresheaf _ _).mapIso
    (KleimanSection.picardFunctorIsoKleiman X.hom)).inv.app (op T)
    ((sheafifyRestrictIso (KleimanSection.kleimanPicardPresheaf X.hom)).hom.app (op (unitLN K)) _)) :
      (picardFunctorLN X.hom).obj (op (unitLN K)))).hom = _
  rw [key₁, key₃]

/-- **The derivation (Def. 9.2.2 form)**: the tree-site form of the leaf from the Kleiman-site form with the
quotient functor `T ↦ Pic(X_T)/Pic(T)`. -/
theorem kleimanPicZeroProper954_of_siteQ (h : KleimanPicZeroProper954SiteQ) : KleimanPicZeroProper954 := by
  intro K _ X hproj hgi hgn hσ P hP rep V hV
  refine h K X hproj hgi hgn hσ P hP (repSiteQ rep) V ?_
  rw [hV]
  unfold identityComponentSiteQ identityComponentLN
  rw [unitPtSiteQ_repSiteQ]

/-- **The derivation (remark form)**: the tree-site form of the leaf from the Kleiman-site form with
`T ↦ Pic(X_T)`. -/
theorem kleimanPicZeroProper954_of_site (h : KleimanPicZeroProper954Site) : KleimanPicZeroProper954 := by
  intro K _ X hproj hgi hgn hσ P hP rep V hV
  refine h K X hproj hgi hgn hσ P hP (repSite rep) V ?_
  rw [hV]
  unfold identityComponentSite identityComponentLN
  rw [unitPtSite_repSite]

/-- **The consumer**: `PicZeroChar0.PicZeroAbVar0` from Kleiman 9.5.4 over Kleiman's site (Def. 9.2.2 form). -/
theorem picZeroAbVar0_of_siteQ (h : KleimanPicZeroProper954SiteQ) : PicZeroChar0.PicZeroAbVar0 :=
  picZeroAbVar0_of_954 (kleimanPicZeroProper954_of_siteQ h)

end KleimanSite

end
