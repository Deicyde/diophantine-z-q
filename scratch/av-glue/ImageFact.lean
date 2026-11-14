import Mathlib
import ZInQKernel.Contrib.AVB1.Poincare
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral

/-!
# av-glue, part B: `ImageFactorization` from Cartier's theorem

Check with `lake env lean scratch/av-glue/ImageFact.lean`.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace AVGlue

/-! ## §1. Scheme-level lemmas on scheme-theoretic images -/

section SchemeLevel

variable {X Y : Scheme.{0}}

/-- The morphism to the scheme-theoretic image has trivial kernel. -/
theorem ker_toImage (f : X ⟶ Y) [QuasiCompact f] : f.toImage.ker = ⊥ := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens => (⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩ : f.image.affineOpens))
    ?_ ?_
  · simp only
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · intro U
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      ← RingHom.injective_iff_ker_eq_bot]
    exact f.toImage_app_injective U

instance (f : X ⟶ Y) [QuasiCompact f] : IsSchemeTheoreticallyDominant f.toImage :=
  ⟨ker_toImage f⟩

/-- If `d` is scheme-theoretically dominant and `d ≫ g` factors through a closed immersion `i`,
then the kernel of `i` is contained in that of `g`. -/
theorem ker_le_of_dominant {V W Y' Z : Scheme.{0}} (d : V ⟶ W) [IsSchemeTheoreticallyDominant d]
    (g : W ⟶ Z) (i : Y' ⟶ Z) (a : V ⟶ Y') (h : d ≫ g = a ≫ i) : i.ker ≤ g.ker := by
  have h1 : g.ker = (d ≫ g).ker := by
    rw [Scheme.Hom.ker_comp, d.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  rw [h1, h, Scheme.Hom.ker_comp, ← Scheme.IdealSheafData.map_bot i]
  exact Scheme.IdealSheafData.map_mono i bot_le

/-- The morphism to the image is surjective for a proper map. -/
theorem surjective_toImage (f : X ⟶ Y) [IsProper f] : Surjective f.toImage := by
  have : IsProper (f.toImage ≫ f.imageι) := by rw [Scheme.Hom.toImage_imageι]; infer_instance
  have : IsProper f.toImage := IsProper.of_comp f.toImage f.imageι
  refine ⟨?_⟩
  rw [← Set.range_eq_univ, ← f.toImage.isClosedMap.isClosed_range.closure_eq]
  exact f.toImage.denseRange.closure_eq

end SchemeLevel

/-! ## §2. A subobject of a group object closed under the group law is a group object -/

section Transport

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {G Y : C} [GrpObj G]

/-- The group object structure on a subobject `i : Y ↪ G` closed under the group law. -/
@[reducible] noncomputable def grpObjOfMono (i : Y ⟶ G) [Mono i]
    (mulY : Y ⊗ Y ⟶ Y) (hmul : mulY ≫ i = fst Y Y ≫ i * snd Y Y ≫ i)
    (oneY : 𝟙_ C ⟶ Y) (hone : oneY ≫ i = η[G])
    (invY : Y ⟶ Y) (hinv : invY ≫ i = i⁻¹) : GrpObj Y where
  one := oneY
  mul := mulY
  one_mul := by
    apply (cancel_mono i).1
    simp only [Category.assoc, hmul, MonObj.comp_mul, whiskerRight_fst_assoc,
      whiskerRight_snd_assoc, hone, leftUnitor_hom]
    rw [show fst (𝟙_ C) Y ≫ η[G] = 1 by rw [Hom.one_def]; congr 1; exact toUnit_unique _ _,
      _root_.one_mul]
  mul_one := by
    apply (cancel_mono i).1
    simp only [Category.assoc, hmul, MonObj.comp_mul, whiskerLeft_fst_assoc,
      whiskerLeft_snd_assoc, hone, rightUnitor_hom]
    rw [show snd Y (𝟙_ C) ≫ η[G] = 1 by rw [Hom.one_def]; congr 1; exact toUnit_unique _ _,
      _root_.mul_one]
  mul_assoc := by
    apply (cancel_mono i).1
    simp only [Category.assoc, hmul, MonObj.comp_mul, whiskerRight_fst_assoc,
      whiskerRight_snd_assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc,
      associator_hom_fst_assoc, associator_hom_snd_fst_assoc, associator_hom_snd_snd_assoc]
    rw [_root_.mul_assoc]
  inv := invY
  left_inv := by
    apply (cancel_mono i).1
    simp only [Category.assoc, hmul, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hinv,
      hone, Category.id_comp]
    rw [inv_mul_cancel, Hom.one_def]
  right_inv := by
    apply (cancel_mono i).1
    simp only [Category.assoc, hmul, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hinv,
      hone, Category.id_comp]
    rw [mul_inv_cancel, Hom.one_def]

/-- The inclusion is a homomorphism for `grpObjOfMono`. -/
theorem isMonHom_grpObjOfMono (i : Y ⟶ G) [Mono i]
    (mulY : Y ⊗ Y ⟶ Y) (hmul : mulY ≫ i = fst Y Y ≫ i * snd Y Y ≫ i)
    (oneY : 𝟙_ C ⟶ Y) (hone : oneY ≫ i = η[G])
    (invY : Y ⟶ Y) (hinv : invY ≫ i = i⁻¹) :
    letI := grpObjOfMono i mulY hmul oneY hone invY hinv
    IsMonHom i := by
  letI := grpObjOfMono i mulY hmul oneY hone invY hinv
  refine ⟨hone, ?_⟩
  change mulY ≫ i = _
  rw [hmul, Hom.mul_def, ← lift_fst_comp_snd_comp]

/-- If `i` is a monic homomorphism and `π ≫ i` is a homomorphism, so is `π`. -/
theorem isMonHom_of_comp_mono {M : C} [MonObj M] [MonObj Y] (π : M ⟶ Y) (i : Y ⟶ G) [Mono i]
    [IsMonHom i] [IsMonHom (π ≫ i)] : IsMonHom π := by
  refine ⟨?_, ?_⟩
  · apply (cancel_mono i).1
    rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · apply (cancel_mono i).1
    rw [Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
      ← tensorHom_comp_tensorHom]

end Transport


/-! ## §3. Whiskerings in `Over S` are flat base changes -/

section Whisker

variable {Base : Scheme.{0}}

theorem isPullback_whiskerRight {R S' T : Over Base} (g : S' ⟶ T) :
    IsPullback (g ▷ R).left (pullback.fst S'.hom R.hom) (pullback.fst T.hom R.hom) g.left := by
  refine IsPullback.of_right (h₁₂ := pullback.snd T.hom R.hom) (h₂₂ := T.hom) (v₁₃ := R.hom)
    ?_ (Over.whiskerRight_left_fst g) (IsPullback.of_hasPullback T.hom R.hom).flip
  rw [Over.whiskerRight_left_snd, Over.w]
  exact (IsPullback.of_hasPullback S'.hom R.hom).flip

theorem isPullback_whiskerLeft {R S' T : Over Base} (g : S' ⟶ T) :
    IsPullback (R ◁ g).left (pullback.snd R.hom S'.hom) (pullback.snd R.hom T.hom) g.left := by
  refine IsPullback.of_right (h₁₂ := pullback.fst R.hom T.hom) (h₂₂ := T.hom) (v₁₃ := R.hom)
    ?_ (Over.whiskerLeft_left_snd g) (IsPullback.of_hasPullback R.hom T.hom)
  rw [Over.whiskerLeft_left_fst, Over.w]
  exact IsPullback.of_hasPullback R.hom S'.hom

theorem dominant_whiskerRight {R S' T : Over Base} (g : S' ⟶ T)
    [IsSchemeTheoreticallyDominant g.left] [QuasiCompact g.left] [Flat R.hom] :
    IsSchemeTheoreticallyDominant (g ▷ R).left :=
  IsSchemeTheoreticallyDominant.of_isPullback (isPullback_whiskerRight g).flip

theorem dominant_whiskerLeft {R S' T : Over Base} (g : S' ⟶ T)
    [IsSchemeTheoreticallyDominant g.left] [QuasiCompact g.left] [Flat R.hom] :
    IsSchemeTheoreticallyDominant (R ◁ g).left :=
  IsSchemeTheoreticallyDominant.of_isPullback (isPullback_whiskerLeft g).flip

end Whisker

/-! ## §4. The image of a homomorphism of abelian varieties -/

section Image

variable {k : Type} [Field k]

/-- A homomorphism of abelian varieties is proper. -/
theorem isProper_hom {A B : _root_.PkgI3.AbVar k} (h : A.X ⟶ B.X) : IsProper h.left := by
  have : IsProper (h.left ≫ B.X.hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp h.left B.X.hom

variable {A J : _root_.PkgI3.AbVar k} (f : A.X ⟶ J.X)

/-- The scheme-theoretic image of `f` (Mathlib's `Scheme.Hom.image`) as a `k`-scheme. -/
noncomputable abbrev imgOver : Over (Spec (CommRingCat.of k)) := Over.mk (f.left.imageι ≫ J.X.hom)

/-- The closed immersion of the image. -/
noncomputable def imgι : imgOver f ⟶ J.X := Over.homMk f.left.imageι rfl

/-- The map onto the image. -/
noncomputable def imgπ : A.X ⟶ imgOver f := Over.homMk f.left.toImage (by simp [imgOver])

@[simp] lemma imgι_left : (imgι f).left = f.left.imageι := rfl
@[simp] lemma imgπ_left : (imgπ f).left = f.left.toImage := rfl

@[reassoc (attr := simp)] lemma imgπ_imgι : imgπ f ≫ imgι f = f := by
  ext1; exact Scheme.Hom.toImage_imageι _

instance : IsClosedImmersion (imgι f).left := inferInstanceAs (IsClosedImmersion f.left.imageι)

instance : Mono (imgι f) := Over.mono_of_mono_left _

instance : QuasiCompact (imgπ f).left := by
  haveI := isProper_hom f; exact inferInstanceAs (QuasiCompact f.left.toImage)

instance : IsSchemeTheoreticallyDominant (imgπ f).left := by
  haveI := isProper_hom f; exact inferInstanceAs (IsSchemeTheoreticallyDominant f.left.toImage)

theorem surjective_imgπ : Surjective (imgπ f).left := by
  haveI := isProper_hom f; exact surjective_toImage f.left

/-- If `d` is scheme-theoretically dominant and `d ≫ g` factors through the image, so does `g`. -/
theorem exists_lift_imgι {V W : Over (Spec (CommRingCat.of k))} (d : V ⟶ W)
    [IsSchemeTheoreticallyDominant d.left] (g : W ⟶ J.X) (a : V ⟶ imgOver f)
    (h : d ≫ g = a ≫ imgι f) : ∃ c : W ⟶ imgOver f, c ≫ imgι f = g := by
  have H : f.left.imageι.ker ≤ g.left.ker :=
    ker_le_of_dominant d.left g.left f.left.imageι a.left (by
      rw [← Over.comp_left, h, Over.comp_left]; rfl)
  refine ⟨Over.homMk (IsClosedImmersion.lift f.left.imageι g.left H) ?_, ?_⟩
  · change IsClosedImmersion.lift f.left.imageι g.left H ≫ f.left.imageι ≫ J.X.hom = W.hom
    rw [IsClosedImmersion.lift_fac_assoc, Over.w]
  · ext1
    exact IsClosedImmersion.lift_fac f.left.imageι g.left H

variable [IsMonHom f]

theorem exists_mulY : ∃ m : imgOver f ⊗ imgOver f ⟶ imgOver f,
    m ≫ imgι f = fst _ _ ≫ imgι f * snd _ _ ≫ imgι f := by
  haveI : IsSchemeTheoreticallyDominant ((imgπ f ▷ A.X) ≫ (imgOver f ◁ imgπ f)).left := by
    rw [Over.comp_left]
    haveI := dominant_whiskerRight (R := A.X) (imgπ f)
    haveI := dominant_whiskerLeft (R := imgOver f) (imgπ f)
    infer_instance
  refine exists_lift_imgι f ((imgπ f ▷ A.X) ≫ (imgOver f ◁ imgπ f)) _ (μ[A.X] ≫ imgπ f) ?_
  simp only [MonObj.comp_mul, Category.assoc, whiskerLeft_fst_assoc, whiskerRight_fst_assoc,
    whiskerLeft_snd_assoc, whiskerRight_snd_assoc, imgπ_imgι]
  rw [← MonObj.mul_comp, ← MonObj.mul_eq_mul]

theorem exists_invY : ∃ v : imgOver f ⟶ imgOver f, v ≫ imgι f = (imgι f)⁻¹ := by
  refine exists_lift_imgι f (imgπ f) _ (ι[A.X] ≫ imgπ f) ?_
  rw [GrpObj.comp_inv, imgπ_imgι, Category.assoc, imgπ_imgι,
    show ι[A.X] = (𝟙 A.X)⁻¹ by rw [Hom.inv_def, Category.id_comp], GrpObj.inv_comp,
    Category.id_comp]

/-- The group structure of the image. -/
noncomputable abbrev imgGrp : GrpObj (imgOver f) :=
  grpObjOfMono (imgι f) (exists_mulY f).choose (exists_mulY f).choose_spec
    (η[A.X] ≫ imgπ f) (by rw [Category.assoc, imgπ_imgι, IsMonHom.one_hom])
    (exists_invY f).choose (exists_invY f).choose_spec

theorem isMonHom_imgι : letI := imgGrp f; IsMonHom (imgι f) :=
  isMonHom_grpObjOfMono _ _ _ _ _ _ _

theorem isMonHom_imgπ : letI := imgGrp f; IsMonHom (imgπ f) := by
  letI := imgGrp f
  haveI := isMonHom_imgι f
  haveI : IsMonHom (imgπ f ≫ imgι f) := by rw [imgπ_imgι]; infer_instance
  exact isMonHom_of_comp_mono (imgπ f) (imgι f)

/-- The image is geometrically connected (the base change of `A → f(A)` is surjective). -/
theorem geometricallyConnected_img : GeometricallyConnected (imgOver f).hom := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩
  haveI := surjective_imgπ f
  have e := pullbackRightPullbackFstIso (imgOver f).hom y (imgπ f).left
  have hA : (imgπ f).left ≫ (imgOver f).hom = A.X.hom := Over.w (imgπ f)
  haveI : IsIntegral (pullback (C := Scheme.{0}) A.X.hom y) := pullback_of_geometrically
    (GeometricallyIntegral.geometrically_isIntegral (f := A.X.hom)) K y
  haveI : ConnectedSpace (pullback (C := Scheme.{0}) ((imgπ f).left ≫ (imgOver f).hom) y) := by
    rw [hA]; infer_instance
  haveI : ConnectedSpace (pullback (C := Scheme.{0}) (imgπ f).left (pullback.fst (imgOver f).hom y)) :=
    e.hom.homeomorph.connectedSpace_iff.mpr inferInstance
  exact (pullback.snd (imgπ f).left (pullback.fst (imgOver f).hom y)).surjective.connectedSpace
    (pullback.snd (imgπ f).left (pullback.fst (imgOver f).hom y)).continuous

end Image


/-! ## §5. The leaf (Cartier's theorem) and `ImageFactorization` -/

/-- (verbatim copy of `ZInQ.Contrib.AVB1.ImageFactorization`, `ZInQKernel/Contrib/AVB1/Poincare.lean`)
**The image of a homomorphism is an abelian subvariety** (textbook; GLUE-level composite).
Over a field of characteristic `0`, every homomorphism `f : A → J` of abelian varieties factors
as `f = i ∘ h` with `h : A → B` a surjective homomorphism and `i : B → J` a homomorphism that is
a closed immersion, `B` an abelian variety. Sources (UNVERIFIED locators): the image `f(A)` is
closed (`A` proper), reduced and irreducible, a subgroup; a reduced group scheme of finite type
over a field of characteristic `0` is smooth (Cartier; Mumford, *Abelian varieties*, §11, Thm 1);
geometric integrality passes to the image of the geometrically integral `A`; Milne 1986 §8
(images of homomorphisms are abelian subvarieties). -/
def ImageFactorization : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A J : _root_.PkgI3.AbVar k)
    (f : _root_.PkgI3.AbVar.Hom A J),
    ∃ (B : _root_.PkgI3.AbVar k) (h : _root_.PkgI3.AbVar.Hom A B)
      (i : _root_.PkgI3.AbVar.Hom B J),
      Surjective h.hom.left ∧ IsClosedImmersion i.hom.left ∧ f.hom = h.hom ≫ i.hom

theorem imageFactorization_iff :
    ImageFactorization ↔ ZInQ.Contrib.AVB1.ImageFactorization := Iff.rfl

/-- **LEAF: Cartier's theorem.** A group scheme locally of finite type over a field of
characteristic `0` is smooth. Stated for a group object `G` (Mathlib's `GrpObj`) in the category
`Over (Spec k)` with its cartesian monoidal structure (fibre products over `k`), i.e. a group
scheme over `k`. Sources (locators UNVERIFIED, from memory): P. Cartier, *Groupes algébriques et
groupes formels*, Colloque Bruxelles 1962; F. Oort, *Algebraic group schemes in characteristic
zero are reduced*, Invent. Math. 2 (1966), 79-80; D. Mumford, *Abelian varieties*, §11, Thm 1
(Cartier's theorem); J. S. Milne, *Algebraic Groups* (CUP 2017), Thm 3.23; Stacks Project,
Groupoid schemes, "Cartier's theorem" (Tag 047N). The published statement, not strengthened (no
hypothesis dropped: `LocallyOfFiniteType` and characteristic `0`). -/
def CartierSmooth : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G],
    LocallyOfFiniteType G.hom → Smooth G.hom

section Final

variable {k : Type} [Field k] {A J : _root_.PkgI3.AbVar k} (f : A.X ⟶ J.X) [IsMonHom f]

instance : IsProper (imgOver f).hom := by
  change IsProper (f.left.imageι ≫ J.X.hom); infer_instance

/-- The image of `f` as an abelian variety, given Cartier's theorem. -/
noncomputable abbrev imgAbVar [CharZero k] (hC : CartierSmooth) : _root_.PkgI3.AbVar k :=
  letI := imgGrp f
  haveI : Smooth (imgOver f).hom := hC k (imgOver f) inferInstance
  haveI : GeometricallyConnected (imgOver f).hom := geometricallyConnected_img f
  haveI : GeometricallyIntegral (imgOver f).hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral _
  { X := imgOver f }

end Final

/-- **`ImageFactorization` from Cartier's theorem** (with Mathlib and the vendored Tau Ceti
theorem "smooth + geometrically connected ⇒ geometrically integral"). -/
theorem imageFactorization_of_cartier (hC : CartierSmooth) : ImageFactorization := by
  intro k _ _ A J f
  letI := imgGrp f.hom
  haveI : IsMonHom (imgι f.hom) := isMonHom_imgι f.hom
  haveI : IsMonHom (imgπ f.hom) := isMonHom_imgπ f.hom
  refine ⟨imgAbVar f.hom hC, _root_.PkgI3.AbVar.Hom.mk' (B := imgAbVar f.hom hC) (imgπ f.hom),
    _root_.PkgI3.AbVar.Hom.mk' (A := imgAbVar f.hom hC) (imgι f.hom), ?_, ?_, ?_⟩
  · exact surjective_imgπ f.hom
  · exact (inferInstance : IsClosedImmersion (imgι f.hom).left)
  · rw [_root_.PkgI3.AbVar.Hom.hom_mk', _root_.PkgI3.AbVar.Hom.hom_mk', imgπ_imgι]

end AVGlue

#print axioms AVGlue.imageFactorization_of_cartier
