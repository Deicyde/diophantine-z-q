import Mathlib
import ZInQKernel.Contrib.AVB1.Poincare
import ZInQKernel.Contrib.AbVarBC.Main
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral

/-! # OneProof H, leaf-fold7 part P: av-glue (`scratch/av-glue/Combined.lean`, verbatim apart from this banner and
the dropped `#print axioms` lines).

T8 = `PkgI3.PoincareReducibility` (the kernel's Prop) from `PoincareComplement`, `WeilPairing.IsogenyQuasiInverse`
(av-glue's copy `AVGlue.WeilPairing.IsogenyQuasiInverse`) and three published theorems on group schemes over a field:
`AVGlue.CartierSmooth`, `AVGlue.GeomConnOfRationalPoint`, `AVGlue.GroupSchemeEquidim` (docs/research/av-glue.md).
This module imports only kernel modules; `TailX` uses `AVGlue.poincareReducibility_of_published'`. -/


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


namespace AVGlue

/-! ## §1. Verbatim copy -/

/-- **A nonzero surjective homomorphism out of a simple abelian variety is an isogeny**
(textbook; GLUE-level composite). Over a field of characteristic `0`, if `End⁰(A)` is a division
algebra (`EndDivision A`) and `h : A → B` is a nonzero surjective homomorphism, then `h` is finite
(and surjective). Sources (UNVERIFIED locators): `(ker h)⁰_red` is an abelian subvariety of `A`
(characteristic `0`); it is not `A` since `h ≠ 0`; it is `0` because a proper nonzero abelian
subvariety would give, by Poincaré (Mumford §19 Thm 1, Cor. 1; Milne 1986 Prop. 12.1) and an
isogeny quasi-inverse, a nonzero endomorphism of `A` that is not surjective; a surjective
homomorphism with finite kernel is finite (Milne 1986, Prop. 7.1; Mumford §6, Application 1). -/
def SimpleSurjIsogeny : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A B : _root_.PkgI3.AbVar k), _root_.PkgI3.EndDivision A →
    ∀ h : _root_.PkgI3.AbVar.Hom A B, h ≠ 0 → Surjective h.hom.left →
      _root_.PkgI3.AbVar.IsIsogenyMor h.hom

theorem simpleSurjIsogeny_iff : SimpleSurjIsogeny ↔ ZInQ.Contrib.AVB1.SimpleSurjIsogeny := Iff.rfl

/-! ## §2. Leaves -/

/-- (verbatim from `ZInQKernel/HDecomp/Faltings/Leaves.lean`, `ZInQ.DefFaltings.IsIsogeny`)
An isogeny: a homomorphism of group schemes, finite and surjective. -/
def IsIsogeny {K : Type} [Field K] {A B : _root_.PkgI3.AbVar K} (φ : A.X ⟶ B.X) : Prop :=
  IsMonHom φ ∧ IsFinite φ.left ∧ Surjective φ.left

/-- **LEAF (Mumford; Milne).** Verbatim text of `HSyn.G0RevIsog.IsogenyQuasiInverse`
(`scratch/av-b2/olean/TailA.lean` l. 1660; g0-revisog), with `ZInQ.DefFaltings.AbVar` (a
structure with the same five fields as `PkgI3.AbVar` in that assembly; in the kernel
`ZInQ.DefFaltings` opens `PkgI3 (AbVar)`) written `PkgI3.AbVar`.
An isogeny `φ : A → B` of abelian varieties over a field `K` (a homomorphism of group schemes
that is finite and surjective) has a quasi-inverse: an isogeny `ψ : B → A` and an integer `n ≥ 1`
(the degree of `φ`) with `ψ ∘ φ = [n]_A` and `φ ∘ ψ = [n]_B`. Here `[n]_A` is `(𝟙 A)ⁿ` in
Mathlib's group of morphisms into the group object `A`. Sources (numbers UNVERIFIED): Mumford,
*Abelian Varieties*, §7 Remark after Thm 4 / §8; Milne, *Abelian Varieties* (Cornell-Silverman
1986) §8 and Milne's notes *Abelian Varieties* (2008) I, Prop. 7.1, Remark 7.2 (any field). -/
def IsogenyQuasiInverse : Prop :=
  ∀ (K : Type) [Field K] (A B : _root_.PkgI3.AbVar K) (φ : A.X ⟶ B.X),
    IsIsogeny φ →
    ∃ (ψ : B.X ⟶ A.X) (n : ℕ), 0 < n ∧ IsIsogeny ψ ∧
      φ ≫ ψ = (𝟙 A.X) ^ n ∧ ψ ≫ φ = (𝟙 B.X) ^ n

/-- **LEAF (new; `(ker h)⁰_red` is an abelian subvariety).** Over a field of characteristic `0`,
if a homomorphism `h : A → B` of abelian varieties is not locally quasi-finite (equivalently, its
kernel is positive-dimensional), there is an abelian subvariety `C ⊆ A` of positive dimension
killed by `h`: an abelian variety `C` with a homomorphism `j : C → A` that is a closed immersion,
`0 < dim C`, and `h ∘ j = 0`. Take `C = (ker h)⁰_red`. Sources (UNVERIFIED locators): the reduced
identity component of a closed subgroup scheme of an abelian variety is an abelian subvariety
(Milne, *Abelian varieties*, Cornell-Silverman 1986, §8 / notes (2008) I §8; Mumford §8; reduced
⇒ smooth: Mumford §11 Thm 1 (Cartier), char `0`); the fibres of `h` over `k̄`-points are
translates of `ker h`, so `h` is quasi-finite iff `ker h` is finite (Mumford §4, Milne 1986 §7).
A consequence of these published statements, never stronger: `C` is existential. -/
def KernelAbSubvariety : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A B : _root_.PkgI3.AbVar k)
    (h : _root_.PkgI3.AbVar.Hom A B), ¬ LocallyQuasiFinite h.hom.left →
    ∃ (C : _root_.PkgI3.AbVar k) (j : _root_.PkgI3.AbVar.Hom C A),
      IsClosedImmersion j.hom.left ∧ 0 < C.dim ∧ j.hom ≫ h.hom = 1

/-! ## §3. Products of abelian varieties (copied from `scratch/g0-product/Product.lean`) -/

/-- (verbatim from `scratch/g0-product/Product.lean`) Geometric integrality is stable under
composition `X → Y → S` when the first map is geometrically integral, flat and universally open
and the second is geometrically integral and locally of finite type. -/
theorem geometricallyIntegral_comp {X Y S : Scheme} (g : X ⟶ Y) (h : Y ⟶ S)
    [GeometricallyIntegral g] [Flat g] [UniversallyOpen g]
    [GeometricallyIntegral h] [LocallyOfFiniteType h] :
    GeometricallyIntegral (g ≫ h) := by
  refine ⟨fun K _ y Z fst snd hP => ?_⟩
  have : IsIntegral (pullback h y) := pullback_of_geometrically
    (GeometricallyIntegral.geometrically_isIntegral (f := h)) K y
  have : IsLocallyNoetherian (pullback h y) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd h y)
  have hI : IsIntegral (pullback g (pullback.fst h y)) := inferInstance
  let e : Z ≅ pullback g (pullback.fst h y) :=
    hP.isoPullback ≪≫ (pullbackRightPullbackFstIso h y g).symm
  have : Nonempty Z := ⟨e.inv (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion e.hom

/-- The product `C ×_k Z` (Mathlib's cartesian monoidal product in `Over (Spec k)`, product
group structure) as a `PkgI3.AbVar` (same proof as g0-product's `prodAbVar`). -/
noncomputable abbrev prodAbVar {K : Type} [Field K] (A Z : _root_.PkgI3.AbVar K) :
    _root_.PkgI3.AbVar K :=
  haveI : IsProper (A.X ⊗ Z.X).hom := by dsimp; infer_instance
  haveI : Smooth (A.X ⊗ Z.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral (A.X ⊗ Z.X).hom := by
    rw [Over.tensorObj_hom]; exact geometricallyIntegral_comp _ _
  { X := A.X ⊗ Z.X }

/-! ## §4. Glue -/

section Glue

variable {k : Type} [Field k]

/-- The underlying scheme of an abelian variety is integral. -/
instance isIntegral_left (A : _root_.PkgI3.AbVar k) : IsIntegral A.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom

/-- A homomorphism of abelian varieties is proper. -/
theorem isProper_hom' {A B : _root_.PkgI3.AbVar k} (h : A.X ⟶ B.X) : IsProper h.left := by
  have : IsProper (h.left ≫ B.X.hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp h.left B.X.hom

/-- If `j : C → A` is a closed immersion whose composite with a homomorphism `h` is `0` and `j`
is surjective, then `h = 0` (`A` is reduced). -/
theorem hom_eq_one_of_surjective {C A B : _root_.PkgI3.AbVar k} (j : C.X ⟶ A.X) (h : A.X ⟶ B.X)
    [IsClosedImmersion j.left] [Surjective j.left] (hjh : j ≫ h = 1) : h = 1 := by
  have : IsIso j.left := isIso_of_isClosedImmersion_of_surjective j.left
  have : IsIso ((Over.forget _).map j) := (inferInstance : IsIso j.left)
  have : IsIso j := isIso_of_reflects_iso j (Over.forget _)
  calc h = inv j ≫ (j ≫ h) := by simp
    _ = 1 := by rw [hjh, MonObj.comp_one]

/-- If `j : C → A` is an embedding whose composite with a finite map `m : A → A'` is constant
(`= 1`), then `C` is discrete, so `dim C ≤ 0`. -/
theorem dim_le_zero_of_comp_one {C A : _root_.PkgI3.AbVar k} (j : C.X ⟶ A.X)
    [IsClosedImmersion j.left] (m : A.X ⟶ A.X) [IsFinite m.left] (hjm : j ≫ m = 1) :
    C.dim ≤ 0 := by
  set e : A.X.left := (η[A.X]).left (Nonempty.some (inferInstance : Nonempty
    (Spec (CommRingCat.of k)))) with he
  have hsub : Set.range j.left ⊆ m.left ⁻¹' {e} := by
    rintro _ ⟨x, rfl⟩
    have h1 : (j ≫ m).left = (toUnit C.X ≫ η[A.X]).left := by rw [hjm, Hom.one_def]
    rw [Over.comp_left, Over.comp_left] at h1
    have h2 : (j.left ≫ m.left) x = ((toUnit C.X).left ≫ (η[A.X]).left) x := by rw [h1]
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h2
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [h2, he]
    congr 1
    have : Subsingleton (𝟙_ (Over (Spec (CommRingCat.of k)))).left :=
      (inferInstance : Subsingleton (Spec (CommRingCat.of k)))
    exact Subsingleton.elim _ _
  have hdisc : _root_.IsDiscrete (m.left ⁻¹' {e}) := m.left.isDiscrete_preimage_singleton e
  have : DiscreteTopology (m.left ⁻¹' {e}) := hdisc.to_subtype
  have hemb : Topology.IsEmbedding (Set.codRestrict j.left _ fun x => hsub ⟨x, rfl⟩) :=
    j.left.isClosedEmbedding.isEmbedding.codRestrict _ _
  have : DiscreteTopology C.X.left := hemb.discreteTopology
  exact topologicalKrullDim_zero_of_discreteTopology C.X.left

end Glue

/-- **`SimpleSurjIsogeny` from three leaves.** -/
theorem simpleSurjIsogeny_of_leaves (hP : ZInQ.Contrib.AVB1.PoincareComplement)
    (hQ : IsogenyQuasiInverse) (hK : KernelAbSubvariety) : SimpleSurjIsogeny := by
  intro k _ _ A B hA h hh hsurj
  have hprop : IsProper h.hom.left := isProper_hom' h.hom
  suffices hlqf : LocallyQuasiFinite h.hom.left from
    ⟨IsFinite.of_isProper_of_locallyQuasiFinite h.hom.left, hsurj⟩
  by_contra hnot
  obtain ⟨C, j, hjci, hCdim, hjh⟩ := hK k A B h hnot
  obtain ⟨Z, g, hφ⟩ := hP k A C j hjci
  set φ : (C.X ⊗ Z.X) ⟶ A.X := fst C.X Z.X ≫ j.hom * snd C.X Z.X ≫ g.hom with hφ_def
  have hφmon : IsMonHom φ := by
    change IsMonHom (lift (fst C.X Z.X ≫ j.hom) (snd C.X Z.X ≫ g.hom) ≫ μ[A.X])
    infer_instance
  obtain ⟨ψ, n, hn, ⟨hψmon, hψfin, hψsurj⟩, hφψ, hψφ⟩ := hQ k (prodAbVar C Z) A φ ⟨hφmon, hφ.1, hφ.2⟩
  -- the endomorphism `e = j ∘ pr₁ ∘ ψ`
  set e : A.X ⟶ A.X := ψ ≫ fst C.X Z.X ≫ j.hom with he_def
  haveI := hψmon
  haveI : IsMonHom e := by
    change IsMonHom (ψ ≫ fst C.X Z.X ≫ j.hom)
    infer_instance
  set E : _root_.PkgI3.AbVar.End A := _root_.PkgI3.AbVar.Hom.mk' e with hE_def
  haveI : IsClosedImmersion j.hom.left := hjci
  by_cases hE : E = 0
  · -- `e = 0` forces `j ∘ [n] = 0` with `[n] = φ ∘ ψ` finite, so `C` is discrete
    have he0 : e = 1 := by
      have := congrArg _root_.PkgI3.AbVar.Hom.hom hE
      simpa [hE_def] using this
    have hjn : j.hom ≫ ((𝟙 A.X) ^ n) = 1 := by
      have h1 : φ ≫ e = 1 := by rw [he0, MonObj.comp_one]
      have h2 : φ ≫ e = ((𝟙 (C.X ⊗ Z.X)) ^ n) ≫ fst C.X Z.X ≫ j.hom := by
        rw [he_def, ← Category.assoc, hφψ]
      have h3 : (lift (𝟙 C.X) (1 : C.X ⟶ Z.X) : C.X ⟶ (C.X ⊗ Z.X)) ≫ φ = j.hom := by
        rw [hφ_def, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd,
          Category.id_comp, MonObj.one_comp, _root_.mul_one]
      have h4 : (lift (𝟙 C.X) (1 : C.X ⟶ Z.X) : C.X ⟶ (C.X ⊗ Z.X)) ≫ ((𝟙 (C.X ⊗ Z.X)) ^ n) ≫ fst C.X Z.X ≫ j.hom
          = 1 := by rw [← h2, h1, MonObj.comp_one]
      haveI : IsMonHom (fst C.X Z.X ≫ j.hom) := inferInstance
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, MonObj.pow_comp,
        ← Category.assoc, lift_fst, Category.id_comp] at h4
      rw [MonObj.comp_pow, Category.comp_id]
      exact h4
    have hfin : IsFinite ((𝟙 A.X) ^ n).left := by
      haveI := hψfin
      haveI : IsFinite φ.left := hφ.1
      rw [← hψφ, Over.comp_left]; infer_instance
    have := dim_le_zero_of_comp_one j.hom ((𝟙 A.X) ^ n) hjn
    exact absurd hCdim (not_lt.mpr this)
  · -- `e ≠ 0` is an isogeny, so `j` is surjective, so `h = 0`
    obtain ⟨-, hesurj⟩ := hA E hE
    have hjsurj : Surjective j.hom.left := by
      have h1 : Surjective (ψ.left ≫ (fst C.X Z.X ≫ j.hom).left) := by
        simpa [hE_def, he_def] using hesurj
      have h2 : Surjective (fst C.X Z.X ≫ j.hom).left := Surjective.of_comp ψ.left _
      rw [Over.comp_left] at h2
      exact Surjective.of_comp (fst C.X Z.X).left _
    apply hh
    apply _root_.PkgI3.AbVar.Hom.ext'
    rw [_root_.PkgI3.AbVar.Hom.hom_zero]
    exact hom_eq_one_of_surjective j.hom h.hom hjh

end AVGlue


/-! ## §5. Variant: the quasi-inverse on `K̄`-points (the assembly's existing leaf) -/

namespace AVGlue.WeilPairing

open _root_.PkgI3 _root_.PkgI3.AbVar

variable {K : Type} [Field K]

/-- (verbatim from weil-pairing, `scratch/av-b2/olean/TailB.lean` l. 5484) The group `A(K̄)`,
written additively. -/
abbrev P (A : AbVar K) : Type := Additive (A.Pt (AlgebraicClosure K))

/-- (verbatim, l. 5570) A homomorphism `f : A → B` acting on `K̄`-points. -/
noncomputable def homP {A B : AbVar K} (f : Hom A B) : P A →+ P B := MonoidHom.toAdditive (ptMap f)

/-- (verbatim, l. 5771) `ψ : Â → A` is a quasi-inverse of `λ` of exponent `d`: `λ ψ = [d]` on
`Â(K̄)` and `ψ λ = [d]` on `A(K̄)`. -/
def IsQuasiInverse {A B : AbVar K} (f : Hom A B) (g : Hom B A) (d : ℕ) : Prop :=
  (∀ z : P B, homP f (homP g z) = d • z) ∧ ∀ x : P A, homP g (homP f x) = d • x

/-- (verbatim, l. 5864; the canonical assembly's LEAF field `isogenyQuasiInverse`, H-54)
**Quasi-inverse of an isogeny.** For an isogeny `f : A → B` (finite and surjective) there are
`d ≥ 1` and `g : B → A` with `f g = [d]`, `g f = [d]` (take `d = deg f`, which kills `ker f`;
Mumford §7, Remark after Thm 4, and §8 Thm 1 (UNVERIFIED numbering); Milne 1986, Prop. 7.1 /
Rem. 8.4 (UNVERIFIED)). Stated on `K̄`-points, a consequence. -/
def IsogenyQuasiInverse : Prop :=
  ∀ (K : Type) [Field K] (A B : AbVar K) (f : Hom A B), IsIsogenyMor f.hom →
    ∃ d : ℕ, 0 < d ∧ ∃ g : Hom B A, IsQuasiInverse f g d

end AVGlue.WeilPairing

namespace AVGlue

section PointsExt

variable {K : Type} [Field K]

/-- **Homomorphisms of abelian varieties are determined by their `K̄`-points** (glue, proved):
two `K`-morphisms `u v : A → B` agreeing on `A(K̄)` are equal. Closed points of `A` are dense
(Jacobson), each closed point has a residue field finite over `K`, which embeds into `K̄`, and
`Spec K̄ → Spec κ(x)` is an epimorphism; Mathlib's `ext_of_fromSpecResidueField_eq`. -/
theorem hom_ext_of_points {A B : _root_.PkgI3.AbVar K} (u v : A.X ⟶ B.X)
    (H : ∀ z : A.Pt (AlgebraicClosure K), z ≫ u = z ≫ v) : u = v := by
  ext1
  haveI : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
  refine ext_of_fromSpecResidueField_eq u.left v.left B.X.hom (closedPoints A.X.left)
    (by rw [dense_iff_closure_eq]; exact closure_closedPoints) ?_ (by rw [Over.w u, Over.w v])
  intro x hx
  have hx' : IsClosed {x} := hx
  have hfin : IsFinite (A.X.left.fromSpecResidueField x ≫ A.X.hom) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hx'
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  set ι0 : CommRingCat.of K ⟶ A.X.left.residueField x :=
    Spec.preimage (A.X.left.fromSpecResidueField x ≫ A.X.hom) with hι0
  have hint : ι0.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, hι0, Spec.map_preimage]; infer_instance
  letI : Algebra K (A.X.left.residueField x) := ι0.hom.toAlgebra
  haveI : Algebra.IsIntegral K (A.X.left.residueField x) := ⟨hint⟩
  let φ : A.X.left.residueField x →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  have hφι : ι0 ≫ CommRingCat.ofHom φ.toRingHom =
      CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
    ext c; exact φ.commutes c
  let z : A.Pt (AlgebraicClosure K) :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ A.X.left.fromSpecResidueField x) (by
      change (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ A.X.left.fromSpecResidueField x) ≫
        A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
      rw [Category.assoc, ← Spec.map_preimage (A.X.left.fromSpecResidueField x ≫ A.X.hom),
        ← hι0, ← Spec.map_comp]
      exact congrArg Spec.map hφι)
  have h2 := congrArg Over.Hom.left (H z)
  simp only [Over.comp_left, z, Over.homMk_left] at h2
  have h3 : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ A.X.left.fromSpecResidueField x ≫ u.left =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ A.X.left.fromSpecResidueField x ≫ v.left := by
    have h4 := h2
    erw [Category.assoc, Category.assoc] at h4
    exact h4
  haveI : Epi (Spec.map (CommRingCat.ofHom φ.toRingHom)) := Flat.epi_of_flat_of_surjective _
  exact (cancel_epi _).1 h3

/-- `[n]` as the integer `n ∈ End A`. -/
theorem natCast_hom (A : _root_.PkgI3.AbVar K) (n : ℕ) :
    (((n : ℤ) : _root_.PkgI3.AbVar.End A)).hom = (𝟙 A.X) ^ n := by
  rw [Int.cast_natCast]
  induction n with
  | zero => rw [Nat.cast_zero, _root_.PkgI3.AbVar.Hom.hom_zero, pow_zero]
  | succ n ih =>
    rw [Nat.cast_succ, _root_.PkgI3.AbVar.Hom.hom_add, ih, pow_succ]
    rfl

/-- The second clause of `IsQuasiInverse` as an identity of morphisms. -/
theorem comp_eq_pow_of_isQuasiInverse {A B : _root_.PkgI3.AbVar K}
    (f : _root_.PkgI3.AbVar.Hom A B) (g : _root_.PkgI3.AbVar.Hom B A) (d : ℕ)
    (hq : WeilPairing.IsQuasiInverse f g d) : f.hom ≫ g.hom = (𝟙 A.X) ^ d := by
  apply hom_ext_of_points
  intro z
  have := congrArg Additive.toMul (hq.2 (Additive.ofMul z))
  rw [toMul_nsmul, toMul_ofMul] at this
  rw [MonObj.comp_pow, Category.comp_id]
  exact this

end PointsExt

/-- **`SimpleSurjIsogeny` from `PoincareComplement`, the assembly's `K̄`-point quasi-inverse leaf
and `KernelAbSubvariety`** (with the kernel's proved `MulIsogeny`, g9-abvarbc). -/
theorem simpleSurjIsogeny_of_leaves' (hP : ZInQ.Contrib.AVB1.PoincareComplement)
    (hQ : WeilPairing.IsogenyQuasiInverse) (hK : KernelAbSubvariety) : SimpleSurjIsogeny := by
  intro k _ _ A B hA h hh hsurj
  have hprop : IsProper h.hom.left := isProper_hom' h.hom
  suffices hlqf : LocallyQuasiFinite h.hom.left from
    ⟨IsFinite.of_isProper_of_locallyQuasiFinite h.hom.left, hsurj⟩
  by_contra hnot
  obtain ⟨C, j, hjci, hCdim, hjh⟩ := hK k A B h hnot
  obtain ⟨Z, g, hφ⟩ := hP k A C j hjci
  set φ : (C.X ⊗ Z.X) ⟶ A.X := fst C.X Z.X ≫ j.hom * snd C.X Z.X ≫ g.hom with hφ_def
  haveI hφmon : IsMonHom φ := by
    change IsMonHom (lift (fst C.X Z.X ≫ j.hom) (snd C.X Z.X ≫ g.hom) ≫ μ[A.X])
    infer_instance
  obtain ⟨n, hn, ψH, hq⟩ := hQ k (prodAbVar C Z) A
    (_root_.PkgI3.AbVar.Hom.mk' (A := prodAbVar C Z) φ) hφ
  set ψ : A.X ⟶ (C.X ⊗ Z.X) := ψH.hom with hψ_def
  have hφψ : φ ≫ ψ = (𝟙 (C.X ⊗ Z.X)) ^ n := comp_eq_pow_of_isQuasiInverse _ ψH n hq
  set e : A.X ⟶ A.X := ψ ≫ fst C.X Z.X ≫ j.hom with he_def
  haveI : IsMonHom e := by
    change IsMonHom (ψH.hom ≫ fst C.X Z.X ≫ j.hom)
    infer_instance
  set E : _root_.PkgI3.AbVar.End A := _root_.PkgI3.AbVar.Hom.mk' e with hE_def
  haveI : IsClosedImmersion j.hom.left := hjci
  by_cases hE : E = 0
  · have he0 : e = 1 := by
      have := congrArg _root_.PkgI3.AbVar.Hom.hom hE
      simpa [hE_def] using this
    have hjn : j.hom ≫ ((𝟙 A.X) ^ n) = 1 := by
      have h1 : φ ≫ e = 1 := by rw [he0, MonObj.comp_one]
      have h2 : φ ≫ e = ((𝟙 (C.X ⊗ Z.X)) ^ n) ≫ fst C.X Z.X ≫ j.hom := by
        rw [he_def, ← Category.assoc, hφψ]
      have h4 : (lift (𝟙 C.X) (1 : C.X ⟶ Z.X) : C.X ⟶ (C.X ⊗ Z.X)) ≫ ((𝟙 (C.X ⊗ Z.X)) ^ n) ≫
          fst C.X Z.X ≫ j.hom = 1 := by rw [← h2, h1, MonObj.comp_one]
      haveI : IsMonHom (fst C.X Z.X ≫ j.hom) := inferInstance
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, MonObj.pow_comp,
        ← Category.assoc, lift_fst, Category.id_comp] at h4
      rw [MonObj.comp_pow, Category.comp_id]
      exact h4
    have hfin : IsFinite ((𝟙 A.X) ^ n).left := by
      rw [← natCast_hom]
      exact (ZInQ.Contrib.AbVarBC.mulIsogeny k A n (by exact_mod_cast hn.ne')).1
    have := dim_le_zero_of_comp_one j.hom ((𝟙 A.X) ^ n) hjn
    exact absurd hCdim (not_lt.mpr this)
  · obtain ⟨-, hesurj⟩ := hA E hE
    have hjsurj : Surjective j.hom.left := by
      have h1 : Surjective (ψ.left ≫ (fst C.X Z.X ≫ j.hom).left) := by
        simpa [hE_def, he_def] using hesurj
      have h2 : Surjective (fst C.X Z.X ≫ j.hom).left := Surjective.of_comp ψ.left _
      rw [Over.comp_left] at h2
      exact Surjective.of_comp (fst C.X Z.X).left _
    apply hh
    apply _root_.PkgI3.AbVar.Hom.ext'
    rw [_root_.PkgI3.AbVar.Hom.hom_zero]
    exact hom_eq_one_of_surjective j.hom h.hom hjh

end AVGlue


namespace AVGlue



section Kernel

variable {k : Type} [Field k] {A B : _root_.PkgI3.AbVar k} (h : A.X ⟶ B.X)

/-- The kernel `ker h = A ×_B Spec k` (fibre product of `h` with the identity section), as a
`k`-scheme. -/
noncomputable abbrev kerOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (pullback.fst h.left (η[B.X]).left ≫ A.X.hom)

/-- The inclusion of the kernel. -/
noncomputable def kerι : kerOver h ⟶ A.X := Over.homMk (pullback.fst h.left (η[B.X]).left) rfl

lemma kerι_left : (kerι h).left = pullback.fst h.left (η[B.X]).left := rfl

instance : Mono (kerι h) := by
  haveI : Mono (kerι h).left := (inferInstance : Mono (pullback.fst h.left (η[B.X]).left))
  exact Over.mono_of_mono_left _

lemma ker_snd_eq :
    pullback.snd h.left (η[B.X]).left = pullback.fst h.left (η[B.X]).left ≫ A.X.hom := by
  have h2 := congrArg (· ≫ B.X.hom) (pullback.condition (f := h.left) (g := (η[B.X]).left))
  simp only [Category.assoc, Over.w] at h2
  simpa using h2.symm

lemma kerι_comp : kerι h ≫ h = 1 := by
  ext1
  rw [Over.comp_left, Hom.one_def, Over.comp_left, Over.toUnit_left, kerι_left, pullback.condition,
    ker_snd_eq]
  rfl

/-- Lifting into the kernel. -/
noncomputable def kerLift {W : Over (Spec (CommRingCat.of k))} (g : W ⟶ A.X) (hg : g ≫ h = 1) :
    W ⟶ kerOver h :=
  Over.homMk (pullback.lift g.left W.hom (by
    have := congrArg Over.Hom.left hg
    rwa [Over.comp_left, Hom.one_def, Over.comp_left, Over.toUnit_left] at this)) (by simp)

@[reassoc (attr := simp)]
lemma kerLift_ι {W : Over (Spec (CommRingCat.of k))} (g : W ⟶ A.X) (hg : g ≫ h = 1) :
    kerLift h g hg ≫ kerι h = g := by
  ext1; simp [kerLift, kerι]

/-! ### The shear isomorphism `A ×_k ker h ≅ A ×_B A` -/

variable [IsMonHom h]

/-- `(a, x) ↦ a + x`. -/
noncomputable def shearS : A.X ⊗ kerOver h ⟶ A.X := fst _ _ * (snd _ _ ≫ kerι h)

lemma shearS_comp : shearS h ≫ h = fst _ _ ≫ h := by
  rw [shearS, MonObj.mul_comp, Category.assoc, kerι_comp, MonObj.comp_one, _root_.mul_one]

/-- `A ×_B A` as a `k`-scheme. -/
noncomputable abbrev pbOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (pullback.fst h.left h.left ≫ A.X.hom)

lemma pb_w : pullback.snd h.left h.left ≫ A.X.hom = pullback.fst h.left h.left ≫ A.X.hom := by
  have h2 := congrArg (· ≫ B.X.hom) (pullback.condition (f := h.left) (g := h.left))
  simp only [Category.assoc, Over.w] at h2
  exact h2.symm

noncomputable def pbFst : pbOver h ⟶ A.X := Over.homMk (pullback.fst h.left h.left) rfl
noncomputable def pbSnd : pbOver h ⟶ A.X := Over.homMk (pullback.snd h.left h.left) (pb_w h)

lemma pbFst_comp : pbFst h ≫ h = pbSnd h ≫ h := by
  ext1; exact pullback.condition

/-- `(a, a') ↦ a' - a`. -/
noncomputable def pbD : pbOver h ⟶ A.X := (pbFst h)⁻¹ * pbSnd h

lemma pbD_comp : pbD h ≫ h = 1 := by
  rw [pbD, MonObj.mul_comp, GrpObj.inv_comp, pbFst_comp, inv_mul_cancel]

noncomputable def pbT : pbOver h ⟶ kerOver h := kerLift h (pbD h) (pbD_comp h)

/-- The shear map `A ×_k ker h → A ×_B A`. -/
noncomputable def shearHom : (A.X ⊗ kerOver h).left ⟶ pullback h.left h.left :=
  pullback.lift (fst A.X (kerOver h)).left (shearS h).left (by
    rw [← Over.comp_left, ← Over.comp_left, shearS_comp])

/-- Its inverse. -/
noncomputable def shearInv : pullback h.left h.left ⟶ (A.X ⊗ kerOver h).left :=
  pullback.lift (pullback.fst h.left h.left) (pbT h).left (by
    have := Over.w (pbT h)
    simpa using this.symm)

noncomputable def shearHomO : A.X ⊗ kerOver h ⟶ pbOver h :=
  Over.homMk (shearHom h) (by simp [shearHom])

noncomputable def shearInvO : pbOver h ⟶ A.X ⊗ kerOver h :=
  Over.homMk (shearInv h) (by simp [shearInv])

lemma shearHomO_fst : shearHomO h ≫ pbFst h = fst _ _ := by
  ext1; simp [shearHomO, pbFst, shearHom]

lemma shearHomO_snd : shearHomO h ≫ pbSnd h = shearS h := by
  ext1; simp [shearHomO, pbSnd, shearHom]

lemma shearInvO_fst : shearInvO h ≫ fst _ _ = pbFst h := by
  ext1; simp [shearInvO, pbFst, shearInv]

lemma shearInvO_snd : shearInvO h ≫ snd _ _ = pbT h := by
  ext1; simp [shearInvO, shearInv]

/-- The shear isomorphism. -/
noncomputable def shearIso : (A.X ⊗ kerOver h).left ≅ pullback h.left h.left where
  hom := shearHom h
  inv := shearInv h
  hom_inv_id := by
    apply pullback.hom_ext
    · simp [shearHom, shearInv]
    · apply (cancel_mono (pullback.fst h.left (η[B.X]).left)).1
      have e1 : shearHomO h ≫ pbD h = snd _ _ ≫ kerι h := by
        rw [pbD, MonObj.comp_mul, GrpObj.comp_inv, shearHomO_fst, shearHomO_snd, shearS,
          inv_mul_cancel_left]
      have e2 := congrArg Over.Hom.left e1
      simp only [Over.comp_left] at e2
      simp only [Category.assoc, shearInv, pullback.lift_snd]
      change shearHom h ≫ (pbT h ≫ kerι h).left = _
      rw [pbT, kerLift_ι]
      exact e2.trans (by simp [kerι])
  inv_hom_id := by
    apply pullback.hom_ext
    · simp [shearHom, shearInv]
    · have e1 : shearInvO h ≫ shearS h = pbSnd h := by
        rw [shearS, MonObj.comp_mul, ← Category.assoc, shearInvO_fst, shearInvO_snd, pbT,
          kerLift_ι, pbD, mul_inv_cancel_left]
      have e2 := congrArg Over.Hom.left e1
      simp only [Over.comp_left] at e2
      simp only [Category.assoc, shearHom, pullback.lift_snd]
      change shearInv h ≫ (shearS h).left = _
      exact e2.trans (by simp [pbSnd])

lemma shearIso_hom_fst :
    (shearIso h).hom ≫ pullback.fst h.left h.left = pullback.fst A.X.hom (kerOver h).hom := by
  simp [shearIso, shearHom]

/-- **If the kernel is locally quasi-finite over `k`, so is `h`.** -/
theorem lqf_of_ker [IsProper h.left] (hK : LocallyQuasiFinite (kerOver h).hom) :
    LocallyQuasiFinite h.left := by
  haveI : LocallyQuasiFinite (pullback.fst A.X.hom (kerOver h).hom) := inferInstance
  haveI : LocallyQuasiFinite (pullback.fst h.left h.left) := by
    have : pullback.fst h.left h.left =
        (shearIso h).inv ≫ pullback.fst A.X.hom (kerOver h).hom := by
      rw [← shearIso_hom_fst, Iso.inv_hom_id_assoc]
    rw [this]; infer_instance
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun y => ?_
  by_cases hy : y ∈ Set.range h.left
  · obtain ⟨x0, rfl⟩ := hy
    refine (((pullback.fst h.left h.left).finite_preimage_singleton x0).image
      (pullback.snd h.left h.left)).subset ?_
    intro a ha
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x0 a ha.symm
    exact ⟨z, hz1, hz2⟩
  · exact Set.finite_empty.subset fun a ha => hy ⟨a, ha⟩

end Kernel



/-! ## The identity component of the kernel -/

/-- In a noetherian space, connected components are open. -/
theorem isOpen_connectedComponent_of_noetherian {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] (x : X) : IsOpen (connectedComponent x) := by
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have heq : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents X | Disjoint Z (connectedComponent x)}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hy
      obtain ⟨Z, hZ, hyZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {y}
        isIrreducible_singleton
      refine ⟨Z, ⟨hZ, ?_⟩, hyZ rfl⟩
      have hZy : Z ⊆ connectedComponent y :=
        hZ.1.isConnected.isPreconnected.subset_connectedComponent
          (hyZ rfl)
      refine Set.disjoint_of_subset_left hZy ?_
      rw [Set.disjoint_iff]
      rintro w ⟨hw1, hw2⟩
      apply hy
      rw [connectedComponent_eq hw2, ← connectedComponent_eq hw1]
      exact mem_connectedComponent
    · rintro ⟨Z, ⟨-, hdisj⟩, hyZ⟩ hy
      exact Set.disjoint_left.mp hdisj hyZ hy
  rw [← isClosed_compl_iff, heq]
  exact (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion fun Z hZ =>
    isClosed_of_mem_irreducibleComponents Z hZ.1

/-- **LEAF (Stacks, Varieties, Lemma 33.7.14, Tag 04KV; UNVERIFIED locator).** A connected
scheme of finite type over a field `k` with a `k`-rational point is geometrically
connected. (Stacks states it without the finiteness hypotheses and with "a point `x` such that `k`
is algebraically closed in `κ(x)`"; a `k`-rational point is such a point, so this is a
consequence, never stronger.) -/
def GeomConnOfRationalPoint : Prop :=
  ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
    (s : Spec (CommRingCat.of k) ⟶ X), s ≫ f = 𝟙 _ → LocallyOfFiniteType f → QuasiCompact f →
    ConnectedSpace X → GeometricallyConnected f

/-- **LEAF (group schemes are equidimensional; Stacks, Groupoids, Lemma 39.8.? "`G` is
equidimensional and `dim G = dim_g G`" (UNVERIFIED locator); SGA 3, Exp. VI_A, 2.4; Milne,
*Algebraic Groups* (2017), Prop. 1.37? (UNVERIFIED)).** For a group scheme `G` of finite type over
a field, every irreducible component of `G` has the dimension of `G` (Krull dimensions of the
underlying spaces; a component with its subspace topology). A consequence of the published
statement (restricted to finite type), never stronger. -/
def GroupSchemeEquidim : Prop :=
  ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G],
    LocallyOfFiniteType G.hom → QuasiCompact G.hom →
    ∀ Z ∈ irreducibleComponents G.left, topologicalKrullDim Z = topologicalKrullDim G.left

/-- **LEAF: Cartier's theorem** (copy of `CartierSmooth` in `scratch/av-glue/ImageFact.lean`). -/
def CartierSmooth' : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G],
    LocallyOfFiniteType G.hom → Smooth G.hom

section IdComp

variable {k : Type} [Field k] {A B : _root_.PkgI3.AbVar k} (h : A.X ⟶ B.X) [IsMonHom h]

noncomputable def kerMul : kerOver h ⊗ kerOver h ⟶ kerOver h :=
  kerLift h (fst _ _ ≫ kerι h * snd _ _ ≫ kerι h) (by
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, kerι_comp, MonObj.comp_one,
      MonObj.comp_one, _root_.mul_one])

lemma kerMul_ι : kerMul h ≫ kerι h = fst _ _ ≫ kerι h * snd _ _ ≫ kerι h := by
  rw [kerMul, kerLift_ι]

noncomputable def kerOne : 𝟙_ _ ⟶ kerOver h :=
  kerLift h η[A.X] (by
    rw [IsMonHom.one_hom, Hom.one_def, show toUnit (𝟙_ (Over (Spec (CommRingCat.of k)))) = 𝟙 _
      from toUnit_unique _ _, Category.id_comp])

lemma kerOne_ι : kerOne h ≫ kerι h = η[A.X] := by rw [kerOne, kerLift_ι]

noncomputable def kerInv : kerOver h ⟶ kerOver h :=
  kerLift h (kerι h)⁻¹ (by rw [GrpObj.inv_comp, kerι_comp, inv_one])

lemma kerInv_ι : kerInv h ≫ kerι h = (kerι h)⁻¹ := by rw [kerInv, kerLift_ι]

/-- The group structure of the kernel. -/
noncomputable instance kerGrp : GrpObj (kerOver h) :=
  grpObjOfMono (kerι h) (kerMul h) (kerMul_ι h) (kerOne h) (kerOne_ι h) (kerInv h) (kerInv_ι h)

instance isMonHom_kerι : IsMonHom (kerι h) :=
  isMonHom_grpObjOfMono (kerι h) (kerMul h) (kerMul_ι h) (kerOne h) (kerOne_ι h) (kerInv h)
    (kerInv_ι h)

instance : IsClosedImmersion (η[B.X]).left := by
  have : IsClosedImmersion ((η[B.X]).left ≫ B.X.hom) := by
    rw [Over.w]; dsimp; infer_instance
  exact IsClosedImmersion.of_comp _ B.X.hom

instance : IsClosedImmersion (kerι h).left :=
  inferInstanceAs (IsClosedImmersion (pullback.fst h.left (η[B.X]).left))

instance : IsProper (kerOver h).hom := by
  dsimp only [kerOver, Over.mk_hom]; infer_instance

instance : IsLocallyNoetherian (kerOver h).left :=
  LocallyOfFiniteType.isLocallyNoetherian (kerOver h).hom

instance : CompactSpace (kerOver h).left :=
  QuasiCompact.compactSpace_of_compactSpace (kerOver h).hom

instance : IsNoetherian (kerOver h).left := {}

instance subsingleton_unit_left : Subsingleton (𝟙_ (Over (Spec (CommRingCat.of k)))).left :=
  (inferInstance : Subsingleton (Spec (CommRingCat.of k)))

/-- The unit point of the kernel. -/
noncomputable def ePt : (kerOver h).left :=
  (η[kerOver h]).left (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of k))))

/-- The identity component `(ker h)⁰` as an open subscheme. -/
noncomputable def U0 : (kerOver h).left.Opens :=
  ⟨connectedComponent (ePt h), isOpen_connectedComponent_of_noetherian _⟩

/-- `(ker h)⁰` as a `k`-scheme. -/
noncomputable abbrev covOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk ((U0 h).ι ≫ (kerOver h).hom)

noncomputable def jK : covOver h ⟶ kerOver h := Over.homMk (U0 h).ι rfl

instance : Mono (jK h) := by
  haveI : Mono (jK h).left := (inferInstance : Mono (U0 h).ι)
  exact Over.mono_of_mono_left _

instance : IsClosedImmersion (jK h).left := by
  change IsClosedImmersion (U0 h).ι
  exact IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)

instance : ConnectedSpace (covOver h).left := by
  change ConnectedSpace (connectedComponent (ePt h))
  exact isConnected_iff_connectedSpace.mp isConnected_connectedComponent

/-- Lift a map into the kernel whose range lies in `(ker h)⁰`. -/
noncomputable def liftCov {W : Over (Spec (CommRingCat.of k))} (g : W ⟶ kerOver h)
    (hg : Set.range g.left ⊆ connectedComponent (ePt h)) : W ⟶ covOver h :=
  Over.homMk (IsOpenImmersion.lift (U0 h).ι g.left (by rw [Scheme.Opens.range_ι]; exact hg))
    (by
      change IsOpenImmersion.lift _ _ _ ≫ (U0 h).ι ≫ (kerOver h).hom = W.hom
      rw [IsOpenImmersion.lift_fac_assoc]; exact Over.w g)

@[reassoc (attr := simp)]
lemma liftCov_jK {W : Over (Spec (CommRingCat.of k))} (g : W ⟶ kerOver h)
    (hg : Set.range g.left ⊆ connectedComponent (ePt h)) : liftCov h g hg ≫ jK h = g := by
  ext1; simp [liftCov, jK]

lemma range_sub {W : Over (Spec (CommRingCat.of k))} [ConnectedSpace W.left]
    (g : W ⟶ kerOver h) (w0 : W.left) (hw0 : g.left w0 = ePt h) :
    Set.range g.left ⊆ connectedComponent (ePt h) :=
  (isPreconnected_range g.left.continuous).subset_connectedComponent ⟨w0, hw0⟩

lemma eta_left_apply {W : Over (Spec (CommRingCat.of k))} (u : 𝟙_ _ ⟶ W) (g : W ⟶ kerOver h)
    (hu : u ≫ g = η[kerOver h]) (p : Spec (CommRingCat.of k)) : g.left (u.left p) = ePt h := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hu, ePt]
  congr 1
  exact Subsingleton.elim _ _

/-- The unit of `(ker h)⁰`. -/
noncomputable def oneCov : 𝟙_ _ ⟶ covOver h :=
  liftCov h η[kerOver h] (by
    rintro _ ⟨p, rfl⟩
    rw [show (η[kerOver h]).left p = ePt h by
      rw [ePt]; congr 1; exact Subsingleton.elim _ _]
    exact mem_connectedComponent)

lemma oneCov_jK : oneCov h ≫ jK h = η[kerOver h] := liftCov_jK _ _ _

variable (hG : GeomConnOfRationalPoint) (hC : CartierSmooth')

include hG in
theorem geomConn_cov : GeometricallyConnected (covOver h).hom := by
  refine hG k (covOver h).left (covOver h).hom (oneCov h).left (Over.w (oneCov h)) ?_ ?_
    inferInstance
  · change LocallyOfFiniteType ((U0 h).ι ≫ (kerOver h).hom); infer_instance
  · change QuasiCompact ((U0 h).ι ≫ (kerOver h).hom); infer_instance

lemma one_eq_eta : (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ kerOver h) = η[kerOver h] := by
  rw [Hom.one_def, show toUnit (𝟙_ (Over (Spec (CommRingCat.of k)))) = 𝟙 _
    from toUnit_unique _ _, Category.id_comp]

include hG in
theorem exists_mulCov : ∃ m : covOver h ⊗ covOver h ⟶ covOver h,
    m ≫ jK h = fst _ _ ≫ jK h * snd _ _ ≫ jK h := by
  haveI := geomConn_cov h hG
  haveI : ConnectedSpace (covOver h ⊗ covOver h).left :=
    (inferInstance : ConnectedSpace (pullback (C := Scheme.{0}) (covOver h).hom (covOver h).hom))
  refine ⟨liftCov h _ (range_sub h _ ((lift (oneCov h) (oneCov h)).left
    (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of k))))) ?_), liftCov_jK _ _ _⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, MonObj.comp_mul, ← Category.assoc,
    ← Category.assoc, lift_fst, lift_snd, oneCov_jK, ← one_eq_eta, _root_.mul_one, one_eq_eta, ePt]

theorem exists_invCov : ∃ v : covOver h ⟶ covOver h, v ≫ jK h = (jK h)⁻¹ := by
  refine ⟨liftCov h _ (range_sub h _ ((oneCov h).left
    (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of k))))) ?_), liftCov_jK _ _ _⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, GrpObj.comp_inv, oneCov_jK, ← one_eq_eta,
    inv_one, one_eq_eta, ePt]

/-- The group structure of `(ker h)⁰`. -/
noncomputable abbrev covGrp : GrpObj (covOver h) :=
  grpObjOfMono (jK h) (exists_mulCov h hG).choose (exists_mulCov h hG).choose_spec
    (oneCov h) (oneCov_jK h) (exists_invCov h).choose (exists_invCov h).choose_spec

end IdComp

/-- **LEAF (`(ker h)⁰_red` is an abelian subvariety, kernel form).** Over a field of
characteristic `0`, let `h : A → B` be a homomorphism of abelian varieties and
`ker h = A ×_B Spec k` its kernel (Mathlib's fibre product of `h` with the identity section of
`B`). If `ker h` is not locally quasi-finite over `k` (i.e. `ker h` is positive-dimensional),
there is an abelian variety `C` with a homomorphism `j : C → A` that is a closed immersion,
`0 < dim C`, and `h ∘ j = 0`: take `C = (ker h)⁰_red`. Sources (UNVERIFIED locators): Milne,
*Abelian varieties* (Cornell-Silverman 1986), §8; Milne's notes (2008) I §8; Mumford §8; reduced
group schemes over a perfect field are smooth, and in characteristic `0` every group scheme of
finite type is reduced (Cartier; Mumford §11 Thm 1); `dim (ker h)⁰ = dim ker h` (a group scheme of
finite type over a field is equidimensional). A consequence of these, never stronger. -/
def KernelIdentityComponent : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A B : _root_.PkgI3.AbVar k)
    (h : _root_.PkgI3.AbVar.Hom A B),
    ¬ LocallyQuasiFinite (pullback.fst h.hom.left (η[B.X]).left ≫ A.X.hom) →
    ∃ (C : _root_.PkgI3.AbVar k) (j : _root_.PkgI3.AbVar.Hom C A),
      IsClosedImmersion j.hom.left ∧ 0 < C.dim ∧ j.hom ≫ h.hom = 1

/-- A homomorphism of abelian varieties is proper. -/
theorem isProper_hom'' {k : Type} [Field k] {A B : _root_.PkgI3.AbVar k} (h : A.X ⟶ B.X) :
    IsProper h.left := by
  have : IsProper (h.left ≫ B.X.hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp h.left B.X.hom

/-- **`KernelAbSubvariety` from `KernelIdentityComponent`** (glue: the shear isomorphism). -/
theorem kernelAbSubvariety_of_identityComponent (hK1 : KernelIdentityComponent) :
    KernelAbSubvariety := by
  intro k _ _ A B h hnot
  refine hK1 k A B h fun hq => hnot ?_
  haveI := isProper_hom'' h.hom
  exact lqf_of_ker h.hom hq


section IdCompFinal

variable {k : Type} [Field k] {A B : _root_.PkgI3.AbVar k} (h : A.X ⟶ B.X) [IsMonHom h]
  (hG : GeomConnOfRationalPoint) (hC : CartierSmooth')

instance : IsClosedImmersion (U0 h).ι := inferInstanceAs (IsClosedImmersion (jK h).left)

include hC in
theorem smooth_ker [CharZero k] : Smooth (kerOver h).hom := hC k (kerOver h) inferInstance

/-- `(ker h)⁰` as an abelian variety. -/
noncomputable abbrev covAbVar [CharZero k] : _root_.PkgI3.AbVar k :=
  letI := covGrp h hG
  haveI : IsProper (covOver h).hom := by
    change IsProper ((U0 h).ι ≫ (kerOver h).hom); infer_instance
  haveI : Smooth (kerOver h).hom := smooth_ker h hC
  haveI : Smooth (covOver h).hom := by
    change Smooth ((U0 h).ι ≫ (kerOver h).hom); infer_instance
  haveI : GeometricallyConnected (covOver h).hom := geomConn_cov h hG
  haveI : GeometricallyIntegral (covOver h).hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral _
  { X := covOver h }

theorem isMonHom_jK : letI := covGrp h hG; IsMonHom (jK h) :=
  isMonHom_grpObjOfMono (jK h) (exists_mulCov h hG).choose (exists_mulCov h hG).choose_spec
    (oneCov h) (oneCov_jK h) (exists_invCov h).choose (exists_invCov h).choose_spec

/-- If the kernel is not locally quasi-finite, it is positive-dimensional. -/
theorem dim_ker_pos (hnot : ¬ LocallyQuasiFinite (kerOver h).hom) :
    0 < topologicalKrullDim (kerOver h).left := by
  by_contra h0
  apply hnot
  haveI : IsLocallyArtinian (kerOver h).left :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero (not_lt.mp h0)
  haveI : Finite (kerOver h).left :=
    Finite.of_finite_univ (isCompact_univ.finite_of_discrete)
  exact LocallyQuasiFinite.of_finite_preimage_singleton _ fun _ => Set.toFinite _

end IdCompFinal

/-- **`KernelIdentityComponent` from three published theorems**: Cartier, Stacks 04KV
(geometric connectedness from a rational point), equidimensionality of group schemes. -/
theorem kernelIdentityComponent_of_leaves (hC : CartierSmooth') (hG : GeomConnOfRationalPoint)
    (hE : GroupSchemeEquidim) : KernelIdentityComponent := by
  intro k _ _ A B h hnot
  letI := covGrp h.hom hG
  haveI := isMonHom_jK h.hom hG
  refine ⟨covAbVar h.hom hG hC,
    _root_.PkgI3.AbVar.Hom.mk' (A := covAbVar h.hom hG hC) (jK h.hom ≫ kerι h.hom), ?_, ?_, ?_⟩
  · rw [_root_.PkgI3.AbVar.Hom.hom_mk', Over.comp_left]; infer_instance
  · -- positivity of the dimension
    have hpos := dim_ker_pos h.hom hnot
    obtain ⟨Z, hZ, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      {ePt h.hom} isIrreducible_singleton
    have hZU : Z ⊆ connectedComponent (ePt h.hom) :=
      hZ.1.isConnected.isPreconnected.subset_connectedComponent (hsub rfl)
    have hEq := hE k (kerOver h.hom) inferInstance inferInstance Z hZ
    have hle : topologicalKrullDim Z ≤ topologicalKrullDim (connectedComponent (ePt h.hom)) :=
      (Topology.IsEmbedding.inclusion hZU).isInducing.topologicalKrullDim_le
    change 0 < topologicalKrullDim (connectedComponent (ePt h.hom))
    exact lt_of_lt_of_le (hEq ▸ hpos) hle
  · rw [_root_.PkgI3.AbVar.Hom.hom_mk', Category.assoc, kerι_comp, MonObj.comp_one]

end AVGlue


namespace AVGlue

/-- (verbatim copy of `ZInQ.Contrib.AVB1.SimpleImageIsogeny`, `ZInQKernel/Contrib/AVB1/Poincare.lean`)
**A nonzero homomorphism out of a simple abelian variety is an isogeny onto its image**
(textbook; the two glue Props `ImageFactorization` and `SimpleSurjIsogeny` together, see
`simpleImageIsogeny_of_pieces`). Over a field of characteristic `0`, if `End⁰(A)` is a division
algebra and `f : A → J` is a nonzero homomorphism, then `f = i ∘ h` with `h : A → B` an isogeny
(finite and surjective) and `i : B → J` a homomorphism that is a closed immersion. Sources
(UNVERIFIED locators): Mumford, *Abelian varieties*, §19 (simple abelian varieties: a nonzero
homomorphism from a simple `A` has finite kernel) with the image of a homomorphism being an
abelian subvariety (Milne 1986 §8); same ingredients as the two glue Props. -/
def SimpleImageIsogeny : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A J : _root_.PkgI3.AbVar k), _root_.PkgI3.EndDivision A →
    ∀ f : _root_.PkgI3.AbVar.Hom A J, f ≠ 0 →
    ∃ (B : _root_.PkgI3.AbVar k) (h : _root_.PkgI3.AbVar.Hom A B)
      (i : _root_.PkgI3.AbVar.Hom B J),
      _root_.PkgI3.AbVar.IsIsogenyMor h.hom ∧ IsClosedImmersion i.hom.left ∧ f.hom = h.hom ≫ i.hom

theorem simpleImageIsogeny_iff : SimpleImageIsogeny ↔ ZInQ.Contrib.AVB1.SimpleImageIsogeny :=
  Iff.rfl

/-- **`SimpleImageIsogeny` (the glue field of the canonical H assembly) from four leaves.** -/
theorem simpleImageIsogeny_of_leaves (hC : CartierSmooth)
    (hP : ZInQ.Contrib.AVB1.PoincareComplement) (hQ : IsogenyQuasiInverse)
    (hK : KernelAbSubvariety) : SimpleImageIsogeny :=
  ZInQ.Contrib.AVB1.simpleImageIsogeny_of_pieces (imageFactorization_of_cartier hC)
    (simpleSurjIsogeny_of_leaves hP hQ hK)

/-- **T8 (`PkgI3.PoincareReducibility`) from the same four leaves.** -/
theorem poincareReducibility_of_leaves (hC : CartierSmooth)
    (hP : ZInQ.Contrib.AVB1.PoincareComplement) (hQ : IsogenyQuasiInverse)
    (hK : KernelAbSubvariety) : _root_.PkgI3.PoincareReducibility :=
  ZInQ.Contrib.AVB1.poincareReducibility_of_pieces hP (imageFactorization_of_cartier hC)
    (simpleSurjIsogeny_of_leaves hP hQ hK)

theorem cartierSmooth_iff : CartierSmooth ↔ CartierSmooth' := Iff.rfl

/-- **`SimpleImageIsogeny` from five published theorems** (Cartier; Poincaré's complement;
quasi-inverse of an isogeny; Stacks 04KV; equidimensionality of group schemes). -/
theorem simpleImageIsogeny_of_published (hC : CartierSmooth)
    (hP : ZInQ.Contrib.AVB1.PoincareComplement) (hQ : IsogenyQuasiInverse)
    (hG : GeomConnOfRationalPoint) (hE : GroupSchemeEquidim) : SimpleImageIsogeny :=
  simpleImageIsogeny_of_leaves hC hP hQ
    (kernelAbSubvariety_of_identityComponent (kernelIdentityComponent_of_leaves hC hG hE))

/-- **`SimpleSurjIsogeny` from four published theorems.** -/
theorem simpleSurjIsogeny_of_published (hC : CartierSmooth)
    (hP : ZInQ.Contrib.AVB1.PoincareComplement) (hQ : IsogenyQuasiInverse)
    (hG : GeomConnOfRationalPoint) (hE : GroupSchemeEquidim) : SimpleSurjIsogeny :=
  simpleSurjIsogeny_of_leaves hP hQ
    (kernelAbSubvariety_of_identityComponent (kernelIdentityComponent_of_leaves hC hG hE))

/-- **T8 (`PkgI3.PoincareReducibility`) from the same five published theorems.** -/
theorem poincareReducibility_of_published (hC : CartierSmooth)
    (hP : ZInQ.Contrib.AVB1.PoincareComplement) (hQ : IsogenyQuasiInverse)
    (hG : GeomConnOfRationalPoint) (hE : GroupSchemeEquidim) :
    _root_.PkgI3.PoincareReducibility :=
  ZInQ.Contrib.AVB1.poincareReducibility_of_simpleImage hP
    (simpleImageIsogeny_of_published hC hP hQ hG hE)

/-- **`SimpleImageIsogeny` from four new-or-existing published leaves, quasi-inverse on points**:
Cartier, Poincaré's complement (existing field), the `K̄`-point quasi-inverse (existing field
`isogenyQuasiInverse`), Stacks 04KV, equidimensionality. -/
theorem simpleImageIsogeny_of_published' (hC : CartierSmooth)
    (hP : ZInQ.Contrib.AVB1.PoincareComplement) (hQ : WeilPairing.IsogenyQuasiInverse)
    (hG : GeomConnOfRationalPoint) (hE : GroupSchemeEquidim) : SimpleImageIsogeny :=
  ZInQ.Contrib.AVB1.simpleImageIsogeny_of_pieces (imageFactorization_of_cartier hC)
    (simpleSurjIsogeny_of_leaves' hP hQ
      (kernelAbSubvariety_of_identityComponent (kernelIdentityComponent_of_leaves hC hG hE)))

theorem simpleSurjIsogeny_of_published' (hC : CartierSmooth)
    (hP : ZInQ.Contrib.AVB1.PoincareComplement) (hQ : WeilPairing.IsogenyQuasiInverse)
    (hG : GeomConnOfRationalPoint) (hE : GroupSchemeEquidim) : SimpleSurjIsogeny :=
  simpleSurjIsogeny_of_leaves' hP hQ
    (kernelAbSubvariety_of_identityComponent (kernelIdentityComponent_of_leaves hC hG hE))

theorem poincareReducibility_of_published' (hC : CartierSmooth)
    (hP : ZInQ.Contrib.AVB1.PoincareComplement) (hQ : WeilPairing.IsogenyQuasiInverse)
    (hG : GeomConnOfRationalPoint) (hE : GroupSchemeEquidim) :
    _root_.PkgI3.PoincareReducibility :=
  ZInQ.Contrib.AVB1.poincareReducibility_of_simpleImage hP
    (simpleImageIsogeny_of_published' hC hP hQ hG hE)

end AVGlue
