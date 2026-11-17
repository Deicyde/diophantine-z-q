import ZInQKernel.Contrib.OneProof.PicDictionary
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Descent

/-! # pic-dict: `PicZeroPtsTranslInv` from two printed leaves (rigidity on `A × Pic⁰`) -/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory Limits
open scoped CategoryTheory.MonObj

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing

variable {K : Type} [Field K]

/-- **LEAF (`𝒪_T = f_{T*}𝒪_{A_T}` universally).** For an abelian variety `A` over `K` (proper, flat, with
geometrically integral fibre) and every `K`-scheme `T`, the unit `𝒪_T → (A_T → T)_* 𝒪_{A_T}` is an isomorphism.
EGA III 7.8.6 (cohomology and base change in degree 0); Kleiman, *The Picard scheme*, Ex. 9.3.11 (`𝒪_S = f_*𝒪_X`
holds universally for `f` proper flat with geometrically integral fibres); over a field also flat base change
(Stacks 02KH) with `Γ(A, 𝒪) = K`. Locators UNVERIFIED. -/
def PushforwardUnitUniversal : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (T : Over (Spec (CommRingCat.of K))),
    IsIso (pushforwardUnitMap (pullback.snd A.X.hom T.hom))

/-- **LEAF (products of geometrically integral schemes).** If `X` and `Y` are geometrically integral over a field
`K`, so is `X ×_K Y`. EGA IV 4.6.5 / Stacks, *Varieties*, products of geometrically irreducible and geometrically
reduced schemes (locators UNVERIFIED). Instance for two abelian varieties. -/
def GeomIntegralProd : Prop :=
  ∀ (K : Type) [Field K] (A B : AbVar K), GeometricallyIntegral (A.X ⊗ B.X).hom

section Setup

variable (A : AbVar K)

/-- The zero section `Spec K → A`. -/
abbrev zs : Spec (CommRingCat.of K) ⟶ A.X.left := η[A.X].left

lemma zs_comp : zs A ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]

/-- Translation by a `T`-point `a` on `A ×_K T`. -/
def translT {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) : A.X ⊗ T ⟶ A.X ⊗ T :=
  CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst _ _)
      (CartesianMonoidalCategory.snd _ _ ≫ a) ≫ μ[A.X])
    (CartesianMonoidalCategory.snd _ _)

/-- `t_a` on the scheme `A ×_K T`. -/
abbrev trT {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) :
    pullback A.X.hom T.hom ⟶ pullback A.X.hom T.hom := (translT A a).left

/-- The normalized subfunctor (classes trivial along the zero section). -/
abbrev Nrm : Subfunctor (picardPresheaf A.X.hom) := picardFunctorNormalized A.X.hom (zs A) (zs_comp A)

/-- Kleiman 9.2.5, proved in the vendored library: normalized classes ≅ the Picard sheaf. -/
def Θ (hU : PushforwardUnitUniversal) : (Nrm A).toFunctor ≅ (picardFunctor A.X.hom).obj :=
  picardFunctorNormalizedIso A.X.hom (zs A) (zs_comp A) (hU K A)

lemma Θ_hom_app (hU : PushforwardUnitUniversal) (T) (x) :
    (Θ A hU).hom.app T x = (toPicardFunctor A.X.hom).app T x.1 := rfl

/-- The `T`-section of `A_T` along `0`. -/
abbrev zT (T : Over (Spec (CommRingCat.of K))) : T.left ⟶ pullback A.X.hom T.hom :=
  sectionBaseChange A.X.hom (zs A) (zs_comp A) T

/-- `t_a^*c ⊗ (pr^* 0^* t_a^* c)⁻¹ ⊗ c⁻¹`, the renormalized `φ_c(a)`. -/
def dT {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) (c : (pullback A.X.hom T.hom).Pic) :
    (pullback A.X.hom T.hom).Pic :=
  Scheme.Pic.map (trT A a) c *
    (Scheme.Pic.map (pullback.snd A.X.hom T.hom) (Scheme.Pic.map (zT A T)
      (Scheme.Pic.map (trT A a) c)))⁻¹ * c⁻¹

lemma dT_mem {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) (c : (pullback A.X.hom T.hom).Pic)
    (hc : Scheme.Pic.map (zT A T) c = 1) : Scheme.Pic.map (zT A T) (dT A a c) = 1 := by
  have h1 : Scheme.Pic.map (zT A T) (Scheme.Pic.map (pullback.snd A.X.hom T.hom)
      (Scheme.Pic.map (zT A T) (Scheme.Pic.map (trT A a) c))) =
      Scheme.Pic.map (zT A T) (Scheme.Pic.map (trT A a) c) := by
    rw [← Scheme.Pic.map_comp, sectionBaseChange_snd, Scheme.Pic.map_id]
  rw [dT, ← Scheme.Pic.mapHom_apply, map_mul, map_mul, map_inv, map_inv]
  simp only [Scheme.Pic.mapHom_apply]
  rw [h1, hc]
  group

lemma bcm_eq {T T' : Over (Spec (CommRingCat.of K))} (g : T' ⟶ T) :
    JacobianChallenge.baseChangeMap A.X.hom g = (A.X ◁ g).left := by
  apply pullback.hom_ext <;> simp [JacobianChallenge.baseChangeMap]

lemma translT_whisker {T T' : Over (Spec (CommRingCat.of K))} (g : T' ⟶ T) (a : T ⟶ A.X) :
    (A.X ◁ g) ≫ translT A a = translT A (g ≫ a) ≫ (A.X ◁ g) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT, CartesianMonoidalCategory.comp_lift_assoc]
  · simp [translT]

lemma dT_natural {T T' : Over (Spec (CommRingCat.of K))} (g : T' ⟶ T) (a : T ⟶ A.X)
    (c : (pullback A.X.hom T.hom).Pic) :
    Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom g) (dT A a c) =
      dT A (g ≫ a) (Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom g) c) := by
  have n1 : JacobianChallenge.baseChangeMap A.X.hom g ≫ trT A a =
      trT A (g ≫ a) ≫ JacobianChallenge.baseChangeMap A.X.hom g := by
    rw [bcm_eq, ← Over.comp_left, ← Over.comp_left, translT_whisker]
  have n2 : JacobianChallenge.baseChangeMap A.X.hom g ≫ pullback.snd A.X.hom T.hom =
      pullback.snd A.X.hom T'.hom ≫ g.left := pullback.lift_snd _ _ _
  have n3 : zT A T' ≫ JacobianChallenge.baseChangeMap A.X.hom g = g.left ≫ zT A T :=
    sectionBaseChange_comp_baseChangeMap _ _ _ g
  rw [dT, dT, ← Scheme.Pic.mapHom_apply, map_mul, map_mul, map_inv, map_inv]
  simp only [Scheme.Pic.mapHom_apply]
  rw [← Scheme.Pic.map_comp, n1, Scheme.Pic.map_comp, ← Scheme.Pic.map_comp _ (pullback.snd _ _), n2,
    Scheme.Pic.map_comp, ← Scheme.Pic.map_comp g.left, ← n3, Scheme.Pic.map_comp,
    ← Scheme.Pic.map_comp _ (trT A a), n1, Scheme.Pic.map_comp]

end Setup

section Psi

variable {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
  (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (hU : PushforwardUnitUniversal)

/-- The morphism classifying the renormalized `φ_c(a)`. -/
def PsiT {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) (c : (Nrm A).toFunctor.obj (op T)) :
    T ⟶ P :=
  rep.homEquiv.symm ((Θ A hU).hom.app (op T) ⟨dT A a c.1, dT_mem A a c.1 c.2⟩)

lemma PsiT_natural {T T' : Over (Spec (CommRingCat.of K))} (g : T' ⟶ T) (a : T ⟶ A.X)
    (c : (Nrm A).toFunctor.obj (op T)) :
    g ≫ PsiT rep hU a c = PsiT rep hU (g ≫ a) ((Nrm A).toFunctor.map g.op c) := by
  rw [PsiT, PsiT, rep.comp_homEquiv_symm]
  congr 1
  rw [← NatTrans.naturality_apply]
  congr 1
  apply Subtype.ext
  exact dT_natural A g a c.1

/-- `η ≫ (classifying map of 1)`: the class `1` classifies the unit. -/
lemma homEquiv_symm_one {T : Over (Spec (CommRingCat.of K))} :
    letI := picardFunctorCommGrpObj A.X.hom rep
    rep.homEquiv.symm ((toPicardFunctor A.X.hom).app (op T) (1 : (pullback A.X.hom T.hom).Pic)) =
      CartesianMonoidalCategory.toUnit T ≫ η[P] := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  have h := (picardClassifyingHom A.X.hom rep T).map_one
  rw [picardClassifyingHom_apply] at h
  exact h

lemma dT_one {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) : dT A a 1 = 1 := by
  simp [dT, Scheme.Pic.map_one]

lemma translT_zero {T : Over (Spec (CommRingCat.of K))} :
    translT A (CartesianMonoidalCategory.toUnit T ≫ η[A.X]) = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [translT, CartesianMonoidalCategory.lift_fst, Category.id_comp]
    rw [← Category.assoc, CartesianMonoidalCategory.toUnit_unique (CartesianMonoidalCategory.snd A.X T ≫
        CartesianMonoidalCategory.toUnit T) (CartesianMonoidalCategory.toUnit _),
      ← CategoryTheory.Hom.one_def, ← CategoryTheory.Hom.mul_def, mul_one]
  · simp [translT]

lemma Θ_inj {T : Over (Spec (CommRingCat.of K))} {x y : (Nrm A).toFunctor.obj (op T)}
    (h : (Θ A hU).hom.app (op T) x = (Θ A hU).hom.app (op T) y) : x = y := by
  have := congrArg ((Θ A hU).inv.app (op T)) h
  simpa using this

/-- `PsiT a c = 1` when `dT a c = 1`. -/
lemma PsiT_eq_one {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) (c : (Nrm A).toFunctor.obj (op T))
    (h : dT A a c.1 = 1) :
    letI := picardFunctorCommGrpObj A.X.hom rep
    PsiT rep hU a c = CartesianMonoidalCategory.toUnit T ≫ η[P] := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  rw [PsiT, ← homEquiv_symm_one rep]
  congr 1
  rw [Θ_hom_app]
  exact congrArg _ h

/-- Conversely, `PsiT a c = 1` forces `dT a c = 1`. -/
lemma dT_eq_one_of_PsiT {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X)
    (c : (Nrm A).toFunctor.obj (op T))
    (h : letI := picardFunctorCommGrpObj A.X.hom rep
      PsiT rep hU a c = CartesianMonoidalCategory.toUnit T ≫ η[P]) : dT A a c.1 = 1 := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  rw [PsiT, ← homEquiv_symm_one rep] at h
  have h2 := rep.homEquiv.symm.injective h
  have h3 : (1 : (pullback A.X.hom T.hom).Pic) ∈ (Nrm A).obj (op T) := by
    change Scheme.Pic.map _ 1 = 1; exact Scheme.Pic.map_one _
  have h4 := Θ_inj hU (x := ⟨dT A a c.1, dT_mem A a c.1 c.2⟩) (y := ⟨(1 : (pullback A.X.hom T.hom).Pic), h3⟩) (by rw [h2]; rfl)
  exact congrArg Subtype.val h4

end Psi

lemma dT_zero {A : AbVar K} {T : Over (Spec (CommRingCat.of K))} (c : (pullback A.X.hom T.hom).Pic)
    (hc : Scheme.Pic.map (zT A T) c = 1) : dT A (CartesianMonoidalCategory.toUnit T ≫ η[A.X]) c = 1 := by
  have e : trT A (CartesianMonoidalCategory.toUnit T ≫ η[A.X]) = 𝟙 _ := by
    rw [trT, translT_zero]; rfl
  rw [dT, e, Scheme.Pic.map_id, hc, Scheme.Pic.map_one, inv_one, mul_one, mul_inv_cancel]

lemma lift_mul_lift {G H T : Over (Spec (CommRingCat.of K))} [GrpObj G] [GrpObj H] (f f' : T ⟶ G)
    (g g' : T ⟶ H) :
    CartesianMonoidalCategory.lift f g * CartesianMonoidalCategory.lift f' g' =
      CartesianMonoidalCategory.lift (f * f') (g * g') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.mul_comp]; simp
  · rw [MonObj.mul_comp]; simp

/-- **`PicZeroPtsTranslInv` from two printed leaves** (rigidity on `A × Pic⁰`). -/
theorem picZeroPtsTranslInv_of_leaves (hU : PushforwardUnitUniversal) (hGI : GeomIntegralProd) :
    PicZeroPtsTranslInv := by
  intro K _ A P rep B j hj y x
  letI := picardFunctorCommGrpObj A.X.hom rep
  obtain ⟨hopen, hrange, hmon⟩ := hj
  haveI : IsOpenImmersion j.left := hopen
  haveI : IsMonHom j := hmon
  haveI : GeometricallyIntegral (A.X ⊗ B.X).hom := hGI K A B
  haveI : IsProper (A.X ⊗ B.X).hom := by dsimp; infer_instance
  let c₀ : (Nrm A).toFunctor.obj (op (A.X ⊗ B.X)) :=
    (Θ A hU).inv.app (op (A.X ⊗ B.X)) (rep.homEquiv (CartesianMonoidalCategory.snd A.X B.X ≫ j))
  let Ψ := PsiT rep hU (CartesianMonoidalCategory.fst A.X B.X) c₀
  -- the class of `g ≫ snd ≫ j` along any `g`
  have hΘc : ∀ {T : Over (Spec (CommRingCat.of K))} (g : T ⟶ A.X ⊗ B.X),
      (Θ A hU).hom.app (op T) ((Nrm A).toFunctor.map g.op c₀) =
        rep.homEquiv (g ≫ CartesianMonoidalCategory.snd A.X B.X ≫ j) := by
    intro T g
    rw [NatTrans.naturality_apply, Iso.inv_hom_id_app_apply]
    exact (rep.homEquiv_comp g _).symm
  have hjη : η[B.X] ≫ j = η[P] := IsMonHom.one_hom j
  -- axis `A × {0}`
  have haxA : CartesianMonoidalCategory.lift (𝟙 A.X) (CartesianMonoidalCategory.toUnit A.X ≫ η[B.X]) ≫ Ψ =
      CartesianMonoidalCategory.toUnit A.X ≫ η[P] := by
    rw [PsiT_natural]
    apply PsiT_eq_one
    have h1 : ((Nrm A).toFunctor.map (CartesianMonoidalCategory.lift (𝟙 A.X)
        (CartesianMonoidalCategory.toUnit A.X ≫ η[B.X])).op c₀).1 =
        (1 : (pullback A.X.hom A.X.hom).Pic) := by
      have h3 : Scheme.Pic.map (zT A A.X) (1 : (pullback A.X.hom A.X.hom).Pic) = 1 :=
        Scheme.Pic.map_one _
      have := Θ_inj hU (x := (Nrm A).toFunctor.map (CartesianMonoidalCategory.lift (𝟙 A.X)
        (CartesianMonoidalCategory.toUnit A.X ≫ η[B.X])).op c₀)
        (y := ⟨(1 : (pullback A.X.hom A.X.hom).Pic), h3⟩) (by
          rw [hΘc, Θ_hom_app]
          simp only [CartesianMonoidalCategory.lift_snd_assoc, Category.assoc, hjη]
          rw [← homEquiv_symm_one rep, Equiv.apply_symm_apply])
      exact congrArg Subtype.val this
    rw [h1]; exact dT_one _
  -- axis `{0} × B`
  have haxB : CartesianMonoidalCategory.lift (CartesianMonoidalCategory.toUnit B.X ≫ η[A.X]) (𝟙 B.X) ≫ Ψ =
      CartesianMonoidalCategory.toUnit B.X ≫ η[P] := by
    rw [PsiT_natural]
    apply PsiT_eq_one
    set c := (Nrm A).toFunctor.map (CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.toUnit B.X ≫ η[A.X]) (𝟙 B.X)).op c₀
    have hc : Scheme.Pic.map (zT A B.X) c.1 = 1 := c.2
    rw [CartesianMonoidalCategory.lift_fst]
    exact dT_zero c.1 hc
  -- `Ψ(0) = 0`
  have hηAB : η[A.X ⊗ B.X] = η[A.X] ≫ CartesianMonoidalCategory.lift (𝟙 A.X)
      (CartesianMonoidalCategory.toUnit A.X ≫ η[B.X]) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [IsMonHom.one_hom (CartesianMonoidalCategory.fst A.X B.X)]; simp
    · rw [IsMonHom.one_hom (CartesianMonoidalCategory.snd A.X B.X)]
      simp only [Category.assoc, CartesianMonoidalCategory.lift_snd]
      rw [← Category.assoc, CartesianMonoidalCategory.toUnit_unique (η[A.X] ≫ _) (𝟙 _),
        Category.id_comp]
  have hη : η[A.X ⊗ B.X] ≫ Ψ = η[P] := by
    rw [hηAB, Category.assoc, haxA, ← Category.assoc,
      CartesianMonoidalCategory.toUnit_unique (η[A.X] ≫ _) (𝟙 _), Category.id_comp]
  -- `Ψ` factors through `Pic⁰ = B`
  haveI : IsIntegral (A.X ⊗ B.X).left := GeometricallyIntegral.isIntegral_of_subsingleton (A.X ⊗ B.X).hom
  have hsub : Set.range Ψ.left ⊆ Set.range j.left := by
    rw [hrange]
    rintro _ ⟨a, rfl⟩
    refine ⟨(A.X ⊗ B.X).hom a, ?_⟩
    have he : η[P].left ((A.X ⊗ B.X).hom a) = Ψ.left (η[A.X ⊗ B.X].left ((A.X ⊗ B.X).hom a)) := by
      rw [← hη]; rfl
    rw [he]
    exact (isPreconnected_range Ψ.left.continuous).subset_connectedComponent ⟨_, rfl⟩ ⟨a, rfl⟩
  let l : (A.X ⊗ B.X).left ⟶ B.X.left := IsOpenImmersion.lift j.left Ψ.left hsub
  have hl : l ≫ j.left = Ψ.left := IsOpenImmersion.lift_fac _ _ _
  have hw : l ≫ B.X.hom = (A.X ⊗ B.X).hom := by
    rw [← Over.w j, ← Category.assoc, hl, Over.w]
  let Ψ' : A.X ⊗ B.X ⟶ B.X := Over.homMk l hw
  have hΨ' : Ψ' ≫ j = Ψ := Over.OverMorphism.ext hl
  have hjm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  have hη' : η[A.X ⊗ B.X] ≫ Ψ' = η[B.X] := by
    rw [← cancel_mono j, Category.assoc, hΨ', hη, hjη]
  haveI : IsMonHom Ψ' := MulRigidity.isMonHom_of_geometricallyIntegral (A.X ⊗ B.X) B.X Ψ' hη'
  have hA' : CartesianMonoidalCategory.lift (𝟙 A.X) (CartesianMonoidalCategory.toUnit A.X ≫ η[B.X]) ≫ Ψ' =
      CartesianMonoidalCategory.toUnit A.X ≫ η[B.X] := by
    rw [← cancel_mono j, Category.assoc, hΨ', haxA, Category.assoc, hjη]
  have hB' : CartesianMonoidalCategory.lift (CartesianMonoidalCategory.toUnit B.X ≫ η[A.X]) (𝟙 B.X) ≫ Ψ' =
      CartesianMonoidalCategory.toUnit B.X ≫ η[B.X] := by
    rw [← cancel_mono j, Category.assoc, hΨ', haxB, Category.assoc, hjη]
  -- at `K̄`-points
  have hpt : CartesianMonoidalCategory.lift x y ≫ Ψ = CartesianMonoidalCategory.toUnit _ ≫ η[P] := by
    have hxy : CartesianMonoidalCategory.lift x y =
        (x ≫ CartesianMonoidalCategory.lift (𝟙 A.X) (CartesianMonoidalCategory.toUnit A.X ≫ η[B.X])) *
        (y ≫ CartesianMonoidalCategory.lift (CartesianMonoidalCategory.toUnit B.X ≫ η[A.X]) (𝟙 B.X)) := by
      simp only [CartesianMonoidalCategory.comp_lift, Category.comp_id, lift_mul_lift]
      congr 1
      · rw [← Category.assoc, CartesianMonoidalCategory.toUnit_unique (y ≫ _) (CartesianMonoidalCategory.toUnit _),
          ← CategoryTheory.Hom.one_def, mul_one]
      · rw [← Category.assoc, CartesianMonoidalCategory.toUnit_unique (x ≫ _) (CartesianMonoidalCategory.toUnit _),
          ← CategoryTheory.Hom.one_def, one_mul]
    rw [← hΨ', ← Category.assoc, hxy, MonObj.mul_comp, Category.assoc, Category.assoc, hA', hB',
      ← Category.assoc, ← Category.assoc,
      CartesianMonoidalCategory.toUnit_unique (x ≫ _) (CartesianMonoidalCategory.toUnit _),
      CartesianMonoidalCategory.toUnit_unique (y ≫ _) (CartesianMonoidalCategory.toUnit _),
      ← CategoryTheory.Hom.one_def, mul_one, MonObj.one_comp, CategoryTheory.Hom.one_def]
  rw [PsiT_natural, CartesianMonoidalCategory.lift_fst] at hpt
  have hd := dT_eq_one_of_PsiT rep hU x _ hpt
  have hcy : ((Nrm A).toFunctor.map (CartesianMonoidalCategory.lift x y).op c₀).1 = picClass rep j y := by
    have h0 := (Θ_hom_app A hU _ ((Nrm A).toFunctor.map (CartesianMonoidalCategory.lift x y).op c₀)).symm.trans
      ((hΘc (CartesianMonoidalCategory.lift x y)).trans
        (by rw [CartesianMonoidalCategory.lift_snd_assoc]))
    exact ((picClass_eq_iff rep j y _).2 h0).symm
  rw [hcy] at hd
  have hS : Scheme.Pic.map (zT A (ptK K)) (Scheme.Pic.map (trT A x) (picClass rep j y)) = 1 :=
    Subsingleton.elim (α := (Spec (CommRingCat.of (AlgebraicClosure K))).Pic) _ _
  rw [dT, hS, Scheme.Pic.map_one, inv_one, mul_one, mul_inv_eq_one] at hd
  exact hd

end PicDict
#print axioms PicDict.picZeroPtsTranslInv_of_leaves
