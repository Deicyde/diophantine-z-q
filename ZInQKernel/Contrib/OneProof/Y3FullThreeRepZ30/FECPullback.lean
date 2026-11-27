import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FibreTransfer
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# Base change of false elliptic curves (draft)

Pullback of a false elliptic curve along `g : S' ⟶ S`, the cartesian square it sits in,
transfer of generators in both directions, pullback of sections and of `V₁(5)`-structures.
-/

attribute [local instance] FEC.grp

/-! ## 1. Generators: precomposition and the converse fibre transfer -/

theorem isGen_comp {M : ℕ} {S : Scheme.{0}} {A : FEC S} {T T' : Scheme.{0}} {P : T ⟶ A.F.left}
    (f : T' ⟶ T) (hP : IsGen M A P) : IsGen M A (f ≫ P) := by
  dsimp only [IsGen] at hP ⊢
  obtain ⟨h1, h2⟩ := hP
  refine ⟨?_, ?_⟩
  · have hw : f ≫ (Over.mk (P ≫ A.F.hom)).hom = (Over.mk ((f ≫ P) ≫ A.F.hom)).hom := by
      simp only [Over.mk_hom, Category.assoc]
    have e : (Over.homMk (U := Over.mk ((f ≫ P) ≫ A.F.hom)) (f ≫ P) rfl :
          Over.mk ((f ≫ P) ≫ A.F.hom) ⟶ A.F) =
        (Over.homMk f hw : Over.mk ((f ≫ P) ≫ A.F.hom) ⟶ Over.mk (P ≫ A.F.hom)) ≫
          (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) :=
      Over.OverMorphism.ext rfl
    rw [e, ← MonObj.comp_pow, h1, MonObj.comp_one]
  · intro k _ _ s
    have e : (s ≫ f) ≫ P ≫ A.F.hom = s ≫ (f ≫ P) ≫ A.F.hom := by simp only [Category.assoc]
    refine (isGenAt_congr A e (s ≫ f ≫ P) (by simp only [Category.assoc])
      (by simp only [Category.assoc])).1 ?_
    refine IsGenAt.of_eq ?_ (h2 k (s ≫ f))
    exact Over.OverMorphism.ext (by simp only [Over.homMk_left, Category.assoc])

section Fibre

variable {S S' : Scheme.{0}} {A : FEC S} {A' : FEC S'} {g : S' ⟶ S}
  {h : A'.F.left ⟶ A.F.left}

/-- Converse of `isGenAt_of_fibre`. -/
theorem isGenAt_of_fibreMap (hpb : IsPullback h A'.F.hom A.F.hom g)
    (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a) {M : ℕ} {k : Type} [Field k]
    {t' : Spec (CommRingCat.of k) ⟶ S'} {t : Spec (CommRingCat.of k) ⟶ S} (ht : t' ≫ g = t)
    {P' : Over.mk t' ⟶ A'.F} (hP : IsGenAt M A t (fibreMap hpb ht P')) : IsGenAt M A' t' P' := by
  dsimp only [IsGenAt] at hP ⊢
  obtain ⟨h1, h2⟩ := hP
  refine ⟨fun a => ?_, fun x' hx' => ?_⟩
  · rw [← fibreMap_eq_one_iff hpb hι ht, ← fibreMap_iota hpb hι]
    exact h1 a
  · have hx : (fibreMap hpb ht x') ^ M = 1 := by
      rw [← fibreMap_pow hpb hι, hx', fibreMap_one hpb hι]
    obtain ⟨a, ha⟩ := h2 _ hx
    exact ⟨a, fibreMap_injective hpb ht (ha.trans (fibreMap_iota hpb hι ht P' a))⟩

theorem isGen_iff_of_fibre (hpb : IsPullback h A'.F.hom A.F.hom g)
    (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a) {M : ℕ} {T : Scheme.{0}} {P' : T ⟶ A'.F.left} :
    IsGen M A' P' ↔ IsGen M A (P' ≫ h) := by
  refine ⟨isGen_of_fibre hpb hι, fun hP => ?_⟩
  dsimp only [IsGen] at hP ⊢
  obtain ⟨h1, h2⟩ := hP
  have ht : (P' ≫ A'.F.hom) ≫ g = (P' ≫ h) ≫ A.F.hom := by
    simp only [Category.assoc, hpb.w]
  have e : (Over.homMk (U := Over.mk ((P' ≫ h) ≫ A.F.hom)) (P' ≫ h) rfl :
        Over.mk ((P' ≫ h) ≫ A.F.hom) ⟶ A.F) =
      fibreMap hpb ht (Over.homMk (U := Over.mk (P' ≫ A'.F.hom)) P' rfl) :=
    Over.OverMorphism.ext (by simp only [fibreMap_left, Over.homMk_left])
  refine ⟨?_, ?_⟩
  · rw [← fibreMap_eq_one_iff hpb hι ht, fibreMap_pow hpb hι, ← e]
    exact h1
  · intro k _ _ s
    have ht' : (s ≫ P' ≫ A'.F.hom) ≫ g = s ≫ (P' ≫ h) ≫ A.F.hom := by
      simp only [Category.assoc, hpb.w]
    refine isGenAt_of_fibreMap hpb hι ht' (IsGenAt.of_eq ?_ (h2 k s))
    exact Over.OverMorphism.ext
      (by simp only [fibreMap_left, Over.homMk_left, Category.assoc])

/-- A point over `t'` and a point over `t' ≫ g` related by `h` are trivial together. -/
theorem fibreMap_homMk (hpb : IsPullback h A'.F.hom A.F.hom g) {W : Scheme.{0}}
    {t' : W ⟶ S'} (Q' : W ⟶ A'.F.left) (hQ' : Q' ≫ A'.F.hom = t') (R : W ⟶ A.F.left)
    (hR : R ≫ A.F.hom = t' ≫ g) (e : Q' ≫ h = R) :
    fibreMap hpb (rfl : t' ≫ g = t' ≫ g) (Over.homMk (U := Over.mk t') Q' hQ') =
      (Over.homMk (U := Over.mk (t' ≫ g)) R hR : Over.mk (t' ≫ g) ⟶ A.F) :=
  Over.OverMorphism.ext (by simp only [fibreMap_left, Over.homMk_left, e])

theorem homMk_eq_one_iff_of_fibre (hpb : IsPullback h A'.F.hom A.F.hom g)
    (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a) {W : Scheme.{0}} {t' : W ⟶ S'}
    (Q' : W ⟶ A'.F.left) (hQ' : Q' ≫ A'.F.hom = t') (R : W ⟶ A.F.left)
    (hR : R ≫ A.F.hom = t' ≫ g) (e : Q' ≫ h = R) :
    (Over.homMk (U := Over.mk t') Q' hQ' : Over.mk t' ⟶ A'.F) = 1 ↔
      (Over.homMk (U := Over.mk (t' ≫ g)) R hR : Over.mk (t' ≫ g) ⟶ A.F) = 1 := by
  rw [← fibreMap_homMk hpb Q' hQ' R hR e, fibreMap_eq_one_iff hpb hι]

theorem homMk_pow_eq_one_iff_of_fibre (hpb : IsPullback h A'.F.hom A.F.hom g)
    (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a) {W : Scheme.{0}} {t' : W ⟶ S'}
    (Q' : W ⟶ A'.F.left) (hQ' : Q' ≫ A'.F.hom = t') (R : W ⟶ A.F.left)
    (hR : R ≫ A.F.hom = t' ≫ g) (e : Q' ≫ h = R) (n : ℕ) :
    (Over.homMk (U := Over.mk t') Q' hQ' : Over.mk t' ⟶ A'.F) ^ n = 1 ↔
      (Over.homMk (U := Over.mk (t' ≫ g)) R hR : Over.mk (t' ≫ g) ⟶ A.F) ^ n = 1 := by
  rw [← fibreMap_eq_one_iff hpb hι (rfl : t' ≫ g = t' ≫ g)
      ((Over.homMk (U := Over.mk t') Q' hQ' : Over.mk t' ⟶ A'.F) ^ n),
    fibreMap_pow hpb hι, fibreMap_homMk hpb Q' hQ' R hR e]

end Fibre

/-! ## 2. The pulled-back family -/

section Pullback

variable {S S' : Scheme.{0}}

/-- The action on the base change, as an endomorphism in `Over S'`. -/
def pullbackIotaHom (A : FEC S) (g : S' ⟶ S) (a : O) :
    (Over.pullback g).obj A.F ⟶ (Over.pullback g).obj A.F :=
  (Over.pullback g).map (Over.homMk (A.iota a) (A.iota_over a))

def pullbackIota (A : FEC S) (g : S' ⟶ S) (a : O) :
    ((Over.pullback g).obj A.F).left ⟶ ((Over.pullback g).obj A.F).left :=
  (pullbackIotaHom A g a).left

theorem pullbackIota_over (A : FEC S) (g : S' ⟶ S) (a : O) :
    pullbackIota A g a ≫ ((Over.pullback g).obj A.F).hom = ((Over.pullback g).obj A.F).hom :=
  Over.w (pullbackIotaHom A g a)

theorem homMk_pullbackIota (A : FEC S) (g : S' ⟶ S) (a : O) :
    (Over.homMk (pullbackIota A g a) (pullbackIota_over A g a) :
        (Over.pullback g).obj A.F ⟶ (Over.pullback g).obj A.F) = pullbackIotaHom A g a :=
  Over.OverMorphism.ext rfl

/-- The group structure transported by the braided monoidal functor `Over.pullback g`. -/
def pullbackGrp (A : FEC S) (g : S' ⟶ S) : GrpObj ((Over.pullback g).obj A.F) :=
  Functor.grpObjObj (F := Over.pullback g) (G := A.F)

theorem pullbackIotaHom_isMonHom (A : FEC S) (g : S' ⟶ S) (a : O) :
    letI := pullbackGrp A g
    IsMonHom (pullbackIotaHom A g a) := by
  haveI := A.iota_hom a
  exact Functor.map.instIsMonHom (F := Over.pullback g) A.F A.F
    (Over.homMk (A.iota a) (A.iota_over a))

theorem pullbackIota_one (A : FEC S) (g : S' ⟶ S) : pullbackIota A g 1 = 𝟙 _ := by
  unfold pullbackIota pullbackIotaHom
  rw [iotaHom_one A, CategoryTheory.Functor.map_id]
  rfl

theorem pullbackIota_mul (A : FEC S) (g : S' ⟶ S) (a b : O) :
    pullbackIota A g (a * b) = pullbackIota A g b ≫ pullbackIota A g a := by
  unfold pullbackIota pullbackIotaHom
  rw [iotaHom_mul A a b, CategoryTheory.Functor.map_comp]
  rfl

theorem pullbackIota_add (A : FEC S) (g : S' ⟶ S) (a b : O) :
    letI := pullbackGrp A g
    (Over.homMk (pullbackIota A g (a + b)) (pullbackIota_over A g _) :
        (Over.pullback g).obj A.F ⟶ (Over.pullback g).obj A.F) =
      Over.homMk (pullbackIota A g a) (pullbackIota_over A g a) *
        Over.homMk (pullbackIota A g b) (pullbackIota_over A g b) := by
  try dsimp only
  rw [homMk_pullbackIota, homMk_pullbackIota, homMk_pullbackIota]
  unfold pullbackIotaHom
  rw [A.iota_add a b]
  exact CategoryTheory.Functor.map_mul (Over.pullback g) _ _

theorem pullback_proper (A : FEC S) (g : S' ⟶ S) :
    IsProper ((Over.pullback g).obj A.F).hom := by
  haveI := IsProper.isStableUnderBaseChange
  show IsProper (Limits.pullback.snd A.F.hom g)
  exact MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback A.F.hom g) A.proper

theorem pullback_smooth (A : FEC S) (g : S' ⟶ S) :
    SmoothOfRelativeDimension 2 ((Over.pullback g).obj A.F).hom := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 2
  show SmoothOfRelativeDimension 2 (Limits.pullback.snd A.F.hom g)
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 2)
    (IsPullback.of_hasPullback A.F.hom g) A.smooth

theorem pullback_geomConn (A : FEC S) (g : S' ⟶ S) :
    GeometricallyConnected ((Over.pullback g).obj A.F).hom := by
  show GeometricallyConnected (Limits.pullback.snd A.F.hom g)
  exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
    (IsPullback.of_hasPullback A.F.hom g) A.geomConn

/-- Base change of a false elliptic curve along `g : S' ⟶ S`. -/
def FEC.pullback (A : FEC S) (g : S' ⟶ S) : FEC S' where
  F := (Over.pullback g).obj A.F
  proper := pullback_proper A g
  smooth := pullback_smooth A g
  iota := pullbackIota A g
  iota_over := pullbackIota_over A g
  grp := pullbackGrp A g
  geomConn := pullback_geomConn A g
  iota_hom a := by
    rw [homMk_pullbackIota]
    exact pullbackIotaHom_isMonHom A g a
  iota_one := pullbackIota_one A g
  iota_mul := pullbackIota_mul A g
  iota_add := pullbackIota_add A g

/-- The first projection of the base change square. -/
def FEC.pullbackFst (A : FEC S) (g : S' ⟶ S) : (A.pullback g).F.left ⟶ A.F.left :=
  Limits.pullback.fst A.F.hom g

theorem FEC.pullback_isPullback (A : FEC S) (g : S' ⟶ S) :
    IsPullback (A.pullbackFst g) (A.pullback g).F.hom A.F.hom g :=
  IsPullback.of_hasPullback A.F.hom g

theorem FEC.pullback_iota_fst (A : FEC S) (g : S' ⟶ S) (a : O) :
    (A.pullback g).iota a ≫ A.pullbackFst g = A.pullbackFst g ≫ A.iota a := by
  show ((Over.pullback g).map (Over.homMk (A.iota a) (A.iota_over a))).left ≫
      Limits.pullback.fst A.F.hom g = Limits.pullback.fst A.F.hom g ≫ A.iota a
  first
    | exact SGRSplit.map_left_fst _
    | exact Limits.pullback.lift_fst _ _ _
    | simp [Over.pullback_map_left]

theorem FEC.pullback_fibre (A : FEC S) (g : S' ⟶ S) : FECFibre A g (A.pullback g) :=
  ⟨A.pullbackFst g, A.pullback_isPullback g, A.pullback_iota_fst g⟩

/-! ## 3. Pullback of sections -/

/-- The section of `A.pullback g` induced by a section `P` of `A`. -/
def FEC.pullbackSection (A : FEC S) (g : S' ⟶ S) (P : S ⟶ A.F.left)
    (hP : P ≫ A.F.hom = 𝟙 S) : S' ⟶ (A.pullback g).F.left :=
  (Limits.pullback.lift (g ≫ P) (𝟙 S')
    (by rw [Category.assoc, hP, Category.comp_id, Category.id_comp]) :
    S' ⟶ Limits.pullback A.F.hom g)

theorem FEC.pullbackSection_fst (A : FEC S) (g : S' ⟶ S) (P : S ⟶ A.F.left)
    (hP : P ≫ A.F.hom = 𝟙 S) : A.pullbackSection g P hP ≫ A.pullbackFst g = g ≫ P := by
  unfold FEC.pullbackSection FEC.pullbackFst
  exact Limits.pullback.lift_fst _ _ _

theorem FEC.pullbackSection_sec (A : FEC S) (g : S' ⟶ S) (P : S ⟶ A.F.left)
    (hP : P ≫ A.F.hom = 𝟙 S) : A.pullbackSection g P hP ≫ (A.pullback g).F.hom = 𝟙 S' := by
  unfold FEC.pullbackSection
  exact Limits.pullback.lift_snd _ _ _

theorem FEC.isGen_pullbackSection {M : ℕ} (A : FEC S) (g : S' ⟶ S) (P : S ⟶ A.F.left)
    (hP : P ≫ A.F.hom = 𝟙 S) (hgen : IsGen M A P) :
    IsGen M (A.pullback g) (A.pullbackSection g P hP) := by
  refine (isGen_iff_of_fibre (A.pullback_isPullback g) (A.pullback_iota_fst g)).2 ?_
  rw [A.pullbackSection_fst g P hP]
  exact isGen_comp g hgen

/-! ## 4. Pullback of `V₁(5)`-structures -/

/-- The unit of `Over S` and `Over.mk (𝟙 S)`, identified by the identity. -/
def unitMkIso (S : Scheme.{0}) : 𝟙_ (Over S) ≅ Over.mk (𝟙 S) :=
  Over.isoMk (Iso.refl S) (by
    show 𝟙 S ≫ 𝟙 S = 𝟙 S
    exact Category.id_comp _)

theorem unit_homMk_eq_comp (A : FEC S) (Q : S ⟶ A.F.left) (hQ : Q ≫ A.F.hom = 𝟙 S) :
    (Over.homMk (U := 𝟙_ (Over S)) Q hQ : 𝟙_ (Over S) ⟶ A.F) =
      (unitMkIso S).hom ≫ (Over.homMk (U := Over.mk (𝟙 S)) Q hQ : Over.mk (𝟙 S) ⟶ A.F) :=
  Over.OverMorphism.ext (Category.id_comp Q).symm

/-- The structure map `Over.mk (𝟙 S' ≫ g) ⟶ 𝟙_ (Over S)`. -/
def baseUnitHom (g : S' ⟶ S) : Over.mk (𝟙 S' ≫ g) ⟶ 𝟙_ (Over S) :=
  Over.homMk g (by
    show g ≫ 𝟙 S = 𝟙 S' ≫ g
    rw [Category.comp_id, Category.id_comp])

theorem homMk_base_comp (A : FEC S) (g : S' ⟶ S) (R : S ⟶ A.F.left) (hR : R ≫ A.F.hom = 𝟙 S)
    (hgR : (g ≫ R) ≫ A.F.hom = 𝟙 S' ≫ g) :
    (Over.homMk (U := Over.mk (𝟙 S' ≫ g)) (g ≫ R) hgR : Over.mk (𝟙 S' ≫ g) ⟶ A.F) =
      baseUnitHom g ≫ (Over.homMk (U := 𝟙_ (Over S)) R hR : 𝟙_ (Over S) ⟶ A.F) :=
  Over.OverMorphism.ext rfl

/-- Base change of a `V₁(5)`-structure. -/
def V15.pullback {A : FEC S} (α : V15 A) (g : S' ⟶ S) : V15 (A.pullback g) where
  Q := A.pullbackSection g α.Q α.Q_sec
  Q_sec := A.pullbackSection_sec g α.Q α.Q_sec
  order := by
    try dsimp only
    have hgQ : (g ≫ α.Q) ≫ A.F.hom = 𝟙 S' ≫ g := by
      rw [Category.assoc, α.Q_sec, Category.comp_id, Category.id_comp]
    have ho : (Over.homMk (U := 𝟙_ (Over S)) α.Q α.Q_sec : 𝟙_ (Over S) ⟶ A.F) ^ 5 = 1 :=
      α.order
    have h0 : (Over.homMk (U := Over.mk (𝟙 S' ≫ g)) (g ≫ α.Q) hgQ :
        Over.mk (𝟙 S' ≫ g) ⟶ A.F) ^ 5 = 1 := by
      rw [homMk_base_comp A g α.Q α.Q_sec hgQ, ← MonObj.comp_pow, ho, MonObj.comp_one]
    have h1 := (homMk_pow_eq_one_iff_of_fibre (A.pullback_isPullback g)
      (A.pullback_iota_fst g) (A.pullbackSection g α.Q α.Q_sec)
      (A.pullbackSection_sec g α.Q α.Q_sec) (g ≫ α.Q) hgQ
      (A.pullbackSection_fst g α.Q α.Q_sec) 5).2 h0
    rw [unit_homMk_eq_comp (A.pullback g) _ (A.pullbackSection_sec g α.Q α.Q_sec),
      ← MonObj.comp_pow, h1, MonObj.comp_one]
  inKer := by
    try dsimp only
    have hQ' := A.pullbackSection_sec g α.Q α.Q_sec
    have hR' : (A.pullbackSection g α.Q α.Q_sec ≫ (A.pullback g).iota e5) ≫
        (A.pullback g).F.hom = 𝟙 S' := by
      rw [Category.assoc, (A.pullback g).iota_over, hQ']
    have hR0 : (α.Q ≫ A.iota e5) ≫ A.F.hom = 𝟙 S := by
      rw [Category.assoc, A.iota_over, α.Q_sec]
    have hR : (g ≫ α.Q ≫ A.iota e5) ≫ A.F.hom = 𝟙 S' ≫ g := by
      rw [Category.assoc, hR0, Category.comp_id, Category.id_comp]
    have e : (A.pullbackSection g α.Q α.Q_sec ≫ (A.pullback g).iota e5) ≫ A.pullbackFst g =
        g ≫ α.Q ≫ A.iota e5 := by
      rw [Category.assoc, A.pullback_iota_fst g e5, ← Category.assoc,
        A.pullbackSection_fst g α.Q α.Q_sec, Category.assoc]
    have hk : (Over.homMk (U := 𝟙_ (Over S)) (α.Q ≫ A.iota e5) hR0 :
        𝟙_ (Over S) ⟶ A.F) = 1 := α.inKer
    have hz : (Over.homMk (U := Over.mk (𝟙 S' ≫ g)) (g ≫ α.Q ≫ A.iota e5) hR :
        Over.mk (𝟙 S' ≫ g) ⟶ A.F) = 1 := by
      rw [homMk_base_comp A g (α.Q ≫ A.iota e5) hR0 hR, hk, MonObj.comp_one]
    rw [unit_homMk_eq_comp (A.pullback g) _ hR',
      (homMk_eq_one_iff_of_fibre (A.pullback_isPullback g) (A.pullback_iota_fst g) _ hR' _
        hR e).2 hz, MonObj.comp_one]
  nonzero := by
    try dsimp only
    intro k _ _ s hz
    have hQ'' : (s ≫ A.pullbackSection g α.Q α.Q_sec) ≫ (A.pullback g).F.hom = s := by
      rw [Category.assoc, A.pullbackSection_sec, Category.comp_id]
    have hR : ((s ≫ g) ≫ α.Q) ≫ A.F.hom = s ≫ g := by
      rw [Category.assoc, α.Q_sec, Category.comp_id]
    have e : (s ≫ A.pullbackSection g α.Q α.Q_sec) ≫ A.pullbackFst g = (s ≫ g) ≫ α.Q := by
      simp only [Category.assoc, FEC.pullbackSection_fst]
    exact α.nonzero k (s ≫ g)
      ((homMk_eq_one_iff_of_fibre (A.pullback_isPullback g) (A.pullback_iota_fst g)
        (s ≫ A.pullbackSection g α.Q α.Q_sec) hQ'' ((s ≫ g) ≫ α.Q) hR e).1 hz)

theorem V15.pullback_fibre {A : FEC S} (α : V15 A) (g : S' ⟶ S) :
    V15Fibre A α g (A.pullback g) (α.pullback g) :=
  ⟨A.pullbackFst g, A.pullback_isPullback g, A.pullback_iota_fst g,
    A.pullbackSection_fst g α.Q α.Q_sec⟩

end Pullback

end Y3Buzzard
