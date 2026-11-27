import ZInQKernel.Contrib.OneProof.BuzzardFrameRepTorsor5

/-!
# Buzzard's `V₁(5)`-structures: frames by generators, orbits, sheafification

The level structures of K. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87
(1997), §1, Defs. 1.1–1.2, for `U = V₁(5)`, with full level-5 structures recorded by their value at
`1` (`Frames5`), and the orbit invariant `invOrb`. The literal form, with Def. 1.1's isomorphisms,
is in `LitFrames` and `Leaf`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj

namespace Y3Buzzard.XDV15

attribute [local instance] FEC.grp

/-! ## 0. The étale site of `S`-schemes -/

/-- The étale topology on `S`-schemes (Buzzard, p. 4: "the sheafification with respect to the
étale topology of the functor ... from `S`-schemes to sets"), induced on `Over S` by Mathlib's
big étale site. -/
abbrev etaleOver (S : Scheme.{0}) : GrothendieckTopology (Over S) :=
  Scheme.etaleTopology.over S

/-- The étale topology is subcanonical: it is coarser than the pro-étale topology. -/
instance etale_subcanonical : Scheme.etaleTopology.{0}.Subcanonical :=
  .of_le Scheme.etaleTopology_le_proetaleTopology

example (S : Scheme.{0}) : (etaleOver S).Subcanonical := inferInstance

example (S : Scheme.{0}) : HasSheafify (etaleOver S) (Type 1) := inferInstance

/-! ## 1. The group `H` -/

/-- `1 - e5`, sent by `κ` to `diag(0, 1)` modulo 5 (with `κ(e5) ≡ diag(1, 0)`). -/
def f5 : O := 1 - e5

/-- Buzzard's `H = u₅(V₁(5)) = {(a b; 0 1)} ⊂ (O/5O)ˣ` for `κ(e5) ≡ diag(1, 0)`: the stabiliser
of `diag(0, 1)` under right multiplication. -/
def H5 : Subgroup (Y3OrderMod.G 5) where
  carrier := {δ | ((f5 : O) : Y3OrderMod.OMod 5) * (δ : Y3OrderMod.OMod 5) =
    ((f5 : O) : Y3OrderMod.OMod 5)}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at ha hb ⊢
    rw [← _root_.mul_assoc, ha, hb]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    calc ((f5 : O) : Y3OrderMod.OMod 5) * ((a⁻¹ : Y3OrderMod.G 5) : Y3OrderMod.OMod 5)
        = (((f5 : O) : Y3OrderMod.OMod 5) * (a : Y3OrderMod.OMod 5)) *
            ((a⁻¹ : Y3OrderMod.G 5) : Y3OrderMod.OMod 5) := by rw [ha]
      _ = ((f5 : O) : Y3OrderMod.OMod 5) := by rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one]

/-! ## 2. Full level-5 frames, `F_{A/S,5}` (Def. 1.1 and p. 4) -/

/-- Transport of `IsGenAt` along equalities of the base point and of the point. -/
theorem isGenAt_transport {S : Scheme.{0}} (A : FEC S) {k : Type} [Field k]
    {b b' : Spec (CommRingCat.of k) ⟶ S} {Q Q' : Spec (CommRingCat.of k) ⟶ A.F.left}
    (hb : b = b') (hQ : Q = Q') (w : Q ≫ A.F.hom = b) (w' : Q' ≫ A.F.hom = b') :
    IsGenAt 5 A b (Over.homMk (U := Over.mk b) Q w) →
      IsGenAt 5 A b' (Over.homMk (U := Over.mk b') Q' w') := by
  subst hb
  subst hQ
  exact id

/-- Generators of full level-5 structures are stable under base change. -/
theorem isGen_comp {S : Scheme.{0}} (A : FEC S) {T T' : Scheme.{0}} (f : T' ⟶ T)
    {P : T ⟶ A.F.left} (hP : IsGen 5 A P) : IsGen 5 A (f ≫ P) := by
  obtain ⟨h1, h2⟩ := hP
  refine ⟨?_, fun k _ _ s => ?_⟩
  · have e : (Over.homMk (U := Over.mk ((f ≫ P) ≫ A.F.hom)) (f ≫ P) rfl :
          Over.mk ((f ≫ P) ≫ A.F.hom) ⟶ A.F) =
        (Over.homMk (U := Over.mk ((f ≫ P) ≫ A.F.hom)) (V := Over.mk (P ≫ A.F.hom)) f
          (by simp)) ≫ (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl) := by
      ext; simp
    rw [e, ← MonObj.comp_pow, h1, MonObj.comp_one]
  · exact isGenAt_transport A (by simp only [Category.assoc]) (by simp only [Category.assoc])
      _ _ (h2 k (s ≫ f))

/-- `F_{A/S,5}`: on `T/S`, the full level-5 structures `α` on `A_T`, recorded by `α(1)`, a point
of `A` over `T` generating the 5-torsion at every geometric point (`IsGen`). -/
def FramesSub {S : Scheme.{0}} (A : FEC S) : Subfunctor (yoneda.obj A.F) where
  obj T := {x | IsGen 5 A x.left}
  map {T T'} i x hx := by
    show IsGen 5 A (i.unop ≫ x).left
    rw [Over.comp_left]
    exact isGen_comp A i.unop.left hx

/-- The presheaf `T ↦ F_{A/S,5}(T)` on `S`-schemes. -/
abbrev Frames5 {S : Scheme.{0}} (A : FEC S) : (Over S)ᵒᵖ ⥤ Type := (FramesSub A).toFunctor

/-- `ι(a)` as an endomorphism of `A` over `S`. -/
abbrev iotaO {S : Scheme.{0}} (A : FEC S) (a : O) : A.F ⟶ A.F :=
  Over.homMk (A.iota a) (A.iota_over a)

/-! ## 3. Orbits and their étale sheafification, `F_{A/S,H}` (p. 4) -/

/-- Buzzard's action `α ↦ α ∘ r_δ` restricted to `H`, on generators: `P ↦ ι(δ) P`. Two frames are
related when they lie in one `H`-orbit. -/
def OrbRel {S : Scheme.{0}} (A : FEC S) (T : (Over S)ᵒᵖ) :
    (Frames5 A).obj T → (Frames5 A).obj T → Prop :=
  fun P P' => ∃ δ ∈ H5, P'.1 = P.1 ≫ iotaO A (Y3OrderMod.σ δ)

/-- `T ↦ H\F_{A/S,5}(T)`, the orbit spaces. -/
def Orbits5 {S : Scheme.{0}} (A : FEC S) : (Over S)ᵒᵖ ⥤ Type where
  obj T := Quot (OrbRel A T)
  map {T T'} f := ↾(Quot.map (fun P => (Frames5 A).map f P) (by
    rintro P P' ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, ?_⟩
    show f.unop ≫ P'.1 = (f.unop ≫ P.1) ≫ _
    rw [h, Category.assoc]))
  map_id T := by
    ext q
    induction q using Quot.ind
    simp
    rfl
  map_comp f g := by
    ext q
    induction q using Quot.ind
    simp
    rfl

/-- `F_{A/S,H}` as a presheaf: the étale sheafification of `T ↦ H\F_{A/S,5}(T)` (lifted to
`Type 1`, the universe in which Mathlib sheafifies on the large site `Over S`). -/
abbrev LevelPre {S : Scheme.{0}} (A : FEC S) : (Over S)ᵒᵖ ⥤ Type 1 :=
  sheafify (etaleOver S) (Orbits5 A ⋙ uliftFunctor.{1, 0})

/-- Def. 1.2: a naive level `H` structure on `A/S` is an element of `F_{A/S,H}(S)`. -/
abbrev LevelStr {S : Scheme.{0}} (A : FEC S) : Type 1 :=
  (LevelPre A).obj (op (Over.mk (𝟙 S)))

/-! ## 4. Morphisms of `X^D(U)` (p. 5) -/

/-- The third bullet of the morphisms of `X^D(U)`, for the cartesian `O`-linear square `h` over
`g : S' ⟶ S`: `α'` corresponds to the restriction of `α` along `g`, through the isomorphism of
étale sheaves `F_{A'/S',H} ≅ F_{A_{S'}/S',H}` induced by `P' ↦ h ∘ P'` on frames. -/
def LevelFibre {S S' : Scheme.{0}} (A : FEC S) (α : LevelStr A) (g : S' ⟶ S) (A' : FEC S')
    (α' : LevelStr A') (h : A'.F.left ⟶ A.F.left) : Prop :=
  ∃ ψ : LevelPre A' ≅ (Over.map g).op ⋙ LevelPre A,
    (∀ (T : Over S') (P' : (Frames5 A').obj (op T))
        (P : (Frames5 A).obj (op ((Over.map g).obj T))), P.1.left = P'.1.left ≫ h →
        ψ.hom.app (op T) ((toSheafify (etaleOver S') (Orbits5 A' ⋙ uliftFunctor.{1, 0})).app
            (op T) (ULift.up (Quot.mk _ P'))) =
          (toSheafify (etaleOver S) (Orbits5 A ⋙ uliftFunctor.{1, 0})).app
            (op ((Over.map g).obj T)) (ULift.up (Quot.mk _ P))) ∧
    ψ.hom.app (op (Over.mk (𝟙 S'))) α' =
      (LevelPre A).map (Over.homMk (U := (Over.map g).obj (Over.mk (𝟙 S'))) (V := Over.mk (𝟙 S))
        g (by simp)).op α

/-- The leaf in generator form. Buzzard, Thm 2.1 and Cor. 2.3, at `U = V₁(5)` (`M_U d = 30`), with his own
level structures: `X^D(V₁(5))` is the stack associated to a scheme `X`, proper and smooth of
relative dimension 1 and projective over `Z[1/30]`. Fine-moduli form: a universal object over
`X`, every object is its pullback along a unique `g`, and the comparison is unique (objects have
no non-trivial automorphisms, proof of Cor. 2.3). -/
def BuzzardXDV15 : Prop :=
  ∃ (X : Over Z30Base) (A : FEC X.left) (α : LevelStr A),
    IsProper X.hom ∧ SmoothOfRelativeDimension 1 X.hom ∧
    (∃ (N : ℕ) (i : X.left ⟶ PN N), IsClosedImmersion i ∧ i ≫ toBase N = X.hom) ∧
    (∀ (S : Over Z30Base) (A' : FEC S.left) (α' : LevelStr A'),
      ∃! g : S ⟶ X, ∃ h : A'.F.left ⟶ A.F.left, IsPullback h A'.F.hom A.F.hom g.left ∧
        (∀ a : O, A'.iota a ≫ h = h ≫ A.iota a) ∧ LevelFibre A α g.left A' α' h) ∧
    ∀ (S : Over Z30Base) (A' : FEC S.left) (α' : LevelStr A') (g : S ⟶ X)
      (h h' : A'.F.left ⟶ A.F.left),
      (IsPullback h A'.F.hom A.F.hom g.left ∧ (∀ a : O, A'.iota a ≫ h = h ≫ A.iota a) ∧
        LevelFibre A α g.left A' α' h) →
      (IsPullback h' A'.F.hom A.F.hom g.left ∧ (∀ a : O, A'.iota a ≫ h' = h' ≫ A.iota a) ∧
        LevelFibre A α g.left A' α' h') →
      h = h'

/-! ## 5. The bridge target (statement only) -/

/-- A section of the Yoneda presheaf, read as a point of `A` over `T`. -/
abbrev pt {S : Scheme.{0}} {A : FEC S} {T : (Over S)ᵒᵖ} (x : (yoneda.obj A.F).obj T) :
    T.unop ⟶ A.F := x

/-- The étale sheaf of `V15`-points: `5`-torsion, killed by `ι(e5)`, nonzero at every geometric
point (zero section `torsZeroL A`). -/
def V15Sub {S : Scheme.{0}} (A : FEC S) : Subfunctor (yoneda.obj A.F) where
  obj T := {x | pt x ^ 5 = 1 ∧ pt x ≫ iotaO A e5 = 1 ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T.unop.left),
      s ≫ (pt x).left ≠ s ≫ T.unop.hom ≫ torsZeroL A}
  map {T T'} i x hx := by
    obtain ⟨h1, h2, h3⟩ := hx
    refine ⟨?_, ?_, ?_⟩
    · show (i.unop ≫ pt x) ^ 5 = 1
      rw [← MonObj.comp_pow, h1, MonObj.comp_one]
    · show (i.unop ≫ pt x) ≫ iotaO A e5 = 1
      rw [Category.assoc, h2, MonObj.comp_one]
    · intro k _ _ s
      show s ≫ (i.unop ≫ pt x).left ≠ s ≫ T'.unop.hom ≫ torsZeroL A
      rw [Over.comp_left, ← Over.w i.unop]
      simpa only [Category.assoc] using h3 k (s ≫ i.unop.left)

/-- The bridge, as a statement: the literal leaf, with Milne's Prop. 20.7 and Remark 8.4 at
`n = 5` (already inputs of the project), gives `BuzzardThm21Cor23V15'`. -/
def B5Bridge : Prop :=
  BuzzardXDV15 → MilneProp207 5 → GeomCard5 → BuzzardThm21Cor23V15'

/-! ## 6. The orbit invariant `α ↦ α(diag(0,1)) = ι(1 - e5) α(1)` -/

/-- `1 - e5` is not in `5 O`. -/
theorem f5_not_mem5 : ¬ ∃ b : O, f5 = ((5 : ℕ) : O) * b := by
  rintro ⟨b, hb⟩
  obtain ⟨n, hn⟩ := Y3OrderMod.exists_ofInt b
  have h1 : ((f5 : O) : B) = ofInt ![-2, 2, 0, -4] := by
    show ((1 - e5 : O) : B) = _
    rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one]
    show 1 - ofInt ![3, -2, 0, 4] = ofInt ![-2, 2, 0, -4]
    ext <;> simp [ofInt] <;> norm_num
  have h2 := congrArg Subtype.val hb
  rw [MulMemClass.coe_mul, GF5.coe_five, hn, h1, GF5.five_mul_ofInt] at h2
  have h3 := LeafQM.AV.ofInt_injective h2
  have h4 := congrFun h3 0
  simp at h4
  omega

/-- A frame is `5`-torsion in the group of points over `T`. -/
theorem frame_pow5 {S : Scheme.{0}} (A : FEC S) {T : Over S} (P : T ⟶ A.F)
    (hP : IsGen 5 A P.left) : P ^ 5 = 1 := by
  rw [← comp_iotaHom_natCast A P 5, comp_iota_eq_one_iff]
  rw [(torsPow_eq_one_iff A P.left 5).1 hP.1, Over.w P]

/-- `e5 (1 - e5) ≡ 0` modulo `5`. -/
theorem e5f5 : ∃ c : O, e5 * f5 - 0 = ((5 : ℕ) : O) * c := by
  obtain ⟨c, hc⟩ := GF5.rel_EE
  refine ⟨-c, ?_⟩
  unfold GF5.mE at hc
  rw [f5, mul_sub, _root_.mul_one, sub_zero, mul_neg, ← hc]
  abel

/-- The invariant of a frame: `P ↦ ι(1 - e5) P`, Buzzard's `Q = β(diag(0,1))` (proof of
Lemma 2.2, pp. 6-7). -/
def invFrame {S : Scheme.{0}} (A : FEC S) : Frames5 A ⟶ (V15Sub A).toFunctor where
  app T := ↾fun P => ⟨P.1 ≫ iotaO A f5, by
    have hG : IsGen 5 A P.1.left := P.2
    have hP5 := frame_pow5 A P.1 hG
    refine ⟨?_, ?_, ?_⟩
    · exact (GF5.fecAct A T.unop).act_tors hP5 f5
    · show (GF5.fecAct A T.unop).act e5 ((GF5.fecAct A T.unop).act f5 P.1) = 1
      rw [(GF5.fecAct A T.unop).act_comp, (GF5.fecAct A T.unop).act_congr hP5 e5f5,
        (GF5.fecAct A T.unop).act_zero]
    · intro k _ _ s hs
      apply f5_not_mem5
      apply ((hG.2 k s).1 f5).1
      rw [comp_iota_eq_one_iff]
      simp only [Over.homMk_left, Over.mk_hom]
      have hw : P.1.left ≫ A.F.hom = T.unop.hom := Over.w P.1
      simp only [Over.comp_left, Over.homMk_left] at hs
      rw [← hw] at hs
      simpa only [Category.assoc] using hs⟩
  naturality T T' f := by
    ext P
    exact Subtype.ext (Category.assoc _ _ _)

/-- The invariant is constant on `H`-orbits. -/
theorem invFrame_orb {S : Scheme.{0}} (A : FEC S) (T : (Over S)ᵒᵖ)
    (P P' : (Frames5 A).obj T) (h : OrbRel A T P P') :
    (invFrame A).app T P = (invFrame A).app T P' := by
  obtain ⟨δ, hδ, hP'⟩ := h
  have hG : IsGen 5 A P.1.left := P.2
  have hP5 := frame_pow5 A P.1 hG
  apply Subtype.ext
  show P.1 ≫ iotaO A f5 = P'.1 ≫ iotaO A f5
  rw [hP']
  show (GF5.fecAct A T.unop).act f5 P.1 =
    (GF5.fecAct A T.unop).act f5 ((GF5.fecAct A T.unop).act (Y3OrderMod.σ δ) P.1)
  rw [(GF5.fecAct A T.unop).act_comp]
  refine (GF5.fecAct A T.unop).act_congr hP5 ?_
  have hc : ((f5 * Y3OrderMod.σ δ : O) : Y3OrderMod.OMod 5) = ((f5 : O) : Y3OrderMod.OMod 5) := by
    rw [RingCon.coe_mul, Y3OrderMod.σ_spec]
    exact hδ
  obtain ⟨c, hc'⟩ := Y3OrderMod.coe_eq_coe_iff.1 hc.symm
  exact ⟨c, hc'⟩

/-- The invariant on orbit spaces, `H\F_{A/S,5} ⟶ V15`. -/
def invOrb {S : Scheme.{0}} (A : FEC S) : Orbits5 A ⟶ (V15Sub A).toFunctor where
  app T := ↾(Quot.lift (fun P => (invFrame A).app T P) (fun P P' h => invFrame_orb A T P P' h))
  naturality T T' f := by
    ext q
    induction q using Quot.ind with
    | mk P => exact Subtype.ext (Category.assoc _ _ _)

/-! ## 7. Local bijectivity gives `F_{A/S,H}(S) ≃ V15` -/

/-- Points of `A` form an étale sheaf on `S`-schemes: Mathlib's pro-étale (hence étale) topology
is subcanonical, so morphisms glue along étale covers. -/
theorem points_isSheaf {S : Scheme.{0}} (A : FEC S) :
    Presieve.IsSheaf (etaleOver S) (yoneda.obj A.F) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- The locality of "nonzero at geometric points": a geometric point of `T`
lifts through some member of every étale-covering sieve of `T` in `Over S`. -/
theorem geomPt_lift {S : Scheme.{0}} {T : Over S} (R : Sieve T) (hR : R ∈ etaleOver S T)
    {k : Type} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T.left) :
    ∃ (U : Over S) (f : U ⟶ T) (_ : R f) (l : Spec (CommRingCat.of k) ⟶ U.left),
      l ≫ f.left = s := by
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hR
  obtain ⟨i, y, hy⟩ := @Scheme.Cover.exists_eq _ _ Scheme.instJointlySurjectivePrecoverage 𝒰 (s default)
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (𝒰.f i) s y hy
  have hmem : (Sieve.overEquiv T R) (𝒰.f i) := hle _ _ (Presieve.ofArrows.mk i)
  rw [Sieve.overEquiv_iff] at hmem
  exact ⟨_, _, hmem, l, hl⟩

/-- If the invariant is locally injective and locally surjective for the étale topology, and the
`V15` presheaf is an étale sheaf, then level structures are `V15`-points (at every `T`). -/
theorem levelPre_iso_of_locallyBijective {S : Scheme.{0}} (A : FEC S)
    (hsh : Presheaf.IsSheaf (etaleOver S) ((V15Sub A).toFunctor ⋙ uliftFunctor.{1, 0}))
    [Presheaf.IsLocallyInjective (etaleOver S) (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0})]
    [Presheaf.IsLocallySurjective (etaleOver S)
      (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0})] :
    IsIso (sheafifyLift (etaleOver S) (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0}) hsh) := by
  let F : Sheaf (etaleOver S) (Type 1) := ⟨_, hsh⟩
  let φ : (presheafToSheaf (etaleOver S) (Type 1)).obj (Orbits5 A ⋙ uliftFunctor.{1, 0}) ⟶ F :=
    ⟨sheafifyLift (etaleOver S) (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0}) hsh⟩
  have hfac : toSheafify (etaleOver S) (Orbits5 A ⋙ uliftFunctor.{1, 0}) ≫ φ.hom =
      Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0} :=
    toSheafify_sheafifyLift _ _ _
  have hI : Sheaf.IsLocallyInjective φ :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac (etaleOver S) _
      hfac
  have hS : Sheaf.IsLocallySurjective φ :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac (etaleOver S) hfac
  have : IsIso φ := (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨hI, hS⟩
  exact Functor.map_isIso (sheafToPresheaf _ _) φ

end Y3Buzzard.XDV15

