import ZInQKernel.Contrib.OneProof.BuzzardXDV15.Defs

/-!
# Base change of `V₁(5)`-structures

Let `h : A' ⟶ A` be a cartesian `O`-linear square over `g : S' ⟶ S`.

1. `P' ↦ h ∘ P'` carries frames of `A'` over `T/S'` to frames of `A` over `T/S`, and
   `V15`-points likewise; on `V15`-points it is a bijection.
2. The canonical isomorphism `ψ_h : F_{A'/S',H} ≅ (Over.map g)^* F_{A/S,H}` is compatible with
   the frame transport (the first clause of `LevelFibre`), and it is the only morphism with
   this property.
3. `LevelFibre A α g A' α' h` holds iff the `V15`-points of `α'` and `α` correspond under `h`.

The sheaf property of `V15` and the local bijectivity of the orbit invariant (the hypotheses of
`levelPre_iso_of_locallyBijective`) are assumed for `A` and for `A'`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj

namespace Y3Buzzard.XDV15

attribute [local instance] FEC.grp

/-! ## 0. The isomorphism `F_{A/S,H} ≅ V15` and the evaluation `Φ` -/

section Iso

/-- The isomorphism `F_{A/S,H} ≅ V15` of `levelPre_iso_of_locallyBijective`. -/
def levelIso {S : Scheme.{0}} (A : FEC S)
    (hsh : Presheaf.IsSheaf (etaleOver S) ((V15Sub A).toFunctor ⋙ uliftFunctor.{1, 0}))
    [Presheaf.IsLocallyInjective (etaleOver S) (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0})]
    [Presheaf.IsLocallySurjective (etaleOver S)
      (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0})] :
    LevelPre A ≅ (V15Sub A).toFunctor ⋙ uliftFunctor.{1, 0} :=
  haveI := levelPre_iso_of_locallyBijective A hsh
  asIso (sheafifyLift (etaleOver S) (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0}) hsh)

/-- `Φ A`: the `V15`-point of `A` over `S` attached to a level structure (the value of
`levelIso` at `S`). -/
def Φ {S : Scheme.{0}} (A : FEC S)
    (hsh : Presheaf.IsSheaf (etaleOver S) ((V15Sub A).toFunctor ⋙ uliftFunctor.{1, 0}))
    [Presheaf.IsLocallyInjective (etaleOver S) (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0})]
    [Presheaf.IsLocallySurjective (etaleOver S)
      (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0})]
    (α : LevelStr A) : (V15Sub A).toFunctor.obj (op (Over.mk (𝟙 S))) :=
  ((levelIso A hsh).hom.app (op (Over.mk (𝟙 S))) α).down

variable {S : Scheme.{0}} (A : FEC S)
    (hsh : Presheaf.IsSheaf (etaleOver S) ((V15Sub A).toFunctor ⋙ uliftFunctor.{1, 0}))
    [Presheaf.IsLocallyInjective (etaleOver S) (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0})]
    [Presheaf.IsLocallySurjective (etaleOver S)
      (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0})]

include hsh in
theorem levelIso_app_injective (X : (Over S)ᵒᵖ) :
    Function.Injective ((levelIso A hsh).hom.app X) := by
  intro a b hab
  simpa only [Iso.hom_inv_id_app_apply] using congrArg ((levelIso A hsh).inv.app X) hab

include hsh in
/-- On the class of an orbit, `levelIso` is the orbit invariant. -/
theorem levelIso_toSheafify (T : Over S) (P : (Frames5 A).obj (op T)) :
    (levelIso A hsh).hom.app (op T)
        ((toSheafify (etaleOver S) (Orbits5 A ⋙ uliftFunctor.{1, 0})).app (op T)
          (ULift.up (Quot.mk _ P))) =
      ULift.up ((invFrame A).app (op T) P) :=
  congrArg (fun φ => φ.app (op T) (ULift.up (Quot.mk (OrbRel A (op T)) P)))
    (toSheafify_sheafifyLift (etaleOver S) (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0}) hsh)

include hsh in
theorem Φ_bijective : Function.Bijective (Φ A hsh) := by
  refine ⟨fun a b hab => levelIso_app_injective A hsh _ (ULift.ext hab), fun v => ?_⟩
  let w : ((V15Sub A).toFunctor ⋙ uliftFunctor.{1, 0}).obj (op (Over.mk (𝟙 S))) := ULift.up v
  refine ⟨(levelIso A hsh).inv.app (op (Over.mk (𝟙 S))) w, ?_⟩
  exact congrArg ULift.down (Iso.inv_hom_id_app_apply (levelIso A hsh) (op (Over.mk (𝟙 S))) w)

end Iso

/-! ## 1. Transport of points, frames and `V15`-points along `h` -/

section Transport

variable {S S' : Scheme.{0}} {A : FEC S} {A' : FEC S'} {g : S' ⟶ S}
  {h : A'.F.left ⟶ A.F.left}

/-- `x ↦ h ∘ x`: a point of `A'` over `T/S'` gives a point of `A` over `T/S`. -/
def ptMap (hpb : IsPullback h A'.F.hom A.F.hom g) {T : Over S'} (x : T ⟶ A'.F) :
    (Over.map g).obj T ⟶ A.F :=
  Over.homMk (x.left ≫ h) (by
    rw [Over.map_obj_hom, Category.assoc, hpb.w, ← Category.assoc, Over.w x])

@[simp]
theorem ptMap_left (hpb : IsPullback h A'.F.hom A.F.hom g) {T : Over S'} (x : T ⟶ A'.F) :
    (ptMap hpb x).left = x.left ≫ h :=
  rfl

/-- The inverse of `ptMap`, from the universal property of the cartesian square. -/
def ptLift (hpb : IsPullback h A'.F.hom A.F.hom g) {T : Over S'} (y : (Over.map g).obj T ⟶ A.F) :
    T ⟶ A'.F :=
  Over.homMk (hpb.lift y.left T.hom (by simpa only [Over.map_obj_hom] using Over.w y))
    (hpb.lift_snd _ _ _)

theorem ptMap_ptLift (hpb : IsPullback h A'.F.hom A.F.hom g) {T : Over S'}
    (y : (Over.map g).obj T ⟶ A.F) : ptMap hpb (ptLift hpb y) = y :=
  Over.OverMorphism.ext (hpb.lift_fst _ _ _)

theorem ptMap_injective (hpb : IsPullback h A'.F.hom A.F.hom g) {T : Over S'} :
    Function.Injective (ptMap hpb (T := T)) := by
  intro x y hxy
  apply Over.OverMorphism.ext
  apply hpb.hom_ext
  · exact congrArg (fun z => z.left) hxy
  · rw [Over.w x, Over.w y]

theorem ptMap_comp_iota (hpb : IsPullback h A'.F.hom A.F.hom g)
    (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a) {T : Over S'} (x : T ⟶ A'.F) (a : O) :
    ptMap hpb x ≫ iotaO A a = ptMap hpb (x ≫ iotaO A' a) :=
  Over.OverMorphism.ext (by
    show (x.left ≫ h) ≫ A.iota a = (x.left ≫ A'.iota a) ≫ h
    rw [Category.assoc, Category.assoc, hι])

theorem ptMap_one (hpb : IsPullback h A'.F.hom A.F.hom g)
    (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a) {T : Over S'} :
    ptMap hpb (1 : T ⟶ A'.F) = 1 := by
  have h0 := ptMap_comp_iota hpb hι (1 : T ⟶ A'.F) 0
  have e : iotaO A 0 = 1 := iotaHom_zero A
  have e' : iotaO A' 0 = 1 := iotaHom_zero A'
  rw [e, e', MonObj.comp_one, MonObj.comp_one] at h0
  exact h0.symm

theorem ptMap_pow (hpb : IsPullback h A'.F.hom A.F.hom g)
    (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a) {T : Over S'} (x : T ⟶ A'.F) (n : ℕ) :
    ptMap hpb (x ^ n) = ptMap hpb x ^ n := by
  rw [← comp_iotaHom_natCast A' x n, ← comp_iotaHom_natCast A (ptMap hpb x) n]
  exact (ptMap_comp_iota hpb hι x (n : O)).symm

/-- The zero sections correspond under `h`. -/
theorem torsZero_comp_h (hpb : IsPullback h A'.F.hom A.F.hom g)
    (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a) {T : Over S'} :
    (T.hom ≫ torsZeroL A') ≫ h = (T.hom ≫ g) ≫ torsZeroL A :=
  congrArg (fun z => Over.Hom.left z) (ptMap_one hpb hι (T := T))

theorem torsZeroL_sec (B : FEC S') : torsZeroL B ≫ B.F.hom = 𝟙 S' := by
  simp [torsZeroL]

/-- `x ↦ h ∘ x` preserves `V15`-points. -/
theorem ptMap_mem_v15Sub (hpb : IsPullback h A'.F.hom A.F.hom g)
    (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a) {T : Over S'} (x : T ⟶ A'.F)
    (hx : x ∈ (V15Sub A').obj (op T)) : ptMap hpb x ∈ (V15Sub A).obj (op ((Over.map g).obj T)) := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · show ptMap hpb x ^ 5 = 1
    rw [← ptMap_pow hpb hι, show x ^ 5 = 1 from h1, ptMap_one hpb hι]
  · show ptMap hpb x ≫ iotaO A e5 = 1
    rw [ptMap_comp_iota hpb hι, show x ≫ iotaO A' e5 = 1 from h2, ptMap_one hpb hι]
  · intro k _ _ s hs
    change s ≫ x.left ≫ h = s ≫ (T.hom ≫ g) ≫ torsZeroL A at hs
    apply h3 k s
    change s ≫ x.left = s ≫ T.hom ≫ torsZeroL A'
    apply hpb.hom_ext
    · have e := torsZero_comp_h hpb hι (T := T)
      simp only [Category.assoc] at hs e ⊢
      rw [hs, e]
    · simp only [Category.assoc, Over.w x, torsZeroL_sec, Category.comp_id]

/-- Conversely, `x` is a `V15`-point if `h ∘ x` is. -/
theorem mem_v15Sub_of_ptMap (hpb : IsPullback h A'.F.hom A.F.hom g)
    (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a) {T : Over S'} (x : T ⟶ A'.F)
    (hx : ptMap hpb x ∈ (V15Sub A).obj (op ((Over.map g).obj T))) :
    x ∈ (V15Sub A').obj (op T) := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · show x ^ 5 = 1
    apply ptMap_injective hpb
    rw [ptMap_pow hpb hι, ptMap_one hpb hι]
    exact h1
  · show x ≫ iotaO A' e5 = 1
    apply ptMap_injective hpb
    rw [← ptMap_comp_iota hpb hι, ptMap_one hpb hι]
    exact h2
  · intro k _ _ s hs
    change s ≫ x.left = s ≫ T.hom ≫ torsZeroL A' at hs
    apply h3 k s
    change s ≫ x.left ≫ h = s ≫ (T.hom ≫ g) ≫ torsZeroL A
    have e := torsZero_comp_h hpb hι (T := T)
    simp only [Category.assoc] at hs e ⊢
    rw [← e, ← Category.assoc, hs]
    simp only [Category.assoc]

/-- Frames: `P' ↦ h ∘ P'`, from `F_{A'/S',5}` to `(Over.map g)^* F_{A/S,5}`. -/
def frameMap (hpb : IsPullback h A'.F.hom A.F.hom g) (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a) :
    Frames5 A' ⟶ (Over.map g).op ⋙ Frames5 A where
  app T := ↾fun P => ⟨ptMap hpb P.1, isGen_of_fibre hpb hι (M := 5) (P' := P.1.left) P.2⟩
  naturality T T' f := by
    ext P
    apply Subtype.ext
    apply Over.OverMorphism.ext
    change (f.unop.left ≫ P.1.left) ≫ h = f.unop.left ≫ P.1.left ≫ h
    exact Category.assoc _ _ _

/-- `V15`-points: `x ↦ h ∘ x`, from `V15_{A'}` to `(Over.map g)^* V15_A`. -/
def v15Map (hpb : IsPullback h A'.F.hom A.F.hom g) (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a) :
    (V15Sub A').toFunctor ⟶ (Over.map g).op ⋙ (V15Sub A).toFunctor where
  app T := ↾fun x => ⟨ptMap hpb x.1, ptMap_mem_v15Sub hpb hι x.1 x.2⟩
  naturality T T' f := by
    ext x
    apply Subtype.ext
    apply Over.OverMorphism.ext
    change (f.unop.left ≫ x.1.left) ≫ h = f.unop.left ≫ x.1.left ≫ h
    exact Category.assoc _ _ _

theorem v15Map_app_bijective (hpb : IsPullback h A'.F.hom A.F.hom g)
    (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a) (T : (Over S')ᵒᵖ) :
    Function.Bijective ((v15Map hpb hι).app T) := by
  refine ⟨fun x y hxy => Subtype.ext (ptMap_injective hpb (congrArg Subtype.val hxy)), ?_⟩
  rintro ⟨y, hy⟩
  have hy' : ptMap hpb (ptLift hpb y) ∈ (V15Sub A).obj (op ((Over.map g).obj T.unop)) := by
    rw [ptMap_ptLift]
    exact hy
  exact ⟨⟨ptLift hpb y, mem_v15Sub_of_ptMap hpb hι _ hy'⟩, Subtype.ext (ptMap_ptLift hpb y)⟩

/-- The `V15` transport is an isomorphism of presheaves on `S'`-schemes. -/
def v15Iso (hpb : IsPullback h A'.F.hom A.F.hom g) (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a) :
    (V15Sub A').toFunctor ≅ (Over.map g).op ⋙ (V15Sub A).toFunctor :=
  haveI : ∀ T, IsIso ((v15Map hpb hι).app T) := fun T =>
    (isIso_iff_bijective _).2 (v15Map_app_bijective hpb hι T)
  haveI : IsIso (v15Map hpb hι) := NatIso.isIso_of_isIso_app _
  asIso (v15Map hpb hι)

/-- Orbits: the frame transport is `H`-equivariant. -/
def orbMap (hpb : IsPullback h A'.F.hom A.F.hom g) (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a) :
    Orbits5 A' ⟶ (Over.map g).op ⋙ Orbits5 A where
  app T := ↾(Quot.map (fun P => (frameMap hpb hι).app T P) (by
    rintro P P' ⟨δ, hδ, hP⟩
    refine ⟨δ, hδ, ?_⟩
    show ptMap hpb P'.1 = ptMap hpb P.1 ≫ iotaO A (Y3OrderMod.σ δ)
    rw [hP, ptMap_comp_iota hpb hι]))
  naturality T T' f := by
    ext q
    induction q using Quot.ind with
    | mk P =>
      apply congrArg (Quot.mk (OrbRel A ((Over.map g).op.obj T')))
      apply Subtype.ext
      apply Over.OverMorphism.ext
      change (f.unop.left ≫ P.1.left) ≫ h = f.unop.left ≫ P.1.left ≫ h
      exact Category.assoc _ _ _

end Transport

/-! ## 2. The canonical isomorphism `ψ_h` -/

/-- `(Over.map g)^* F_{A/S,H}` is an étale sheaf on `S'`-schemes (`Over.map g` is continuous). -/
theorem levelPre_map_isSheaf {S S' : Scheme.{0}} (g : S' ⟶ S) (A : FEC S) :
    Presheaf.IsSheaf (etaleOver S') ((Over.map g).op ⋙ LevelPre A) :=
  Functor.op_comp_isSheaf (Over.map g) (etaleOver S') (etaleOver S)
    ((presheafToSheaf (etaleOver S) (Type 1)).obj (Orbits5 A ⋙ uliftFunctor.{1, 0}))

section Psi

variable {S S' : Scheme.{0}} {A : FEC S} {A' : FEC S'} {g : S' ⟶ S}
  {h : A'.F.left ⟶ A.F.left}

/-- The canonical `ψ_h : F_{A'/S',H} ≅ (Over.map g)^* F_{A/S,H}`: through `levelIso` on both
sides it is the `V15` transport `x ↦ h ∘ x`. -/
def psiH (hpb : IsPullback h A'.F.hom A.F.hom g) (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a)
    (hsh : Presheaf.IsSheaf (etaleOver S) ((V15Sub A).toFunctor ⋙ uliftFunctor.{1, 0}))
    [Presheaf.IsLocallyInjective (etaleOver S) (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0})]
    [Presheaf.IsLocallySurjective (etaleOver S)
      (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0})]
    (hsh' : Presheaf.IsSheaf (etaleOver S') ((V15Sub A').toFunctor ⋙ uliftFunctor.{1, 0}))
    [Presheaf.IsLocallyInjective (etaleOver S')
      (Functor.whiskerRight (invOrb A') uliftFunctor.{1, 0})]
    [Presheaf.IsLocallySurjective (etaleOver S')
      (Functor.whiskerRight (invOrb A') uliftFunctor.{1, 0})] :
    LevelPre A' ≅ (Over.map g).op ⋙ LevelPre A :=
  levelIso A' hsh' ≪≫ Functor.isoWhiskerRight (v15Iso hpb hι) uliftFunctor.{1, 0} ≪≫
    (Functor.isoWhiskerLeft (Over.map g).op (levelIso A hsh)).symm

variable (hpb : IsPullback h A'.F.hom A.F.hom g) (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a)
    (hsh : Presheaf.IsSheaf (etaleOver S) ((V15Sub A).toFunctor ⋙ uliftFunctor.{1, 0}))
    [Presheaf.IsLocallyInjective (etaleOver S) (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0})]
    [Presheaf.IsLocallySurjective (etaleOver S)
      (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0})]
    (hsh' : Presheaf.IsSheaf (etaleOver S') ((V15Sub A').toFunctor ⋙ uliftFunctor.{1, 0}))
    [Presheaf.IsLocallyInjective (etaleOver S')
      (Functor.whiskerRight (invOrb A') uliftFunctor.{1, 0})]
    [Presheaf.IsLocallySurjective (etaleOver S')
      (Functor.whiskerRight (invOrb A') uliftFunctor.{1, 0})]

theorem levelIso_psiH_hom (T : Over S') (z : (LevelPre A').obj (op T)) :
    (levelIso A hsh).hom.app (op ((Over.map g).obj T)) ((psiH hpb hι hsh hsh').hom.app (op T) z) =
      ULift.up ((v15Map hpb hι).app (op T) ((levelIso A' hsh').hom.app (op T) z).down) := by
  let w : ((V15Sub A).toFunctor ⋙ uliftFunctor.{1, 0}).obj (op ((Over.map g).obj T)) :=
    ULift.up ((v15Map hpb hι).app (op T) ((levelIso A' hsh').hom.app (op T) z).down)
  exact Iso.inv_hom_id_app_apply (levelIso A hsh) (op ((Over.map g).obj T)) w

/-- The first clause of `LevelFibre` for `ψ_h`: compatibility with `P' ↦ h ∘ P'` on frames. -/
theorem psiH_frame (T : Over S') (P' : (Frames5 A').obj (op T))
    (P : (Frames5 A).obj (op ((Over.map g).obj T))) (hP : P.1.left = P'.1.left ≫ h) :
    (psiH hpb hι hsh hsh').hom.app (op T)
        ((toSheafify (etaleOver S') (Orbits5 A' ⋙ uliftFunctor.{1, 0})).app (op T)
          (ULift.up (Quot.mk _ P'))) =
      (toSheafify (etaleOver S) (Orbits5 A ⋙ uliftFunctor.{1, 0})).app (op ((Over.map g).obj T))
        (ULift.up (Quot.mk _ P)) := by
  apply levelIso_app_injective A hsh (op ((Over.map g).obj T))
  rw [levelIso_psiH_hom hpb hι hsh hsh' T, levelIso_toSheafify A' hsh' T P',
    levelIso_toSheafify A hsh ((Over.map g).obj T) P]
  apply congrArg ULift.up
  apply Subtype.ext
  apply Over.OverMorphism.ext
  change (P'.1.left ≫ A'.iota f5) ≫ h = P.1.left ≫ A.iota f5
  rw [hP, Category.assoc, Category.assoc, hι]

/-- Uniqueness of `ψ_h`: a morphism compatible with the frame transport is `ψ_h`. -/
theorem psiH_unique (ψ : LevelPre A' ⟶ (Over.map g).op ⋙ LevelPre A)
    (hψ : ∀ (T : Over S') (P' : (Frames5 A').obj (op T))
      (P : (Frames5 A).obj (op ((Over.map g).obj T))), P.1.left = P'.1.left ≫ h →
        ψ.app (op T) ((toSheafify (etaleOver S') (Orbits5 A' ⋙ uliftFunctor.{1, 0})).app (op T)
            (ULift.up (Quot.mk _ P'))) =
          (toSheafify (etaleOver S) (Orbits5 A ⋙ uliftFunctor.{1, 0})).app
            (op ((Over.map g).obj T)) (ULift.up (Quot.mk _ P))) :
    ψ = (psiH hpb hι hsh hsh').hom := by
  refine sheafify_hom_ext (etaleOver S') ψ _ (levelPre_map_isSheaf g A) ?_
  ext ⟨T⟩ ⟨q⟩
  induction q using Quot.ind with
  | mk P' =>
    exact (hψ T P' ((frameMap hpb hι).app (op T) P') rfl).trans
      (psiH_frame hpb hι hsh hsh' T P' ((frameMap hpb hι).app (op T) P') rfl).symm

/-- `ψ_h` is the morphism `sheafifyLift` induces from the frame transport. -/
theorem psiH_hom_eq_sheafifyLift :
    (psiH hpb hι hsh hsh').hom = sheafifyLift (etaleOver S')
      (Functor.whiskerRight (orbMap hpb hι) uliftFunctor.{1, 0} ≫
        Functor.whiskerLeft (Over.map g).op
          (toSheafify (etaleOver S) (Orbits5 A ⋙ uliftFunctor.{1, 0})))
      (levelPre_map_isSheaf g A) := by
  apply sheafifyLift_unique
  ext ⟨T⟩ ⟨q⟩
  induction q using Quot.ind with
  | mk P' => exact psiH_frame hpb hι hsh hsh' T P' ((frameMap hpb hι).app (op T) P') rfl

/-! ## 3. The characterization of `LevelFibre` -/

theorem psiH_unit_left (α' : LevelStr A') :
    ((levelIso A hsh).hom.app (op ((Over.map g).obj (Over.mk (𝟙 S'))))
      ((psiH hpb hι hsh hsh').hom.app (op (Over.mk (𝟙 S'))) α')).down.1.left =
        (Φ A' hsh' α').1.left ≫ h := by
  rw [levelIso_psiH_hom]
  rfl

include hsh in
theorem levelIso_map_unit_left (α : LevelStr A) :
    ((levelIso A hsh).hom.app (op ((Over.map g).obj (Over.mk (𝟙 S'))))
      ((LevelPre A).map (Over.homMk (U := (Over.map g).obj (Over.mk (𝟙 S'))) (V := Over.mk (𝟙 S))
        g (by simp)).op α)).down.1.left = g ≫ (Φ A hsh α).1.left := by
  rw [NatTrans.naturality_apply]
  rfl

/-- The second clause of `LevelFibre` for `ψ_h`, in terms of `Φ`. -/
theorem psiH_unit_iff (α : LevelStr A) (α' : LevelStr A') :
    (psiH hpb hι hsh hsh').hom.app (op (Over.mk (𝟙 S'))) α' =
        (LevelPre A).map (Over.homMk (U := (Over.map g).obj (Over.mk (𝟙 S'))) (V := Over.mk (𝟙 S))
          g (by simp)).op α ↔
      (Φ A' hsh' α').1.left ≫ h = g ≫ (Φ A hsh α).1.left := by
  constructor
  · intro e
    rw [← psiH_unit_left hpb hι hsh hsh', ← levelIso_map_unit_left hsh (g := g), e]
  · intro e
    apply levelIso_app_injective A hsh (op ((Over.map g).obj (Over.mk (𝟙 S'))))
    apply ULift.ext
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact (psiH_unit_left hpb hι hsh hsh' α').trans
      (e.trans (levelIso_map_unit_left hsh (g := g) α).symm)

end Psi

/-- **Base change of level structures.** For a cartesian `O`-linear square `h` over `g`, the
third bullet of the morphisms of `X^D(U)` holds iff `h` carries the `V15`-point of `α'` to the
restriction along `g` of the `V15`-point of `α`. -/
theorem levelFibre_iff {S S' : Scheme.{0}} {A : FEC S} {A' : FEC S'} {g : S' ⟶ S}
    {h : A'.F.left ⟶ A.F.left} (hpb : IsPullback h A'.F.hom A.F.hom g)
    (hι : ∀ a, A'.iota a ≫ h = h ≫ A.iota a)
    (hsh : Presheaf.IsSheaf (etaleOver S) ((V15Sub A).toFunctor ⋙ uliftFunctor.{1, 0}))
    [Presheaf.IsLocallyInjective (etaleOver S) (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0})]
    [Presheaf.IsLocallySurjective (etaleOver S)
      (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0})]
    (hsh' : Presheaf.IsSheaf (etaleOver S') ((V15Sub A').toFunctor ⋙ uliftFunctor.{1, 0}))
    [Presheaf.IsLocallyInjective (etaleOver S')
      (Functor.whiskerRight (invOrb A') uliftFunctor.{1, 0})]
    [Presheaf.IsLocallySurjective (etaleOver S')
      (Functor.whiskerRight (invOrb A') uliftFunctor.{1, 0})]
    (α : LevelStr A) (α' : LevelStr A') :
    LevelFibre A α g A' α' h ↔ (Φ A' hsh' α').1.left ≫ h = g ≫ (Φ A hsh α).1.left := by
  constructor
  · rintro ⟨ψ, h1, h2⟩
    rw [psiH_unique hpb hι hsh hsh' ψ.hom h1] at h2
    exact (psiH_unit_iff hpb hι hsh hsh' α α').1 h2
  · intro e
    exact ⟨psiH hpb hι hsh hsh', fun T P' P hP => psiH_frame hpb hι hsh hsh' T P' P hP,
      (psiH_unit_iff hpb hι hsh hsh' α α').2 e⟩

end Y3Buzzard.XDV15
