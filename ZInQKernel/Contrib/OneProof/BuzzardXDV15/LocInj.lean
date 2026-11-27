import ZInQKernel.Contrib.OneProof.BuzzardXDV15.Defs
import Mathlib

/-!
# The orbit invariant is locally injective (bridge step B2)

Two frames `P, P'` over `T` with equal invariants `ι(1 - e5) P = ι(1 - e5) P'` factor through the
frame scheme `Z`, so `(P', P) : T ⟶ Z ×_S Z ≅ ∐_g Z`. Pulling back the coproduct inclusions
decomposes `T` into open pieces `T_g` covering `T` (a Zariski, hence étale, cover). On `T_g` we
have `P' = ι(σ g) P`. If `T_g` has a point, the annihilator clause of `IsGenAt` at a geometric
point turns `ι(1 - e5) P = ι((1 - e5) σ g) P` into `(1 - e5) g ≡ 1 - e5` modulo `5`, that is
`g ∈ H5`; so `P` and `P'` have the same orbit on `T_g`. Empty pieces are trivial.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj

namespace Y3Buzzard.XDV15

attribute [local instance] FEC.grp

/-- If a frame `x` over a scheme with a point `w` satisfies `ι(1 - e5) x = ι(1 - e5) ι(σ g) x`,
then `g ∈ H5`: at a geometric point over `w`, `ι((1 - e5) - (1 - e5) σ g)` kills the generator,
so `(1 - e5) - (1 - e5) σ g ∈ 5 O`. -/
theorem mem_H5_of_inv_eq {S : Scheme.{0}} (A : FEC S) {W : Scheme.{0}} {x : W ⟶ A.F.left}
    (hx : IsGen 5 A x) {g : Y3OrderMod.G 5}
    (h : x ≫ A.iota f5 = (x ≫ A.iota (Y3OrderMod.σ g)) ≫ A.iota f5) (w : W) : g ∈ H5 := by
  have hgen := hx.2 (geomK w) (geomPt w)
  set X : Over.mk (geomPt w ≫ x ≫ A.F.hom) ⟶ A.F :=
    Over.homMk (U := Over.mk (geomPt w ≫ x ≫ A.F.hom)) (geomPt w ≫ x)
      (Category.assoc _ _ _) with hX
  have hxy : X ≫ (Over.homMk (A.iota f5) (A.iota_over _) : A.F ⟶ A.F) =
      X ≫ (Over.homMk (A.iota (f5 * Y3OrderMod.σ g)) (A.iota_over _) : A.F ⟶ A.F) := by
    apply Over.OverMorphism.ext
    show (geomPt w ≫ x) ≫ A.iota f5 = (geomPt w ≫ x) ≫ A.iota (f5 * Y3OrderMod.σ g)
    rw [A.iota_mul, Category.assoc, h]
    simp only [Category.assoc]
  obtain ⟨b, hb⟩ := (hgen.1 _).1 (FrameTorsor.comp_iota_sub_eq_one A X hxy)
  have e := (Y3OrderMod.coe_eq_coe_iff (M := 5)).2 ⟨b, hb⟩
  rw [RingCon.coe_mul, Y3OrderMod.σ_spec] at e
  exact e.symm

/-- On the piece where `φ = (P', P)` lands in the `g`-component of the kernel pair,
`P' = ι(σ g) P`. -/
theorem comp_eq_on_piece {S : Scheme.{0}} (A : FEC S) {Z : Scheme.{0}} {i : Z ⟶ A.F.left}
    {ρ : Y3OrderMod.G 5 →* Aut Z}
    (hρ : ∀ g : Y3OrderMod.G 5, (ρ g).asIso.hom ≫ i = i ≫ A.iota (Y3OrderMod.σ g))
    {W V : Scheme.{0}} {φ : W ⟶ Y3QuotientDescent.actRel Z (Y3OrderMod.G 5)} {p p' : W ⟶ Z}
    (hS : φ ≫ Y3QuotientDescent.actS ρ = p')
    (hT : φ ≫ Y3QuotientDescent.actT Z (Y3OrderMod.G 5) = p)
    (g : Y3OrderMod.G 5) {j : V ⟶ W} {k : V ⟶ Z}
    (hjk : j ≫ φ = k ≫ Sigma.ι (fun _ : Y3OrderMod.G 5 => Z) g) :
    j ≫ p' ≫ i = (j ≫ p ≫ i) ≫ A.iota (Y3OrderMod.σ g) := by
  have h1 : j ≫ p' = k ≫ (ρ g).asIso.hom := by
    rw [← hS, ← Category.assoc, hjk, Category.assoc, Y3QuotientDescent.actS, Sigma.ι_comp_desc]
  have h2 : j ≫ p = k := by
    rw [← hT, ← Category.assoc, hjk, Category.assoc, Y3QuotientDescent.actT, Sigma.ι_comp_desc,
      Category.comp_id]
  calc j ≫ p' ≫ i = (j ≫ p') ≫ i := (Category.assoc _ _ _).symm
    _ = k ≫ (ρ g).asIso.hom ≫ i := by rw [h1, Category.assoc]
    _ = k ≫ i ≫ A.iota (Y3OrderMod.σ g) := by rw [hρ g]
    _ = (j ≫ p ≫ i) ≫ A.iota (Y3OrderMod.σ g) := by rw [← h2]; simp only [Category.assoc]

/-- A sieve on `T` in `S`-schemes containing the arrows of an étale cover of `T` is covering. -/
theorem mem_etaleOver_of_cover {X : Scheme.{0}} {T : Over X} (R : Sieve T)
    (𝒰 : Scheme.Cover.{0} (Scheme.precoverage @Etale) T.left)
    (h : ∀ i, R (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)) :
    R ∈ etaleOver X T := by
  rw [GrothendieckTopology.mem_over_iff]
  exact Scheme.mem_grothendieckTopology_iff.2
    ⟨𝒰, fun _ _ ⟨i⟩ => (Sieve.overEquiv_iff R (𝒰.f i)).2 (h i)⟩

/-- Two frames in one `H`-orbit after restriction along `f` have the same restricted orbit. -/
theorem orbits_map_mk_eq {S : Scheme.{0}} (A : FEC S) {T W : Over S} (f : W ⟶ T)
    (P P' : (Frames5 A).obj (op T)) (δ : Y3OrderMod.G 5) (hδ : δ ∈ H5)
    (h : f.left ≫ P'.1.left = (f.left ≫ P.1.left) ≫ A.iota (Y3OrderMod.σ δ)) :
    (Orbits5 A ⋙ uliftFunctor.{1, 0}).map f.op (ULift.up (Quot.mk _ P)) =
      (Orbits5 A ⋙ uliftFunctor.{1, 0}).map f.op (ULift.up (Quot.mk _ P')) := by
  have hr : OrbRel A (op W) ((Frames5 A).map f.op P) ((Frames5 A).map f.op P') :=
    ⟨δ, hδ, Over.OverMorphism.ext h⟩
  exact congrArg ULift.up (Quot.sound hr)

/-- Plan step B2: the orbit invariant `[P] ↦ ι(1 - e5) P` is locally injective for the étale
topology on `S`-schemes. -/
theorem invOrb_locallyInjective (hB25 : BuzzardFrameRepTorsor 5) (S : Over Z30Base)
    (A : FEC S.left) :
    Presheaf.IsLocallyInjective (etaleOver S.left)
      (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0}) := by
  obtain ⟨Z, i, -, -, -, -, hchar, ρ, hρ, hpb⟩ := hB25 S A
  constructor
  intro T x y hxy
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  induction x using Quot.ind with
  | mk P => ?_
  induction y using Quot.ind with
  | mk P' => ?_
  have h1 : (invFrame A).app T P = (invFrame A).app T P' := congrArg ULift.down hxy
  have hinv : P.1.left ≫ A.iota f5 = P'.1.left ≫ A.iota f5 :=
    congrArg (fun u : T.unop ⟶ A.F => u.left) (congrArg Subtype.val h1)
  obtain ⟨p, hp⟩ := (hchar T.unop.left P.1.left).2 P.2
  obtain ⟨p', hp'⟩ := (hchar T.unop.left P'.1.left).2 P'.2
  have hcond : p' ≫ i ≫ A.F.hom = p ≫ i ≫ A.F.hom := by
    have e1 : p ≫ i ≫ A.F.hom = T.unop.hom := by
      rw [← Category.assoc, hp]; exact Over.w P.1
    have e2 : p' ≫ i ≫ A.F.hom = T.unop.hom := by
      rw [← Category.assoc, hp']; exact Over.w P'.1
    rw [e1, e2]
  have hS : hpb.lift p' p hcond ≫ Y3QuotientDescent.actS ρ = p' := hpb.lift_fst _ _ _
  have hT : hpb.lift p' p hcond ≫ Y3QuotientDescent.actT Z (Y3OrderMod.G 5) = p :=
    hpb.lift_snd _ _ _
  let 𝒰 : Scheme.Cover.{0} (Scheme.precoverage @Etale) T.unop.left :=
    Scheme.Cover.mkOfCovers (Y3OrderMod.G 5)
      (fun g => pullback (hpb.lift p' p hcond) (Sigma.ι (fun _ : Y3OrderMod.G 5 => Z) g))
      (fun g => pullback.fst (hpb.lift p' p hcond) (Sigma.ι (fun _ : Y3OrderMod.G 5 => Z) g))
      (fun t => by
        obtain ⟨⟨g, z⟩, hz⟩ := (sigmaMk (fun _ : Y3OrderMod.G 5 => Z)).surjective
          (hpb.lift p' p hcond t)
        rw [sigmaMk_mk] at hz
        obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback t z hz.symm
        exact ⟨g, w, hw⟩)
  refine mem_etaleOver_of_cover _ 𝒰 (fun g => ?_)
  have E := comp_eq_on_piece A hρ hS hT g
    (pullback.condition (f := hpb.lift p' p hcond) (g := Sigma.ι (fun _ : Y3OrderMod.G 5 => Z) g))
  rw [hp, hp'] at E
  by_cases hne : Nonempty (𝒰.X g)
  · obtain ⟨w⟩ := hne
    refine orbits_map_mk_eq A _ P P' g ?_ E
    refine mem_H5_of_inv_eq A (isGen_comp A (pullback.fst (hpb.lift p' p hcond)
      (Sigma.ι (fun _ : Y3OrderMod.G 5 => Z) g)) P.2) ?_ w
    rw [← E, Category.assoc, Category.assoc, hinv]
  · have : IsEmpty (𝒰.X g) := not_nonempty_iff.1 hne
    exact orbits_map_mk_eq A _ P P' 1 H5.one_mem ((isInitialOfIsEmpty (X := 𝒰.X g)).hom_ext _ _)

end Y3Buzzard.XDV15
