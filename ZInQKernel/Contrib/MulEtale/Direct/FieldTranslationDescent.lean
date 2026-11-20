/-
Multiplication-etale construction: FieldTranslationDescent.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.JacobsonSpace

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace H101DirectFieldRoute.Translation

universe u

/-! ### 1. `[m]` intertwines the actual translations of a commutative group object -/

section Intertwining

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]

omit [BraidedCategory C] in
/-- Precomposition is multiplicative on powers in `Hom(X, M)`: `h ≫ (f ^ n) = (h ≫ f) ^ n`.
(Local, explicitly parenthesised form, used to avoid any `≫`/`^` parsing ambiguity at the call
sites below; the native `MonObj.comp_pow` is a genuine Mathlib lemma.) -/
theorem comp_pow_hom {X Y M : C} [MonObj M] (h : Y ⟶ X) (f : X ⟶ M) (n : ℕ) :
    h ≫ (f ^ n) = (h ≫ f) ^ n := by
  induction n with
  | zero => rw [_root_.pow_zero, _root_.pow_zero, MonObj.comp_one]
  | succ n ih => rw [_root_.pow_succ, _root_.pow_succ, MonObj.comp_mul, ih]

omit [BraidedCategory C] in
/-- The actual translation `mulRight x` is `𝟙 * (toUnit ≫ x)` in the monoid `Hom(G, G)`. -/
theorem mulRight_hom_eq_mul {G : C} [GrpObj G] (x : 𝟙_ C ⟶ G) :
    (GrpObj.mulRight x).hom = 𝟙 G * (toUnit G ≫ x) :=
  -- both sides are `lift (𝟙 G) (toUnit G ≫ x) ≫ μ` (definition of `mulRight`, `Hom.mul_def`)
  rfl

/-- **`[m]` intertwines translations.** For a commutative group object, translating by `x` and then
raising to the `m`-th power equals raising to the `m`-th power and then translating by `x ^ m`.
This is the group-homomorphism property of `[m]`, computed on the actual Hom-monoid. -/
theorem mulRight_hom_comp_pow_id {G : C} [GrpObj G] [IsCommMonObj G] (x : 𝟙_ C ⟶ G) (m : ℕ) :
    (GrpObj.mulRight x).hom ≫ (𝟙 G ^ m) = (𝟙 G ^ m) ≫ (GrpObj.mulRight (x ^ m)).hom := by
  rw [mulRight_hom_eq_mul, mulRight_hom_eq_mul]
  have h1 : (𝟙 G * (toUnit G ≫ x)) ≫ (𝟙 G ^ m) = (𝟙 G ^ m) * (toUnit G ≫ (x ^ m)) := by
    rw [comp_pow_hom (𝟙 G * (toUnit G ≫ x)) (𝟙 G) m, Category.comp_id, _root_.mul_pow,
      comp_pow_hom (toUnit G) x m]
  have h2 : (𝟙 G ^ m) ≫ (𝟙 G * (toUnit G ≫ (x ^ m))) = (𝟙 G ^ m) * (toUnit G ≫ (x ^ m)) := by
    rw [MonObj.comp_mul (𝟙 G ^ m) (𝟙 G) (toUnit G ≫ (x ^ m)), Category.comp_id,
      ← Category.assoc, comp_toUnit]
  rw [h1, h2]

/-- Inverse form of `mulRight_hom_comp_pow_id`. -/
theorem mulRight_inv_comp_pow_id {G : C} [GrpObj G] [IsCommMonObj G] (x : 𝟙_ C ⟶ G) (m : ℕ) :
    (GrpObj.mulRight x).inv ≫ (𝟙 G ^ m) = (𝟙 G ^ m) ≫ (GrpObj.mulRight (x ^ m)).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, mulRight_hom_comp_pow_id]

omit [BraidedCategory C] in
/-- The unit followed by the translation by `x` is `x`. -/
theorem one_comp_mulRight_hom {G : C} [GrpObj G] (x : 𝟙_ C ⟶ G) :
    η[G] ≫ (GrpObj.mulRight x).hom = x := by
  rw [mulRight_hom_eq_mul, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    toUnit_unique (η[G] ≫ toUnit G) (𝟙 _), Category.id_comp, MonObj.one_eq_one G, _root_.one_mul]

omit [BraidedCategory C] in
/-- `x` followed by the inverse translation is the unit. -/
theorem comp_mulRight_inv {G : C} [GrpObj G] (x : 𝟙_ C ⟶ G) :
    x ≫ (GrpObj.mulRight x).inv = η[G] := by
  rw [Iso.comp_inv_eq, one_comp_mulRight_hom]

end Intertwining

/-! ### 2. Étale neighbourhoods are transported by intertwining isomorphisms -/

/-- If isomorphisms `φ ψ` of `X` intertwine `f` (`φ ≫ f = f ≫ ψ`) and `U` is an open with
`Etale (U.ι ≫ f)` containing `φ y`, then `φ ⁻¹ᵁ U` is an open containing `y` with the same
property. -/
theorem exists_etale_nbhd_of_intertwine {X : Scheme.{u}} (f φ ψ : X ⟶ X) [IsIso φ] [IsIso ψ]
    (hφψ : φ ≫ f = f ≫ ψ) (y : X) (U : X.Opens) (hU : φ y ∈ U) (hUf : Etale (U.ι ≫ f)) :
    ∃ V : X.Opens, y ∈ V ∧ Etale (V.ι ≫ f) := by
  refine ⟨φ ⁻¹ᵁ U, (Scheme.Hom.mem_preimage _).mpr hU, ?_⟩
  have e : (φ ⁻¹ᵁ U).ι ≫ f ≫ ψ = (φ ∣_ U) ≫ U.ι ≫ f := by
    rw [← hφψ, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  have h1 : Etale ((φ ∣_ U) ≫ U.ι ≫ f) := by
    have : Etale (U.ι ≫ f) := hUf
    infer_instance
  rw [← e, ← Category.assoc] at h1
  -- cancel the isomorphism `ψ` by composing with the étale isomorphism `inv ψ`
  have h2 : Etale ((((φ ⁻¹ᵁ U).ι ≫ f) ≫ ψ) ≫ inv ψ) := by
    have : Etale (((φ ⁻¹ᵁ U).ι ≫ f) ≫ ψ) := h1
    infer_instance
  simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using h2

/-! ### 3. Over an algebraically closed field: translation to every closed point -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Over an algebraically closed field, an actual étale open neighbourhood of the unit point for
`[m] = (𝟙 G ^ m).left` makes `[m]` étale.  `G` is the actual commutative group object; every
closed point is an `Ω`-point, translation moves the unit neighbourhood there, and the union of
the étale opens contains all closed points of the Jacobson scheme `G.left`. -/
theorem etale_pow_id_left_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K]
    (G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G] [LocallyOfFiniteType G.hom] (m : ℕ)
    (s : Spec (.of K)) (V : G.left.Opens) (hsV : η[G].left s ∈ V)
    (hV : Etale (V.ι ≫ (𝟙 G ^ m : G ⟶ G).left)) :
    Etale ((𝟙 G ^ m : G ⟶ G).left) := by
  have hs : s = IsLocalRing.closedPoint K := Subsingleton.elim (α := Spec (.of K)) _ _
  subst hs
  -- every closed point has an étale open neighbourhood, by translation from the unit
  have hclosed : ∀ (x : G.left) (hxc : x ∈ closedPoints G.left),
      ∃ W : G.left.Opens, x ∈ W ∧ Etale (W.ι ≫ (𝟙 G ^ m : G ⟶ G).left) := by
    intro x hxc
    let x' : 𝟙_ (Over (Spec (.of K))) ⟶ G :=
      Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hxc⟩).2
    have hx' : x'.left (IsLocalRing.closedPoint K) = x := by
      -- `pointEquivClosedPoint p = ⟨p.1 (closedPoint K), _⟩` by definition
      have h := congrArg Subtype.val ((pointEquivClosedPoint G.hom).apply_symm_apply ⟨x, hxc⟩)
      exact h
    have hpt : (GrpObj.mulRight x').inv.left x = η[G].left (IsLocalRing.closedPoint K) := by
      rw [← hx', ← Scheme.Hom.comp_apply, ← Over.comp_left, comp_mulRight_inv]
    have hφψ : (GrpObj.mulRight x').inv.left ≫ (𝟙 G ^ m : G ⟶ G).left =
        (𝟙 G ^ m : G ⟶ G).left ≫ (GrpObj.mulRight (x' ^ m)).inv.left := by
      have h := congrArg (fun t : G ⟶ G ↦ t.left) (mulRight_inv_comp_pow_id x' m)
      simpa only [Over.comp_left] using h
    exact exists_etale_nbhd_of_intertwine _ _ _ hφψ x V (hpt ▸ hsV) hV
  -- the union of the étale opens is everything (Jacobson + closed points)
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  have hE : (⨆ W : {W : G.left.Opens // Etale (W.ι ≫ (𝟙 G ^ m : G ⟶ G).left)}, W.1) = ⊤ := by
    rw [← TopologicalSpace.Opens.coe_eq_univ, ← not_ne_iff, ← Set.nonempty_compl]
    intro H
    obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints H
      (⨆ W : {W : G.left.Opens // Etale (W.ι ≫ (𝟙 G ^ m : G ⟶ G).left)},
        W.1).2.isClosed_compl.isLocallyClosed
    obtain ⟨W, hxW, hW⟩ := hclosed x hxc
    exact hx (TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW⟩, hxW⟩)
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale)
    (fun W : {W : G.left.Opens // Etale (W.ι ≫ (𝟙 G ^ m : G ⟶ G).left)} ↦ W.1) hE (fun W ↦ W.2)

/-! ### 4. The actual base-change square of an `Over` morphism -/

/-- For `k : A ⟶ B` in `Over S` and `g : S' ⟶ S`, the native `Over.pullback g` image of `k`
sits in an actual pullback square over `k.left` (same construction as Mathlib's
`MorphismProperty.pullbackLift_fst_snd`). -/
theorem isPullback_overPullback_map_left {S S' : Scheme.{u}} (g : S' ⟶ S) {A B : Over S}
    (k : A ⟶ B) :
    IsPullback (pullback.fst A.hom g) ((Over.pullback g).map k).left k.left
      (pullback.fst B.hom g) := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback B.hom g)
  · -- `((Over.pullback g).obj B).hom` is `pullback.snd B.hom g` by definition of `Over.pullback`
    have e : ((Over.pullback g).map k).left ≫ pullback.snd B.hom g = pullback.snd A.hom g :=
      Over.w ((Over.pullback g).map k)
    rw [e, Over.w k]
    exact IsPullback.of_hasPullback A.hom g
  · -- `((Over.pullback g).map k).left` is `pullback.lift (pullback.fst _ _ ≫ k.left) (pullback.snd _ _) _`
    -- by definition of `Over.pullback`
    exact (pullback.lift_fst (pullback.fst A.hom g ≫ k.left) (pullback.snd A.hom g) _).symm

/-! ### 5. The field statement: transport, translate, descend -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Field multiplication is étale from an actual étale neighbourhood of the unit.**
For the ORIGINAL field `k` and group carrier `G` (smooth, proper, geometrically integral), an
actual open `V ∋ η[G].left s` with `Etale (V.ι ≫ (𝟙 G ^ m).left)` (exact output shape of
`LocalPromotion.exists_etale_open_mul_at_unit`) implies `Etale (𝟙 G ^ m).left`.  Valid for every
`m : ℕ`; no field or `m` restriction. -/
theorem etale_pow_id_left_of_etale_unit_nbhd {k : Type u} [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] [Smooth G.hom] [IsProper G.hom]
    [GeometricallyIntegral G.hom] (m : ℕ) (s : Spec (.of k))
    (H : ∃ V : G.left.Opens, IsAffineOpen V ∧ η[G].left s ∈ V ∧
      Etale (V.ι ≫ (𝟙 G ^ m : G ⟶ G).left)) :
    Etale ((𝟙 G ^ m : G ⟶ G).left) := by
  obtain ⟨V, -, hsV, hV⟩ := H
  let Ω : Type u := AlgebraicClosure k
  let g : Spec (.of Ω) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom <| algebraMap k Ω)
  let G' : Over (Spec (.of Ω)) := (Over.pullback g).obj G
  let : GrpObj G' := Functor.grpObjObj
  have : IsProper G'.hom := by dsimp [G']; infer_instance
  have : GeometricallyIntegral G'.hom := by dsimp [G']; infer_instance
  have : Smooth G'.hom := by dsimp [G']; infer_instance
  -- commutativity of the actual base-changed group, from native Mathlib
  have : IsCommMonObj G' := isCommMonObj_of_isProper_of_geometricallyIntegral G'
  -- the actual base change of `[m]` is `[m]` of `G'`
  have hpow : (Over.pullback g).map (𝟙 G ^ m) = (𝟙 G' ^ m : G' ⟶ G') := by
    have h : (Over.pullback g).map (𝟙 G ^ m) = ((Over.pullback g).map (𝟙 G)) ^ m :=
      map_pow ((Over.pullback g).homMonoidHom (X := G) (M := G)) (𝟙 G) m
    rw [CategoryTheory.Functor.map_id] at h
    exact h
  have sq := isPullback_overPullback_map_left g (𝟙 G ^ m)
  -- the unit neighbourhood transported to `G'`
  have hV' : Etale ((pullback.fst G.hom g ⁻¹ᵁ V).ι ≫ (𝟙 G' ^ m : G' ⟶ G').left) := by
    have big := ((isPullback_morphismRestrict (pullback.fst G.hom g) V).flip.paste_horiz
      sq.flip).flip
    rw [← hpow]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) big hV
  -- the unit point of `G'`, typed in the actual domain `(𝟙_ (Over (Spec Ω))).left` of `η[G'].left`
  let z : (𝟙_ (Over (Spec (.of Ω)))).left := IsLocalRing.closedPoint Ω
  have he' : η[G'].left z ∈ pullback.fst G.hom g ⁻¹ᵁ V := by
    rw [Scheme.Hom.mem_preimage]
    -- `η[G'] = ε ≫ (Over.pullback g).map η[G]` is the definition of `Functor.monObjObj`
    have hl : ((Over.pullback g).map η[G]).left ≫ pullback.fst G.hom g =
        pullback.fst (𝟙_ (Over (Spec (.of k)))).hom g ≫ η[G].left :=
      -- `((Over.pullback g).map η[G]).left` is the native `pullback.lift` of `Over.pullback`
      pullback.lift_fst _ _ _
    have h1 : η[G'].left ≫ pullback.fst G.hom g =
        (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
          pullback.fst (𝟙_ (Over (Spec (.of k)))).hom g ≫ η[G].left := by
      change (Functor.LaxMonoidal.ε (Over.pullback g) ≫ (Over.pullback g).map η[G]).left ≫
        pullback.fst G.hom g = _
      rw [Over.comp_left, Category.assoc, hl]
    have h2 : (η[G'].left ≫ pullback.fst G.hom g) z =
        ((Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
          pullback.fst (𝟙_ (Over (Spec (.of k)))).hom g ≫ η[G].left) z := by
      rw [h1]
    simp only [Scheme.Hom.comp_apply] at h2
    -- `Spec k` has exactly one point
    have hz : pullback.fst (𝟙_ (Over (Spec (.of k)))).hom g
        ((Functor.LaxMonoidal.ε (Over.pullback g)).left z) = s :=
      Subsingleton.elim (α := Spec (.of k)) _ _
    -- the actual image point is the actual unit point `η[G].left s`
    have h3 : pullback.fst G.hom g (η[G'].left z) = η[G].left s :=
      h2.trans (congrArg (fun p ↦ η[G].left p) hz)
    exact (congrArg (fun y ↦ y ∈ V) h3).mpr hsV
  -- étale over the algebraic closure, by translation
  have hG' : Etale (𝟙 G' ^ m : G' ⟶ G').left :=
    etale_pow_id_left_of_isAlgClosed G' m z _ he' hV'
  rw [← hpow] at hG'
  -- native fpqc descent along the actual faithfully flat base change
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq.flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hG'

end H101DirectFieldRoute.Translation
