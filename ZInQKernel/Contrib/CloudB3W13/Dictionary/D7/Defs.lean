/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.InterfaceD6D7

/-!
# W13 dictionary D7: definitions shared by the D7 files

* `L3 S`: the FLT objects `WithFullLevel Λ 1 3 S`.
* `IsLevelPB φ u v g`: `g : v.A ⟶ u.A` exhibits `v` as the base change of `u` along `φ`. The
  square over `Spec φ` is a pullback, and `g` respects the group law, the action and the level
  point.
* The three mathematical inputs of the D7 construction, stated as `Prop`s:
  - `BCInput`: base change exists;
  - `RigidInput`: rigidity of level-3 automorphisms;
  - `DimInput`: relative dimension 2 over rings.
  Each one is proved from FLT source theorems in its own file (`BaseChange.lean`, `Rigid.lean`,
  `Dim.lean`). The final theorem `d7_obligation` takes none of them as a hypothesis.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D7

open CategoryTheory AlgebraicGeometry Limits
open scoped Quaternion
open ZInQ.Contrib.CloudW03NeronSurj ZInQ.Contrib.CloudW03NeronSurj.FLT
open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian
open ZInQ.Contrib.CloudW03NeronSurj.FLT.CerednikDrinfeld.QM
open ZInQ.Contrib.CloudB2Shimura.Dictionary

/-- FLT objects of the moduli problem `(Λ, N = 1, m = 3)` over a ring. -/
abbrev L3 (S : Type) [CommRing S] : Type 1 := FakeEllipticCurve.WithFullLevel Λ 1 3 S

/-- Base change of level-3 objects exists (proved in `BaseChange.lean`). -/
def BCInput : Prop :=
  ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (u : L3 S),
    ∃ u' : L3 S', FakeEllipticCurve.WithFullLevel.IsPullback φ u u'

/-- Rigidity of level-3 objects over rings in which `3` is a unit (the FLT theorem
`WithFullLevel.eq_refl_of_mapPt_eq_of_three_le`, specialised in `Rigid.lean`). -/
def RigidInput : Prop :=
  ∀ (S : Type) [CommRing S], IsUnit ((3 : ℕ) : S) → ∀ (u : L3 S) (e : u.1.A ≅ u.1.A)
    (he : e.hom ≫ u.1.f = u.1.f),
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = u.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) →
    (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u.1.act x) →
    mapPt e.hom he u.2.P = u.2.P → e = Iso.refl u.1.A

/-- Fake elliptic curves over any ring are smooth of relative dimension `2` (proved in
`Dim.lean`). -/
def DimInput : Prop :=
  ∀ (R : Type) [CommRing R] (E : FakeEllipticCurve Λ 1 R), SmoothOfRelativeDimension 2 E.f

/-- `g : v.A ⟶ u.A` exhibits `v` as the base change of `u` along `φ`, respecting the group law,
the action and the level point. -/
def IsLevelPB {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (u : L3 S) (v : L3 S')
    (g : v.1.A ⟶ u.1.A) : Prop :=
  IsPullback g v.1.f u.1.f (Spec.map (CommRingCat.ofHom φ)) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (t' : T ⟶ Spec (CommRingCat.of S))
      (_ : t ≫ Spec.map (CommRingCat.ofHom φ) = t') (P Q : SchemeHomOver t v.1.f)
      (P' Q' : SchemeHomOver t' u.1.f), P'.1 = P.1 ≫ g → Q'.1 = Q.1 ≫ g →
        (v.1.L.mul t P Q).1 ≫ g = (u.1.L.mul t' P' Q').1) ∧
    (∀ x : ↥Λ, v.1.act x ≫ g = g ≫ u.1.act x) ∧
    (v.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1

section Lemmas

variable {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S'']

lemma isLevelPB_congr {φ φ' : S →+* S'} {u : L3 S} {v : L3 S'} {g : v.1.A ⟶ u.1.A}
    (h : IsLevelPB φ u v g) (hφ : φ = φ') : IsLevelPB φ' u v g := by
  subst hφ; exact h

/-- A base change in the sense of the FLT `WithFullLevel.IsPullback` gives a level pullback. -/
lemma exists_isLevelPB_of_isPullback {φ : S →+* S'} {u : L3 S} {v : L3 S'}
    (h : FakeEllipticCurve.WithFullLevel.IsPullback φ u v) : ∃ g, IsLevelPB φ u v g := by
  obtain ⟨g, hg, hmul, hact, -, hP⟩ := h
  refine ⟨g, hg, ?_, hact, hP⟩
  intro T t t' ht P Q P' Q' hP' hQ'
  subst ht
  have e1 : P' = ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩ := Subtype.ext hP'
  have e2 : Q' = ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩ := Subtype.ext hQ'
  rw [e1, e2]
  exact hmul t P Q

/-- The identity is a level pullback along the identity. -/
lemma isLevelPB_id (u : L3 S) : IsLevelPB (RingHom.id S) u u (𝟙 u.1.A) := by
  have hSpec : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by
    rw [show CommRingCat.ofHom (RingHom.id S) = 𝟙 (CommRingCat.of S) from rfl, Spec.map_id]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hSpec]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · intro T t t' ht P Q P' Q' hP' hQ'
    rw [hSpec, Category.comp_id] at ht
    subst ht
    have e1 : P' = P := Subtype.ext (hP'.trans (Category.comp_id _))
    have e2 : Q' = Q := Subtype.ext (hQ'.trans (Category.comp_id _))
    rw [e1, e2, Category.comp_id]
  · intro x; simp
  · rw [hSpec]; simp

/-- An FLT isomorphism is a level pullback along the identity. -/
lemma isLevelPB_of_iso {u v : L3 S} (e : u.1.A ≅ v.1.A) (he : e.hom ≫ v.1.f = u.1.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = v.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (hact : ∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ v.1.act x)
    (hP : mapPt e.hom he u.2.P = v.2.P) : IsLevelPB (RingHom.id S) v u e.hom := by
  have hSpec : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by
    rw [show CommRingCat.ofHom (RingHom.id S) = 𝟙 (CommRingCat.of S) from rfl, Spec.map_id]
  refine ⟨?_, ?_, hact, ?_⟩
  · rw [hSpec]
    exact IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
  · intro T t t' ht P Q P' Q' hP' hQ'
    rw [hSpec, Category.comp_id] at ht
    subst ht
    have e1 : P' = mapPt e.hom he P := Subtype.ext hP'
    have e2 : Q' = mapPt e.hom he Q := Subtype.ext hQ'
    rw [e1, e2, ← hmul]
    rfl
  · rw [hSpec, Category.id_comp]
    exact congrArg Subtype.val hP

/-- Level pullbacks compose. -/
lemma IsLevelPB.comp {φ : S →+* S'} {ψ : S' →+* S''} {u : L3 S} {v : L3 S'} {w : L3 S''}
    {g : v.1.A ⟶ u.1.A} {g' : w.1.A ⟶ v.1.A} (h : IsLevelPB φ u v g) (h' : IsLevelPB ψ v w g') :
    IsLevelPB (ψ.comp φ) u w (g' ≫ g) := by
  have hSpec : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  obtain ⟨hg, hmul, hact, hP⟩ := h
  obtain ⟨hg', hmul', hact', hP'⟩ := h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hSpec]
    exact hg'.paste_horiz hg
  · intro T t t'' ht P Q P'' Q'' hP'' hQ''
    have hw : ∀ X : SchemeHomOver t w.1.f, (X.1 ≫ g') ≫ v.1.f = t ≫ Spec.map (CommRingCat.ofHom ψ) :=
      fun X => by rw [Category.assoc, hg'.w, ← Category.assoc, X.2]
    rw [← Category.assoc, hmul' t _ rfl P Q ⟨P.1 ≫ g', hw P⟩ ⟨Q.1 ≫ g', hw Q⟩ rfl rfl]
    refine hmul _ t'' ?_ _ _ P'' Q'' ?_ ?_
    · rw [← ht, hSpec, Category.assoc]
    · rw [hP'', Category.assoc]
    · rw [hQ'', Category.assoc]
  · intro x
    rw [← Category.assoc, hact', Category.assoc, hact, Category.assoc]
  · rw [← Category.assoc, hP', Category.assoc, hP, ← Category.assoc, hSpec]

/-- **Uniqueness of level pullbacks** (from rigidity). -/
lemma IsLevelPB.unique (hR : RigidInput) {φ : S →+* S'} {u : L3 S} {v : L3 S'}
    (h3 : IsUnit ((3 : ℕ) : S')) {g₁ g₂ : v.1.A ⟶ u.1.A} (h₁ : IsLevelPB φ u v g₁)
    (h₂ : IsLevelPB φ u v g₂) : g₁ = g₂ := by
  obtain ⟨hg₁, hmul₁, hact₁, hP₁⟩ := h₁
  obtain ⟨hg₂, hmul₂, hact₂, hP₂⟩ := h₂
  let e : v.1.A ⟶ v.1.A := hg₂.lift g₁ v.1.f hg₁.w
  let e' : v.1.A ⟶ v.1.A := hg₁.lift g₂ v.1.f hg₂.w
  have he₁ : e ≫ g₂ = g₁ := hg₂.lift_fst _ _ _
  have he₂ : e ≫ v.1.f = v.1.f := hg₂.lift_snd _ _ _
  have he'₁ : e' ≫ g₁ = g₂ := hg₁.lift_fst _ _ _
  have he'₂ : e' ≫ v.1.f = v.1.f := hg₁.lift_snd _ _ _
  have hee' : e ≫ e' = 𝟙 _ := hg₁.hom_ext (by rw [Category.assoc, he'₁, he₁, Category.id_comp])
    (by rw [Category.assoc, he'₂, he₂, Category.id_comp])
  have he'e : e' ≫ e = 𝟙 _ := hg₂.hom_ext (by rw [Category.assoc, he₁, he'₁, Category.id_comp])
    (by rw [Category.assoc, he₂, he'₂, Category.id_comp])
  let E : v.1.A ≅ v.1.A := ⟨e, e', hee', he'e⟩
  have hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t v.1.f),
      mapPt E.hom he₂ (v.1.L.mul t P Q) = v.1.L.mul t (mapPt E.hom he₂ P) (mapPt E.hom he₂ Q) := by
    intro T t P Q
    have hw : ∀ X : SchemeHomOver t v.1.f, (X.1 ≫ g₁) ≫ u.1.f = t ≫ Spec.map (CommRingCat.ofHom φ) :=
      fun X => by rw [Category.assoc, hg₁.w, ← Category.assoc, X.2]
    apply Subtype.ext
    refine hg₂.hom_ext ?_ ?_
    · change ((v.1.L.mul t P Q).1 ≫ e) ≫ g₂ = (v.1.L.mul t (mapPt E.hom he₂ P) (mapPt E.hom he₂ Q)).1 ≫ g₂
      rw [Category.assoc, he₁, hmul₁ t _ rfl P Q ⟨P.1 ≫ g₁, hw P⟩ ⟨Q.1 ≫ g₁, hw Q⟩ rfl rfl,
        hmul₂ t _ rfl _ _ ⟨P.1 ≫ g₁, hw P⟩ ⟨Q.1 ≫ g₁, hw Q⟩]
      · change P.1 ≫ g₁ = (P.1 ≫ e) ≫ g₂
        rw [Category.assoc, he₁]
      · change Q.1 ≫ g₁ = (Q.1 ≫ e) ≫ g₂
        rw [Category.assoc, he₁]
    · rw [(mapPt E.hom he₂ (v.1.L.mul t P Q)).2, (v.1.L.mul t _ _).2]
  have hact : ∀ x : ↥Λ, v.1.act x ≫ E.hom = E.hom ≫ v.1.act x := by
    intro x
    refine hg₂.hom_ext ?_ ?_
    · change (v.1.act x ≫ e) ≫ g₂ = (e ≫ v.1.act x) ≫ g₂
      rw [Category.assoc, he₁, hact₁, Category.assoc, hact₂, ← Category.assoc, he₁]
    · change (v.1.act x ≫ e) ≫ v.1.f = (e ≫ v.1.act x) ≫ v.1.f
      rw [Category.assoc, he₂, v.1.act_over, Category.assoc, v.1.act_over, he₂]
  have hP : mapPt E.hom he₂ v.2.P = v.2.P := by
    apply Subtype.ext
    refine hg₂.hom_ext ?_ ?_
    · change (v.2.P.1 ≫ e) ≫ g₂ = v.2.P.1 ≫ g₂
      rw [Category.assoc, he₁, hP₁, hP₂]
    · change (v.2.P.1 ≫ e) ≫ v.1.f = v.2.P.1 ≫ v.1.f
      rw [Category.assoc, he₂]
  have hE := hR S' h3 v E he₂ hmul hact hP
  have : e = 𝟙 _ := congrArg Iso.hom hE
  rw [← he₁, this, Category.id_comp]

end Lemmas

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D7
