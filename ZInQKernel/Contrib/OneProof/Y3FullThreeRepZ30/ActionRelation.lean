import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Limits

/-!
# The relation of a finite group action on a scheme

For a group `G` acting on a scheme `X` through `ρ : G →* Aut X`, the relation scheme
is `∐ (_ : G), X`, with the action leg `Sigma.desc fun g => (ρ g).asIso.hom` and the
projection leg `Sigma.desc fun _ => 𝟙 X`. The action leg is the projection leg
precomposed with an automorphism of the relation scheme, so finiteness, flatness and
local finite presentation pass from the projection leg to the action leg. For finite
`G`, the relation is an equivalence relation on `T`-points: transitivity uses the
fibre product of the two legs, computed by finitary extensivity.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace Y3QuotientDescent

open AlgebraicGeometry

variable {X : Scheme.{u}} {G : Type u} [Group G] (ρ : G →* Aut X)

/-- The relation scheme: one copy of `X` for each group element. -/
noncomputable abbrev actRel (X : Scheme.{u}) (G : Type u) : Scheme.{u} :=
  ∐ fun _ : G => X

/-- The projection leg. -/
noncomputable def actT (X : Scheme.{u}) (G : Type u) : actRel X G ⟶ X :=
  Sigma.desc fun _ => 𝟙 X

/-- The action leg. -/
noncomputable def actS : actRel X G ⟶ X :=
  Sigma.desc fun g => (ρ g).asIso.hom

/-- The componentwise action, an automorphism of the relation scheme. -/
noncomputable def twist : actRel X G ⟶ actRel X G :=
  Sigma.desc fun g => (ρ g).asIso.hom ≫ Sigma.ι (fun _ : G => X) g

/-- The inverse of `twist`. -/
noncomputable def untwist : actRel X G ⟶ actRel X G :=
  Sigma.desc fun g => (ρ g).asIso.inv ≫ Sigma.ι (fun _ : G => X) g

instance : IsIso (twist ρ) := by
  refine ⟨untwist ρ, ?_, ?_⟩
  · apply Sigma.hom_ext
    intro g
    simp [twist, untwist]
  · apply Sigma.hom_ext
    intro g
    simp [twist, untwist]

theorem actS_eq : actS ρ = twist ρ ≫ actT X G := by
  apply Sigma.hom_ext
  intro g
  simp [actS, actT, twist]

instance : Flat (actT X G) := by
  unfold actT
  infer_instance

theorem locallyOfFinitePresentation_actT : LocallyOfFinitePresentation (actT X G) := by
  haveI : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
  unfold actT
  exact IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

theorem flat_actS : Flat (actS ρ) := by
  rw [actS_eq]
  infer_instance

theorem locallyOfFinitePresentation_actS : LocallyOfFinitePresentation (actS ρ) := by
  have := locallyOfFinitePresentation_actT (X := X) (G := G)
  rw [actS_eq]
  infer_instance

theorem isFinite_actS [IsFinite (actT X G)] : IsFinite (actS ρ) := by
  rw [actS_eq]
  infer_instance

/-- Reflexivity of the action relation on `T`-points. -/
theorem rel_refl {T : Scheme.{u}} (x : T ⟶ X) :
    ∃ φ : T ⟶ actRel X G, φ ≫ actS ρ = x ∧ φ ≫ actT X G = x := by
  refine ⟨x ≫ Sigma.ι (fun _ : G => X) 1, ?_, ?_⟩
  · rw [Category.assoc, actS, Sigma.ι_desc, map_one]
    exact Category.comp_id x
  · rw [Category.assoc, actT, Sigma.ι_desc]
    exact Category.comp_id x

/-- Symmetry of the action relation on `T`-points. -/
theorem rel_symm {T : Scheme.{u}} (φ : T ⟶ actRel X G) :
    ∃ ψ : T ⟶ actRel X G, ψ ≫ actS ρ = φ ≫ actT X G ∧ ψ ≫ actT X G = φ ≫ actS ρ := by
  refine ⟨φ ≫ Sigma.desc fun g => (ρ g).asIso.hom ≫ Sigma.ι (fun _ : G => X) g⁻¹, ?_, ?_⟩
  · rw [Category.assoc]
    congr 1
    apply Sigma.hom_ext
    intro g
    rw [Sigma.ι_desc_assoc, Category.assoc, actS, Sigma.ι_desc, actT, Sigma.ι_desc,
      map_inv]
    exact (ρ g).asIso.hom_inv_id
  · rw [Category.assoc]
    congr 1
    apply Sigma.hom_ext
    intro g
    rw [Sigma.ι_desc_assoc, Category.assoc, actT, Sigma.ι_desc, Category.comp_id, actS,
      Sigma.ι_desc]

/-- The action law in the composition order used below. -/
theorem rho_mul_hom (g h : G) :
    (ρ (g * h)).asIso.hom = (ρ h).asIso.hom ≫ (ρ g).asIso.hom := by
  rw [map_mul]
  rfl

/-- Multiplication of composable relation elements, indexed by pairs of group
elements. -/
noncomputable def actMul :
    (∐ fun p : G × G => pullback (𝟙 X) (ρ p.2).asIso.hom) ⟶ actRel X G :=
  Sigma.desc fun p =>
    pullback.snd (𝟙 X) (ρ p.2).asIso.hom ≫ Sigma.ι (fun _ : G => X) (p.1 * p.2)

/-- The fibre product of the projection leg and the action leg, by finitary
extensivity. -/
theorem isPullback_actT_actS [Finite G] :
    IsPullback
      (Sigma.desc fun p : G × G =>
        pullback.fst (𝟙 X) (ρ p.2).asIso.hom ≫ Sigma.ι (fun _ : G => X) p.1)
      (Sigma.desc fun p : G × G =>
        pullback.snd (𝟙 X) (ρ p.2).asIso.hom ≫ Sigma.ι (fun _ : G => X) p.2)
      (actT X G) (actS ρ) :=
  FinitaryPreExtensive.isPullback_sigmaDesc (fun _ : G => 𝟙 X)
    (fun k : G => (ρ k).asIso.hom)

theorem actMul_actS :
    actMul ρ ≫ actS ρ = (Sigma.desc fun p : G × G =>
      pullback.fst (𝟙 X) (ρ p.2).asIso.hom ≫ Sigma.ι (fun _ : G => X) p.1) ≫
        actS ρ := by
  apply Sigma.hom_ext
  rintro ⟨g, k⟩
  simp only [actMul, actS, Sigma.ι_desc_assoc, Category.assoc, Sigma.ι_desc]
  rw [rho_mul_hom, ← Category.assoc, ← pullback.condition, Category.comp_id]

theorem actMul_actT :
    actMul ρ ≫ actT X G = (Sigma.desc fun p : G × G =>
      pullback.snd (𝟙 X) (ρ p.2).asIso.hom ≫ Sigma.ι (fun _ : G => X) p.2) ≫
        actT X G := by
  apply Sigma.hom_ext
  rintro ⟨g, k⟩
  simp only [actMul, actT, Sigma.ι_desc_assoc, Category.assoc, Sigma.ι_desc]

/-- Transitivity of the action relation on `T`-points. -/
theorem rel_trans [Finite G] {T : Scheme.{u}} (φ ψ : T ⟶ actRel X G)
    (h : φ ≫ actT X G = ψ ≫ actS ρ) :
    ∃ χ : T ⟶ actRel X G, χ ≫ actS ρ = φ ≫ actS ρ ∧ χ ≫ actT X G = ψ ≫ actT X G := by
  refine ⟨(isPullback_actT_actS ρ).lift φ ψ h ≫ actMul ρ, ?_, ?_⟩
  · rw [Category.assoc, actMul_actS, ← Category.assoc, IsPullback.lift_fst]
  · rw [Category.assoc, actMul_actT, ← Category.assoc, IsPullback.lift_snd]

/-- The action relation on `T`-points is an equivalence relation, in the form used by
the finite locally free quotient theorem. -/
theorem rel_equivalence [Finite G] (T : Scheme.{u}) :
    _root_.Equivalence fun x y : T ⟶ X =>
      ∃ φ : T ⟶ actRel X G, φ ≫ actS ρ = x ∧ φ ≫ actT X G = y := by
  refine ⟨fun x => rel_refl ρ x, ?_, ?_⟩
  · rintro x y ⟨φ, hs, ht⟩
    obtain ⟨ψ, h₁, h₂⟩ := rel_symm ρ φ
    exact ⟨ψ, h₁.trans ht, h₂.trans hs⟩
  · rintro x y z ⟨φ, hs, ht⟩ ⟨ψ, hs', ht'⟩
    obtain ⟨χ, h₁, h₂⟩ := rel_trans ρ φ ψ (ht.trans hs'.symm)
    exact ⟨χ, h₁.trans hs, h₂.trans ht'⟩


/-! ### Freeness gives joint monicity of the two legs -/

/-- One component of the decomposition: if a test map lands in copies i and j over
the same point, freeness forces agreement. -/
theorem rel_mono_component
    (hfree : ∀ g h : G, g ≠ h → ∀ {T : Scheme.{u}} (z : T ⟶ X),
      z ≫ (ρ g).asIso.hom = z ≫ (ρ h).asIso.hom → IsEmpty T)
    {T W : Scheme.{u}} (a b : T ⟶ actRel X G) (hs : a ≫ actS ρ = b ≫ actS ρ)
    (i j : G) (c : W ⟶ T) (z : W ⟶ X)
    (ha : c ≫ a = z ≫ Sigma.ι (fun _ : G => X) i)
    (hb : c ≫ b = z ≫ Sigma.ι (fun _ : G => X) j) :
    c ≫ a = c ≫ b := by
  by_cases hij : i = j
  · subst hij
    rw [ha, hb]
  · have h1 : c ≫ a ≫ actS ρ = c ≫ b ≫ actS ρ := by rw [hs]
    rw [← Category.assoc, ha, ← Category.assoc, hb, Category.assoc, Category.assoc,
      actS, Sigma.ι_desc, Sigma.ι_desc] at h1
    haveI := hfree i j hij z h1
    exact isInitialOfIsEmpty.hom_ext _ _

/-- Scheme-theoretic freeness of the action makes the two legs jointly monic. This is
the joint monicity hypothesis of the finite locally free quotient theorem. -/
theorem rel_mono [Finite G]
    (hfree : ∀ g h : G, g ≠ h → ∀ {T : Scheme.{u}} (z : T ⟶ X),
      z ≫ (ρ g).asIso.hom = z ≫ (ρ h).asIso.hom → IsEmpty T)
    {T : Scheme.{u}} (a b : T ⟶ actRel X G)
    (hs : a ≫ actS ρ = b ≫ actS ρ) (ht : a ≫ actT X G = b ≫ actT X G) : a = b := by
  have hP : IsPullback
      (Sigma.desc fun p : G × G =>
        pullback.fst (𝟙 X) (𝟙 X) ≫ Sigma.ι (fun _ : G => X) p.1)
      (Sigma.desc fun p : G × G =>
        pullback.snd (𝟙 X) (𝟙 X) ≫ Sigma.ι (fun _ : G => X) p.2)
      (actT X G) (actT X G) :=
    FinitaryPreExtensive.isPullback_sigmaDesc (fun _ : G => 𝟙 X) (fun _ : G => 𝟙 X)
  obtain ⟨ℓ, hℓ₁, hℓ₂⟩ : ∃ ℓ : T ⟶ ∐ fun _ : G × G => pullback (𝟙 X) (𝟙 X),
      ℓ ≫ (Sigma.desc fun p : G × G =>
        pullback.fst (𝟙 X) (𝟙 X) ≫ Sigma.ι (fun _ : G => X) p.1) = a ∧
      ℓ ≫ (Sigma.desc fun p : G × G =>
        pullback.snd (𝟙 X) (𝟙 X) ≫ Sigma.ι (fun _ : G => X) p.2) = b :=
    ⟨hP.lift a b ht, hP.lift_fst a b ht, hP.lift_snd a b ht⟩
  have hD : IsPullback
      (Sigma.desc fun p : (G × G) × PUnit.{u+1} =>
        pullback.fst (Sigma.ι (fun _ : G × G => pullback (𝟙 X) (𝟙 X)) p.1) ℓ ≫
          Sigma.ι (fun _ : G × G => pullback (𝟙 X) (𝟙 X)) p.1)
      (Sigma.desc fun p : (G × G) × PUnit.{u+1} =>
        pullback.snd (Sigma.ι (fun _ : G × G => pullback (𝟙 X) (𝟙 X)) p.1) ℓ ≫
          Sigma.ι (fun _ : PUnit.{u+1} => T) p.2)
      (Sigma.desc fun k : G × G => Sigma.ι (fun _ : G × G => pullback (𝟙 X) (𝟙 X)) k)
      (Sigma.desc fun _ : PUnit.{u+1} => ℓ) :=
    FinitaryPreExtensive.isPullback_sigmaDesc
      (fun k : G × G => Sigma.ι (fun _ : G × G => pullback (𝟙 X) (𝟙 X)) k)
      (fun _ : PUnit.{u+1} => ℓ)
  have hid : (Sigma.desc fun k : G × G =>
      Sigma.ι (fun _ : G × G => pullback (𝟙 X) (𝟙 X)) k) = 𝟙 _ := by
    apply Sigma.hom_ext
    intro k
    simp
  have hw : ℓ ≫ (Sigma.desc fun k : G × G =>
      Sigma.ι (fun _ : G × G => pullback (𝟙 X) (𝟙 X)) k) =
      Sigma.ι (fun _ : PUnit.{u+1} => T) PUnit.unit ≫ Sigma.desc fun _ : PUnit.{u+1} => ℓ := by
    rw [hid, Category.comp_id, Sigma.ι_desc]
  have hσ := hD.lift_snd ℓ (Sigma.ι (fun _ : PUnit.{u+1} => T) PUnit.unit) hw
  have hfs : pullback.fst (𝟙 X) (𝟙 X) = pullback.snd (𝟙 X) (𝟙 X) := by
    have h := (pullback.condition :
      pullback.fst (𝟙 X) (𝟙 X) ≫ 𝟙 X = pullback.snd (𝟙 X) (𝟙 X) ≫ 𝟙 X)
    rwa [Category.comp_id, Category.comp_id] at h
  have hcomp : ∀ k : G × G,
      pullback.snd (Sigma.ι (fun _ : G × G => pullback (𝟙 X) (𝟙 X)) k) ℓ ≫ a =
        pullback.snd (Sigma.ι (fun _ : G × G => pullback (𝟙 X) (𝟙 X)) k) ℓ ≫ b := by
    rintro ⟨i, j⟩
    refine rel_mono_component ρ hfree a b hs i j _
      (pullback.fst (Sigma.ι (fun _ : G × G => pullback (𝟙 X) (𝟙 X)) (i, j)) ℓ ≫
        pullback.fst (𝟙 X) (𝟙 X)) ?_ ?_
    · rw [← hℓ₁, ← pullback.condition_assoc]
      simp only [Category.assoc, Sigma.ι_desc]
    · rw [← hℓ₂, ← pullback.condition_assoc]
      simp only [Category.assoc, Sigma.ι_desc, hfs]
  have hfold : (hD.lift ℓ (Sigma.ι (fun _ : PUnit.{u+1} => T) PUnit.unit) hw ≫
      (Sigma.desc fun p : (G × G) × PUnit.{u+1} =>
        pullback.snd (Sigma.ι (fun _ : G × G => pullback (𝟙 X) (𝟙 X)) p.1) ℓ ≫
          Sigma.ι (fun _ : PUnit.{u+1} => T) p.2)) ≫
      (Sigma.desc fun _ : PUnit.{u+1} => 𝟙 T) = 𝟙 T := by
    rw [hσ, Sigma.ι_desc]
  have key : ((Sigma.desc fun p : (G × G) × PUnit.{u+1} =>
        pullback.snd (Sigma.ι (fun _ : G × G => pullback (𝟙 X) (𝟙 X)) p.1) ℓ ≫
          Sigma.ι (fun _ : PUnit.{u+1} => T) p.2) ≫
      (Sigma.desc fun _ : PUnit.{u+1} => 𝟙 T)) ≫ a =
      ((Sigma.desc fun p : (G × G) × PUnit.{u+1} =>
        pullback.snd (Sigma.ι (fun _ : G × G => pullback (𝟙 X) (𝟙 X)) p.1) ℓ ≫
          Sigma.ι (fun _ : PUnit.{u+1} => T) p.2) ≫
      (Sigma.desc fun _ : PUnit.{u+1} => 𝟙 T)) ≫ b := by
    apply Sigma.hom_ext
    rintro ⟨k, ⟨⟩⟩
    simp only [Category.assoc, Sigma.ι_desc_assoc, Sigma.ι_desc, Category.comp_id]
    exact hcomp k
  rw [← Category.id_comp a, ← Category.id_comp b, ← hfold]
  simp only [Category.assoc] at key ⊢
  rw [key]

end Y3QuotientDescent
