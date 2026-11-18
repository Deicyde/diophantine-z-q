import HenselDivision.EtaleResidueLiftV005
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Sections of étale schemes over a henselian local ring

Let `R` be a henselian local ring with residue field `k`, and `p : X → Spec R` an étale morphism of
schemes (no finiteness, no separatedness, no quasi-compactness). Every `k`-point of the closed
fibre, i.e. every `x : Spec k → X` over `Spec R`, extends to a unique section `s : Spec R → X` of
`p` (EGA IV 18.5.11, Stacks 04GG). The proof chooses an affine open `U ∋ x`, notes that any
section through `x` lands in `U` (the closed point of `Spec R` maps into `U`, so the whole local
scheme does), and applies the algebraic Hensel lifting for the étale `R`-algebra `Γ(X, U)`.

Applied to a quasi-finite étale torsion scheme `G[n]` this is the integral/residual torsion
comparison: it uses only the closed fibre and never asserts that `G[n]` is finite, so it applies to
Néron models with toric part, whose torsion schemes have generic points that do not specialize.

Edition V004: the closed-point membership step is a term-level equality chain; statements as
in V001.
-/

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace HenselDivision

universe u

/-- The closed point `Spec k → Spec R` of a local ring. -/
noncomputable def closedPt (R : Type u) [CommRing R] [IsLocalRing R] :
    Spec (CommRingCat.of (ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))

lemma closedPt_closedPoint (R : Type u) [CommRing R] [IsLocalRing R] :
    closedPt R (closedPoint (CommRingCat.of (ResidueField R))) =
      closedPoint (CommRingCat.of R) := by
  have : IsLocalHom (CommRingCat.ofHom (algebraMap R (ResidueField R))).hom := by
    rw [CommRingCat.hom_ofHom, ResidueField.algebraMap_eq]; infer_instance
  exact Spec_closedPoint

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

/-- **Hensel lifting of points of étale schemes.** -/
theorem etale_section_existsUnique {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) [Etale p]
    (x : Spec (CommRingCat.of (ResidueField R)) ⟶ X) (hx : x ≫ p = closedPt R) :
    ∃! s : Spec (CommRingCat.of R) ⟶ X, s ≫ p = 𝟙 _ ∧ closedPt R ≫ s = x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x (closedPoint (CommRingCat.of (ResidueField R))))) isOpen_univ
  replace hU : IsAffineOpen U := hU
  have hrange : ∀ {T : CommRingCat.{u}} [IsLocalRing T] (f : Spec T ⟶ X),
      f (closedPoint T) ∈ U → Set.range f ⊆ Set.range hU.fromSpec := by
    intro T _ f hf
    rintro _ ⟨y, rfl⟩
    rw [hU.range_fromSpec]
    have hy : y ∈ f ⁻¹ᵁ U := by
      rw [Scheme.preimage_eq_top_of_closedPoint_mem f hf]; trivial
    exact hy
  -- the étale ring map `R → Γ(X, U)`
  let θ : CommRingCat.of R ⟶ Γ(X, U) := Spec.preimage (hU.fromSpec ≫ p)
  have hθ : Spec.map θ = hU.fromSpec ≫ p := Spec.map_preimage _
  have hθe : θ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hθ]; infer_instance
  letI : Algebra R Γ(X, U) := θ.hom.toAlgebra
  have : Algebra.Etale R Γ(X, U) := hθe
  -- the residue point as an `R`-algebra map `Γ(X, U) → k`
  let x' : Spec (CommRingCat.of (ResidueField R)) ⟶ Spec Γ(X, U) :=
    IsOpenImmersion.lift hU.fromSpec x (hrange x hxU)
  have hx' : x' ≫ hU.fromSpec = x := IsOpenImmersion.lift_fac _ _ _
  let ψ0 : Γ(X, U) ⟶ CommRingCat.of (ResidueField R) := Spec.preimage x'
  have hψ0 : Spec.map ψ0 = x' := Spec.map_preimage _
  have hcompat : θ ≫ ψ0 = CommRingCat.ofHom (algebraMap R (ResidueField R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ0, hθ, ← Category.assoc, hx', hx]
    rfl
  let ψ : Γ(X, U) →ₐ[R] ResidueField R :=
    { ψ0.hom with
      commutes' := fun r => by
        have h := congrArg (fun h => h.hom r) hcompat
        exact h }
  obtain ⟨φ, hφ, huniq⟩ := etale_existsUnique_lift (R := R) (S := Γ(X, U)) ψ
  let φc : Γ(X, U) ⟶ CommRingCat.of R := CommRingCat.ofHom φ.toRingHom
  have hθφ : θ ≫ φc = 𝟙 _ := by
    apply CommRingCat.hom_ext
    ext r
    exact φ.commutes r
  have hφres : φc ≫ CommRingCat.ofHom (algebraMap R (ResidueField R)) = ψ0 := by
    apply CommRingCat.hom_ext
    ext a
    exact AlgHom.congr_fun hφ a
  refine ⟨Spec.map φc ≫ hU.fromSpec, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, ← hθ, ← Spec.map_comp, hθφ, Spec.map_id]
  · rw [closedPt, ← Category.assoc, ← Spec.map_comp, hφres, hψ0, hx']
  · rintro s ⟨hs1, hs2⟩
    have key : s (closedPoint (CommRingCat.of R)) =
        x (closedPoint (CommRingCat.of (ResidueField R))) := by
      have h0 := Scheme.Hom.comp_apply (closedPt R) s
        (closedPoint (CommRingCat.of (ResidueField R)))
      rw [hs2] at h0
      have e := congrArg s (closedPt_closedPoint R)
      exact e.symm.trans h0.symm
    have hspt : s (closedPoint (CommRingCat.of R)) ∈ U := by
      rw [key]; exact hxU
    let s' := IsOpenImmersion.lift hU.fromSpec s (hrange s hspt)
    have hs' : s' ≫ hU.fromSpec = s := IsOpenImmersion.lift_fac _ _ _
    let φ0 : Γ(X, U) ⟶ CommRingCat.of R := Spec.preimage s'
    have hφ0 : Spec.map φ0 = s' := Spec.map_preimage _
    have hθφ0 : θ ≫ φ0 = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ0, hθ, ← Category.assoc, hs', hs1, Spec.map_id]
    have hres0 : φ0 ≫ CommRingCat.ofHom (algebraMap R (ResidueField R)) = ψ0 := by
      apply Spec.map_injective
      rw [Spec.map_comp, hψ0, hφ0]
      apply (cancel_mono hU.fromSpec).mp
      rw [Category.assoc, hs', hx']
      exact hs2
    let φ0a : Γ(X, U) →ₐ[R] R :=
      { φ0.hom with
        commutes' := fun r => by
          have h := congrArg (fun h => h.hom r) hθφ0
          exact h }
    have hφ0a : (resₐ R).comp φ0a = ψ := by
      ext a
      have h := congrArg (fun h => h.hom a) hres0
      exact h
    have heq : φ0a = φ := huniq φ0a hφ0a
    have hφ0c : φ0 = φc := by
      apply CommRingCat.hom_ext
      ext a
      exact AlgHom.congr_fun heq a
    rw [← hs', ← hφ0, hφ0c]

/-- **Restriction of sections to the closed fibre is bijective** for étale `X → Spec R`. -/
theorem etale_section_restrict_bijective {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    [Etale p] :
    Function.Bijective (fun s : {s : Spec (CommRingCat.of R) ⟶ X // s ≫ p = 𝟙 _} =>
      (⟨closedPt R ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩ :
        {x : Spec (CommRingCat.of (ResidueField R)) ⟶ X // x ≫ p = closedPt R})) := by
  constructor
  · rintro ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ h
    have h' : closedPt R ≫ s₁ = closedPt R ≫ s₂ := congrArg Subtype.val h
    obtain ⟨s, -, hs⟩ := etale_section_existsUnique p (closedPt R ≫ s₁)
      (by rw [Category.assoc, h₁, Category.comp_id])
    have e1 := hs s₁ ⟨h₁, rfl⟩
    have e2 := hs s₂ ⟨h₂, h'.symm⟩
    exact Subtype.ext (e1.trans e2.symm)
  · rintro ⟨x, hx⟩
    obtain ⟨s, ⟨hs1, hs2⟩, -⟩ := etale_section_existsUnique p x hx
    exact ⟨⟨s, hs1⟩, Subtype.ext hs2⟩

end HenselDivision

#check @HenselDivision.etale_section_existsUnique
#check @HenselDivision.etale_section_restrict_bijective
#print axioms HenselDivision.etale_section_existsUnique
#print axioms HenselDivision.etale_section_restrict_bijective
