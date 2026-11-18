import ToricBaseChange.EtaleKernelVanishingV002
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# From points to morphisms: a morphism into an unramified scheme landing on a section is the section

`eq_section_of_range_subset`: for `f : P → S` formally unramified and locally of finite type with a
section `e`, a morphism `y : T → P` whose image lies in `e(S)` equals `(y ≫ f) ≫ e`. Proof: the
diagonal `Δ : P → P ×_S P` is an open immersion; `γ = (𝟙, f ≫ e) : P → P ×_S P` satisfies
`e ≫ γ = e ≫ Δ`, so `y ≫ γ` lands in the image of `Δ` and factors through it; projecting gives
`y = (y ≫ f) ≫ e`.

`kernel_morphism_trivial`: with `P`, `P'` étale over an irreducible `S` (`P` separated), sections
`e`, `e'`, a morphism `v : P → P'` with trivial generic kernel on points (`hgen`): every `T`-point `y`
of `P` with `y ≫ v = (y ≫ f) ≫ e'` (killed by `v`) is the unit `(y ≫ f) ≫ e`. Applied to the
`m`-torsion of the two models and the comparison (with `T = Spec Ω` over the closed point) this is
the triviality of the special-fibre `m`-torsion kernel.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology

namespace ToricBaseChange.Vanishing

universe u

variable {S P P' : Scheme.{u}}

/-- A morphism into a formally unramified `S`-scheme of finite type whose image lies on a section
factors through the section. -/
theorem eq_section_of_range_subset (f : P ⟶ S) [FormallyUnramified f] [LocallyOfFiniteType f]
    (e : S ⟶ P) (he : e ≫ f = 𝟙 S) {T : Scheme.{u}} (y : T ⟶ P)
    (hy : Set.range y ⊆ Set.range e) : y = (y ≫ f) ≫ e := by
  let γ : P ⟶ pullback f f := pullback.lift (𝟙 P) (f ≫ e) (by rw [Category.assoc, he]; simp)
  have hγe : e ≫ γ = e ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · simp [γ]
    · simp only [γ, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
      rw [← Category.assoc, he, Category.id_comp]
  have hrange : Set.range (y ≫ γ) ⊆ Set.range (pullback.diagonal f) := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨s, hs⟩ := hy ⟨a, rfl⟩
    refine ⟨e s, ?_⟩
    rw [Scheme.Hom.comp_apply, ← hs, ← Scheme.Hom.comp_apply, ← hγe, Scheme.Hom.comp_apply]
  obtain ⟨z, hz⟩ : ∃ z : T ⟶ P, z ≫ pullback.diagonal f = y ≫ γ :=
    ⟨IsOpenImmersion.lift (pullback.diagonal f) (y ≫ γ) hrange,
      IsOpenImmersion.lift_fac _ _ _⟩
  have h1 : y = z := by
    have := congrArg (· ≫ pullback.fst f f) hz
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, γ, pullback.lift_fst] at this
    exact this.symm
  have h2 : (y ≫ f) ≫ e = z := by
    have := congrArg (· ≫ pullback.snd f f) hz
    simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, γ, pullback.lift_snd] at this
    rw [Category.assoc]
    exact this.symm
  rw [h2]
  exact h1

/-- **The kernel of `v` on `T`-points is trivial**, from triviality on generic points. -/
theorem kernel_morphism_trivial [IrreducibleSpace S] (f : P ⟶ S) [Etale f] [IsSeparated f]
    (f' : P' ⟶ S) [Etale f'] (e : S ⟶ P) (he : e ≫ f = 𝟙 S) (e' : S ⟶ P') (he' : e' ≫ f' = 𝟙 S)
    (v : P ⟶ P')
    (hgen : ∀ x : P, f x = genericPoint S → v x ∈ Set.range e' → x ∈ Set.range e)
    {T : Scheme.{u}} (y : T ⟶ P) (hy : y ≫ v = (y ≫ f) ≫ e') : y = (y ≫ f) ≫ e := by
  obtain ⟨hfl, hfu, hlfp⟩ := (Etale.iff_flat_and_formallyUnramified (f := f)).mp inferInstance
  haveI := hfl
  haveI := hfu
  haveI := hlfp
  apply eq_section_of_range_subset f e he y
  rintro _ ⟨a, rfl⟩
  apply kernel_subset_section f f' e he e' he' v hgen
  refine ⟨f (y a), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hy,
    Category.assoc]

end ToricBaseChange.Vanishing
