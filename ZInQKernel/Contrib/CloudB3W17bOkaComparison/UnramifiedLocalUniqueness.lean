import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Actual open-diagonal uniqueness over a local spectrum

A finite-type formally unramified algebraic target has an open diagonal.
Two maps from a genuine local spectrum which agree after a map through its
closed point and agree over the base must be equal.  The proof factors the
actual pair through the actual open diagonal: an open containing the closed
point of a local spectrum is the whole spectrum.  No completion, Henselianity,
Krull-intersection premise or GAGA statement is used.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- The genuine open algebraic diagonal gives uniqueness from a closed-point agreement
on a local spectrum. This is an auxiliary theorem, not an algebraicity premise. -/
theorem formallyUnramified_localSpec_ext
    {R : Type} [CommRing R] [IsLocalRing R] {T X Y : Scheme}
    (s : X ⟶ Y) [FormallyUnramified s] [LocallyOfFiniteType s]
    (f g : Spec (CommRingCat.of R) ⟶ X) (w : f ≫ s = g ≫ s)
    (p : T ⟶ Spec (CommRingCat.of R)) (t : T)
    (hp : p t = IsLocalRing.closedPoint R) (h : p ≫ f = p ≫ g) : f = g := by
  let d := pullback.lift f g w
  let δ := pullback.diagonal s
  have hd : p ≫ d = (p ≫ f) ≫ δ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id, d, δ]
    · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, d, δ]
      exact h.symm
  have hcp : d (IsLocalRing.closedPoint R) = δ ((p ≫ f) t) := by
    rw [← hp]
    exact congrArg (fun m : T ⟶ pullback s s => m t) hd
  have hmem : d (IsLocalRing.closedPoint R) ∈ δ.opensRange := ⟨(p ≫ f) t, hcp.symm⟩
  have htop : d ⁻¹ᵁ δ.opensRange = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem d hmem
  have hrange : Set.range d ⊆ Set.range δ := by
    rintro _ ⟨u, rfl⟩
    change u ∈ d ⁻¹ᵁ δ.opensRange
    rw [htop]
    trivial
  let l := IsOpenImmersion.lift δ d hrange
  have hl : l ≫ δ = d := IsOpenImmersion.lift_fac δ d hrange
  have hf : l = f := by
    have H := congrArg (fun m : Spec (CommRingCat.of R) ⟶ pullback s s =>
      m ≫ pullback.fst s s) hl
    simpa only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst, d, δ] using H
  have hg : l = g := by
    have H := congrArg (fun m : Spec (CommRingCat.of R) ⟶ pullback s s =>
      m ≫ pullback.snd s s) hl
    simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd, d, δ] using H
  exact hf.symm.trans hg

end ZInQ.Contrib.CloudB3W17bOkaComparison
