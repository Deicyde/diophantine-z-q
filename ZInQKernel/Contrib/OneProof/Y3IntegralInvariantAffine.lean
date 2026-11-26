import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Invariant affine neighborhoods from affine orbit neighborhoods

This restates, without the curve-specific construction of affine neighborhoods, the
finite-intersection argument of `Y3InvariantAffine.lean` (which does not import this file). The
affine intersection step is the separated-over-affine case of Stacks, Tag 01KP (the lemma number
is not checked against a recorded reading).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Y3IntegralDescent

/-- An affine open containing a finite orbit in a scheme separated over an affine base
contains an invariant affine neighborhood of the point. No freeness is needed. -/
theorem exists_invariant_affineOpen_le_of_contains_orbit
    {S X : Scheme} (f : X ⟶ S) [IsAffine S] [IsSeparated f]
    {G : Type*} [Group G] [Finite G] (ρ : G →* Aut X)
    (x : X) (V : X.Opens) (hV : IsAffineOpen V)
    (hOrbit : ∀ g : G, (ρ g).asIso.hom x ∈ V) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ V ∧
      ∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ U = U := by
  classical
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let U : X.Opens := ⨅ g : G, (ρ g).asIso.hom ⁻¹ᵁ V
  refine ⟨U, IsAffineOpen.iInf (fun g => hV.preimage (ρ g).asIso.hom), ?_, ?_, ?_⟩
  · change x ∈ (U : Set X)
    rw [Opens.coe_iInf, Set.mem_iInter]
    exact hOrbit
  · exact (iInf_le (fun g : G => (ρ g).asIso.hom ⁻¹ᵁ V) (1 : G)).trans (by simp)
  · intro h
    ext y
    change ((ρ h).asIso.hom y ∈ (U : Set X)) ↔ y ∈ (U : Set X)
    rw [Opens.coe_iInf, Set.mem_iInter, Set.mem_iInter]
    change (∀ g, (ρ g).asIso.hom ((ρ h).asIso.hom y) ∈ V) ↔
      ∀ g, (ρ g).asIso.hom y ∈ V
    have hcomp (g : G) : (ρ g).asIso.hom ((ρ h).asIso.hom y) =
        (ρ (g * h)).asIso.hom y := by rw [map_mul]; rfl
    simp only [hcomp]
    constructor
    · intro hy g
      simpa only [inv_mul_cancel_right] using hy (g * h⁻¹)
    · exact fun hy g => hy (g * h)

end Y3IntegralDescent
