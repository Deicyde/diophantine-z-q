/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

New proof, not a port of an admitted or conditional NOS theorem.
Uses Mathlib's scheme-theoretic fibres, residue-field maps and open diagonals.
Modification/contribution notice (2026-11-14): isolated finite pointed-etale
neighbourhood overlap geometry for original-O good-model descent. This file
neither assumes nor claims effective descent or the original NOS theorem.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Gluing

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent

/-- If the entire scheme-theoretic fibre of `p` at `s` is a monomorphism
    to `Spec κ(s)`, every point of the self-overlap above `s` lies on the
    diagonal. Equality of topological points alone would not prove this:
    the proof compares the two actual residue-field-valued morphisms. -/
theorem mem_range_diagonal_of_mono_fibre
    {U S : Scheme.{u}} (p : U ⟶ S) (s : S)
    [Mono (p.fiberToSpecResidueField s)]
    (z : (pullback p p : Scheme.{u})) (hz : (pullback.fst p p ≫ p) z = s) :
    z ∈ Set.range (pullback.diagonal p) := by
  subst s
  let R : Scheme.{u} := pullback p p
  let b : R ⟶ S := pullback.fst p p ≫ p
  let q : Spec (R.residueField z) ⟶ R := R.fromSpecResidueField z
  let t : Spec (R.residueField z) ⟶ Spec (S.residueField (b z)) :=
    Spec.map (b.residueFieldMap z)
  have hb : q ≫ b = t ≫ S.fromSpecResidueField (b z) := by
    exact (b.SpecMap_residueFieldMap_fromSpecResidueField z).symm
  let a₁ : Spec (R.residueField z) ⟶ p.fiber (b z) :=
    pullback.lift (q ≫ pullback.fst p p) t (by simpa [b, Category.assoc] using hb)
  let a₂ : Spec (R.residueField z) ⟶ p.fiber (b z) :=
    pullback.lift (q ≫ pullback.snd p p) t (by
      rw [Category.assoc, ← pullback.condition]
      exact hb)
  have ha : a₁ = a₂ := by
    apply (cancel_mono (p.fiberToSpecResidueField (b z))).mp
    dsimp only [a₁, a₂, Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
    rw [pullback.lift_snd, pullback.lift_snd]
  have hq : q ≫ pullback.fst p p = q ≫ pullback.snd p p := by
    have ha' := congrArg (fun a => a ≫ p.fiberι (b z)) ha
    dsimp only [a₁, a₂, Scheme.Hom.fiberι, Scheme.Hom.fiber] at ha'
    simpa only [pullback.lift_fst] using ha'
  have hdiag : (q ≫ pullback.fst p p) ≫ pullback.diagonal p = q := by
    apply pullback.hom_ext
    · simp
    · simpa using hq
  let z₀ : Spec (R.residueField z) := default
  refine ⟨(q ≫ pullback.fst p p) z₀, ?_⟩
  have hval := congrArg (fun a : Spec (R.residueField z) ⟶ R => a z₀) hdiag
  simpa only [Scheme.Hom.comp_apply, q, Scheme.fromSpecResidueField_apply] using hval

/-- The actual finite-neighbourhood overlap cover used in henselization
    descent: diagonal plus generic open. The condition on the *whole fibre*,
    not merely a chosen point with equal residue field, is essential. It holds
    after shrinking a pointed etale neighbourhood to remove its other special
    points. It does not hold for arbitrary ramified DVR extensions. -/
theorem diagonal_sup_generic_eq_top
    {U S : Scheme.{u}} (p : U ⟶ S) [Etale p]
    (s : S) [Mono (p.fiberToSpecResidueField s)]
    (V : S.Opens) (hV : ∀ x : S, x ∉ V → x = s) :
    (pullback.diagonal p).opensRange ⊔
      (pullback.fst p p ≫ p) ⁻¹ᵁ V = ⊤ := by
  apply top_le_iff.mp
  intro z _
  change z ∈ Set.range (pullback.diagonal p) ∨
    (pullback.fst p p ≫ p) z ∈ V
  by_cases hz : (pullback.fst p p ≫ p) z ∈ V
  · exact Or.inr hz
  · exact Or.inl (mem_range_diagonal_of_mono_fibre p s z (hV _ hz))

/-- Pulling the overlap cover back along any test morphism gives the same
    two-open cover. This is the geometric input for natural transport and its
    triple-overlap cocycle, rather than an assumed descent datum. -/
theorem preimage_diagonal_sup_generic_eq_top
    {U S T : Scheme.{u}} (p : U ⟶ S) [Etale p]
    (s : S) [Mono (p.fiberToSpecResidueField s)]
    (V : S.Opens) (hV : ∀ x : S, x ∉ V → x = s)
    (q : T ⟶ pullback p p) :
    q ⁻¹ᵁ (pullback.diagonal p).opensRange ⊔
      (q ≫ pullback.fst p p ≫ p) ⁻¹ᵁ V = ⊤ := by
  apply top_le_iff.mp
  intro z _
  have hz : q z ∈ (pullback.diagonal p).opensRange ⊔
      (pullback.fst p p ≫ p) ⁻¹ᵁ V := by
    rw [diagonal_sup_generic_eq_top p s V hV]
    trivial
  exact hz

#print axioms mem_range_diagonal_of_mono_fibre
#print axioms diagonal_sup_generic_eq_top
#print axioms preimage_diagonal_sup_generic_eq_top

end ZInQ.Contrib.CloudR2NOS.GoodDescent
