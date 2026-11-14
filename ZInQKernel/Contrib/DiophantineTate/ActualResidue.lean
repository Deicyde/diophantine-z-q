import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Residue fields of valuation subrings of algebraically closed fields

The residue field of any valuation subring of an algebraically closed field is
algebraically closed. The proof lifts a monic polynomial along the actual residue
quotient, finds a root in the ambient field, and uses integral closure to put
that same root in the valuation subring before reducing it.

There is no discrete-valuation, Noetherian, Henselian or residue-closure premise.
The underlying valuation subring and residue quotient are not replaced.

AI-assisted proof development; the algebraic APIs are from the pinned Mathlib.
-/

namespace DiophantineTate.ActualResidue

/-- Lift a monic polynomial through a surjective homomorphism, preserving both degrees. -/
theorem monic_lift_of_surjective
    {R S : Type*} [Semiring R] [Semiring S] [Nontrivial S]
    (f : R →+* S) (hf : Function.Surjective f)
    (p : Polynomial S) (hp : p.Monic) :
    ∃ q : Polynomial R,
      q.map f = p ∧ q.degree = p.degree ∧
      q.natDegree = p.natDegree ∧ q.Monic := by
  obtain ⟨q, hmap, hdeg, hmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective hf p) hp
  exact ⟨q, hmap, hdeg,
    Polynomial.natDegree_eq_of_degree_eq hdeg, hmonic⟩

/-- A root in the ambient field of a monic polynomial over `V` belongs to `V`. -/
theorem monic_root_mem
    {Ω : Type} [Field Ω] (V : ValuationSubring Ω)
    (f : Polynomial V) (hf : f.Monic) (x : Ω)
    (hx : (f.map V.subtype).IsRoot x) : x ∈ V := by
  letI : IsIntegrallyClosed V :=
    Valuation.Integers.isIntegrallyClosed (ValuationRing.integers V Ω)
  have hsubtype : algebraMap V Ω = V.subtype := by
    ext a
    rfl
  have hint : IsIntegral V x := by
    refine ⟨f, hf, ?_⟩
    rw [hsubtype, Polynomial.eval₂_eq_eval_map]
    exact hx.eq_zero
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  change (y : Ω) = x at hy
  exact hy ▸ y.property

/-- Every nonconstant monic polynomial over the actual residue field has a root. -/
theorem monic_residue_root
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (V : ValuationSubring Ω)
    (p : Polynomial (IsLocalRing.ResidueField V))
    (hp : p.Monic) (hdegree : p.degree ≠ 0) :
    ∃ z : IsLocalRing.ResidueField V, p.eval z = 0 := by
  obtain ⟨f, hred, hdeg, _, hmonic⟩ :=
    monic_lift_of_surjective (IsLocalRing.residue V)
      (IsLocalRing.residue_surjective (R := V)) p hp
  have hd : (f.map V.subtype).degree ≠ 0 := by
    rw [hmonic.degree_map V.subtype, hdeg]
    exact hdegree
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (k := Ω) (f.map V.subtype) hd
  let y : V := ⟨x, monic_root_mem V f hmonic x hx⟩
  have hy : f.eval y = 0 := by
    apply V.subtype_injective
    rw [map_zero, ← Polynomial.eval_map_apply (p := f) V.subtype y]
    change (f.map V.subtype).eval x = 0
    exact hx.eq_zero
  refine ⟨IsLocalRing.residue V y, ?_⟩
  calc
    p.eval (IsLocalRing.residue V y) =
        (f.map (IsLocalRing.residue V)).eval (IsLocalRing.residue V y) := by
      rw [hred]
    _ = IsLocalRing.residue V (f.eval y) :=
      Polynomial.eval_map_apply (p := f) (IsLocalRing.residue V) y
    _ = 0 := by rw [hy, map_zero]

/-- The residue field of a valuation subring of an algebraically closed field is closed. -/
theorem isAlgClosed_residueField
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (V : ValuationSubring Ω) :
    IsAlgClosed (IsLocalRing.ResidueField V) := by
  refine IsAlgClosed.of_exists_root (IsLocalRing.ResidueField V) ?_
  intro p hp hirr
  exact monic_residue_root V p hp
    (ne_of_gt (Polynomial.degree_pos_of_irreducible hirr))

end DiophantineTate.ActualResidue
