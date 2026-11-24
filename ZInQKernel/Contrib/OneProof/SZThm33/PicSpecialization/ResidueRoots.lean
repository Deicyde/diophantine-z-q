import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

namespace ZInQ.ToricOrthogonality

/-- A prime-to-residue-characteristic root of unity over a local domain
is determined at the identity by its reduction. -/
theorem eq_one_of_residue_eq_one {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {n : ℕ} (hn : (n : IsLocalRing.ResidueField R) ≠ 0)
    {a : R} (ha : a ^ n = 1) (hred : IsLocalRing.residue R a = 1) : a = 1 := by
  have hsum : (∑ i ∈ Finset.range n, a ^ i) ≠ 0 := by
    intro h
    have hz := congrArg (IsLocalRing.residue R) h
    apply hn
    simpa only [map_sum, map_pow, hred, one_pow, Finset.sum_const, Finset.card_range, nsmul_one,
      map_zero] using hz
  have hz := geom_sum_mul a n
  rw [ha, sub_self] at hz
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hsum)

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.eq_one_of_residue_eq_one
