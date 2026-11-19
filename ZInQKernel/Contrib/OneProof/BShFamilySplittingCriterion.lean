import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Order.Filter.Germ.Basic

/-! ON THE SPOT (provenance (c)): a monic remainder lifts eventual pointwise
root exhaustion to a splitting statement over a field of germs. -/

noncomputable section

namespace BShFamily

open Filter Polynomial
open scoped BigOperators

/-- A pointwise exhaustion of roots over an algebraically closed field implies
divisibility by a power of the product of the displayed linear factors. -/
theorem dvd_prod_pow_of_exhaustion {F ι : Type*} [Field F] [IsAlgClosed F] [Fintype ι]
    (P : F[X]) (hP : P ≠ 0) (r : ι → F) (d : ℕ) (hd : P.natDegree ≤ d)
    (h : ∀ x, P.eval x = 0 → ∃ i, x = r i) :
    P ∣ (∏ i, (X - C (r i))) ^ d := by
  classical
  let Q : F[X] := ∏ i, (X - C (r i))
  have hm : Q.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (r i))
  apply (IsAlgClosed.splits P).dvd_of_roots_le_roots hP
  apply Multiset.le_iff_count.mpr
  intro x
  by_cases hx : x ∈ P.roots
  · obtain ⟨i, rfl⟩ := h x ((mem_roots hP).mp hx)
    have hQ : r i ∈ Q.roots := by
      apply (mem_roots hm.ne_zero).mpr
      exact dvd_iff_isRoot.mp (Finset.dvd_prod_of_mem (fun j => X - C (r j)) (Finset.mem_univ i))
    rw [roots_pow, Multiset.count_nsmul]
    exact (Multiset.count_le_card _ _).trans
      (P.card_roots'.trans (hd.trans (Nat.le_mul_of_pos_right _ (Multiset.count_pos.mpr hQ))))
  · simp [Multiset.count_eq_zero_of_notMem hx]

/-- The monic remainder identity can be tested pointwise before passage to
a germ. The powers account for multiplicities independently of the root atlas. -/
theorem splits_of_eventually_exhaustion {α F E ι : Type*} [Field F] [IsAlgClosed F]
    [Field E] [Fintype ι] {l : Filter α} [NeBot l]
    (e : E →+* Germ l F) (P : E[X]) (A : (α → F)[X]) (hA : A.Monic)
    (he : A.map (Germ.coeRingHom l) = P.map e)
    (r : ι → E) (f : ι → α → F)
    (hr : ∀ i, e (r i) = (f i : Germ l F)) (d : ℕ)
    (h : ∀ᶠ z in l, let Pz := A.map (Pi.evalRingHom (fun _ : α => F) z);
      Pz.natDegree ≤ d ∧ ∀ x, Pz.eval x = 0 → ∃ i, x = f i z) :
    P.Splits := by
  classical
  let B : (α → F)[X] := (∏ i, (X - C (f i))) ^ d
  let Q : E[X] := (∏ i, (X - C (r i))) ^ d
  have hB : B.map (Germ.coeRingHom l) = Q.map e := by
    simp only [B, Q, Polynomial.map_pow, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C, hr]
    rfl
  have hz : ∀ᶠ z in l, (B %ₘ A).map (Pi.evalRingHom (fun _ : α => F) z) = 0 := by
    filter_upwards [h] with z hz
    rw [map_modByMonic _ hA, modByMonic_eq_zero_iff_dvd (hA.map _)]
    have hBz : B.map (Pi.evalRingHom (fun _ : α => F) z) =
        (∏ i, (X - C (f i z))) ^ d := by
      simp only [B, Polynomial.map_pow, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C]
      rfl
    rw [hBz]
    exact dvd_prod_pow_of_exhaustion _ (hA.map _).ne_zero _ d hz.1 hz.2
  have hz' : (B %ₘ A).map (Germ.coeRingHom l) = 0 := by
    ext n
    rw [coeff_map, coeff_zero]
    apply Germ.coe_eq.mpr
    filter_upwards [hz] with z hzz
    change (B %ₘ A).coeff n z = 0
    have hcoeff := congrArg (fun p : F[X] => p.coeff n) hzz
    rw [coeff_map, coeff_zero] at hcoeff
    exact hcoeff
  rw [map_modByMonic _ hA, hB, he, ← map_modByMonic] at hz'
  · have hm : P.Monic := by
      apply monic_of_injective e.injective
      rw [← he]
      exact hA.map _
    have hdvd := (modByMonic_eq_zero_iff_dvd hm).mp ((Polynomial.map_eq_zero_iff e.injective).mp hz')
    have hQ : Q.Monic := (monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (r i))).pow _
    exact ((Splits.prod (fun i _ => Splits.X_sub_C (r i))).pow _).of_dvd hQ.ne_zero hdvd
  · apply monic_of_injective e.injective
    rw [← he]
    exact hA.map _

#print axioms dvd_prod_pow_of_exhaustion
#print axioms splits_of_eventually_exhaustion

end BShFamily
