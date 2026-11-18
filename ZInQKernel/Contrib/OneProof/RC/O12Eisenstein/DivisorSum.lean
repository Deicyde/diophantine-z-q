import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.Divisors

/-!
# Weight-two Eisenstein coefficients at a ramified prime

Tex 9862–9864. The divisor-sum proof and the check on degeneracies away from
the operator prime are on-the-spot calculations (provenance (c)).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Eisenstein

variable {K : Type*} [CommRing K]

/-- Weight two: the factor `d` is on the second character. The factor pairs
`(u,d)` of `n` index the divisors `d`, with `u = n/d`. -/
def divisorCoeff {m₁ m₂ : ℕ} (χ₁ : DirichletCharacter K m₁)
    (χ₂ : DirichletCharacter K m₂) (n : ℕ) : K :=
  ∑ x ∈ n.divisorsAntidiagonal, χ₁ (x.1 : ZMod m₁) * (χ₂ (x.2 : ZMod m₂) * (x.2 : K))

private theorem factorSum_at_mul {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (f g : ℕ →* K) (hg : g p = 0) :
    (∑ x ∈ (p * n).divisorsAntidiagonal, f x.1 * g x.2) =
      f p * ∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (p := fun x : ℕ × ℕ => p ∣ x.1), Finset.mul_sum]
  have hz : (∑ x ∈ (p * n).divisorsAntidiagonal.filter (fun x => ¬ p ∣ x.1),
      f x.1 * g x.2) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    obtain ⟨hx, hx₁⟩ := Finset.mem_filter.mp hx
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hx).1
    have hdiv : p ∣ x.1 * x.2 := hprod ▸ dvd_mul_right p n
    obtain ⟨k, hk⟩ := (hp.dvd_mul.mp hdiv).resolve_left hx₁
    rw [hk, map_mul, hg, zero_mul, mul_zero]
  rw [hz, add_zero]
  symm
  refine Finset.sum_bij (fun x _ => (p * x.1, x.2)) ?_ ?_ ?_ ?_
  · intro x hx
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hx).1
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisorsAntidiagonal.mpr
        ⟨by rw [mul_assoc, hprod], mul_ne_zero hp.ne_zero hn⟩, dvd_mul_right p x.1⟩
  · intro x _ y _ h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left hp.pos h₁) h₂
  · intro y hy
    obtain ⟨hy, k, hk⟩ := Finset.mem_filter.mp hy
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hy).1
    refine ⟨(k, y.2), Nat.mem_divisorsAntidiagonal.mpr ⟨?_, hn⟩, Prod.ext hk.symm rfl⟩
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    rw [← mul_assoc, ← hk, hprod]
  · intro x _
    simp only [map_mul, mul_assoc]

private theorem factorSum_swap (f g : ℕ →* K) (n : ℕ) :
    (∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2) =
      ∑ x ∈ n.divisorsAntidiagonal, g x.1 * f x.2 := by
  conv_lhs => rw [← Nat.map_swap_divisorsAntidiagonal, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

private def natChar {m : ℕ} (χ : DirichletCharacter K m) : ℕ →* K :=
  χ.toMonoidHom.comp (Nat.castRingHom (ZMod m)).toMonoidHom

private def weightedNatChar {m : ℕ} (χ : DirichletCharacter K m) : ℕ →* K :=
  natChar χ * (Nat.castRingHom K).toMonoidHom

/-- If the second character vanishes at `p`, the eigenvalue is `χ₁(p)`. -/
theorem divisorCoeff_mul_of_right_zero {m₁ m₂ p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (χ₁ : DirichletCharacter K m₁) (χ₂ : DirichletCharacter K m₂)
    (hχ : χ₂ (p : ZMod m₂) = 0) :
    divisorCoeff χ₁ χ₂ (p * n) = χ₁ (p : ZMod m₁) * divisorCoeff χ₁ χ₂ n :=
  factorSum_at_mul hp hn (natChar χ₁) (weightedNatChar χ₂)
    (show χ₂ (p : ZMod m₂) * (p : K) = 0 by rw [hχ, zero_mul])

/-- If the first character vanishes at `p`, the eigenvalue is `χ₂(p) p`. -/
theorem divisorCoeff_mul_of_left_zero {m₁ m₂ p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (χ₁ : DirichletCharacter K m₁) (χ₂ : DirichletCharacter K m₂)
    (hχ : χ₁ (p : ZMod m₁) = 0) :
    divisorCoeff χ₁ χ₂ (p * n) = (χ₂ (p : ZMod m₂) * (p : K)) * divisorCoeff χ₁ χ₂ n := by
  change (∑ x ∈ (p * n).divisorsAntidiagonal, natChar χ₁ x.1 * weightedNatChar χ₂ x.2) =
    weightedNatChar χ₂ p * ∑ x ∈ n.divisorsAntidiagonal, natChar χ₁ x.1 * weightedNatChar χ₂ x.2
  rw [factorSum_swap (natChar χ₁) (weightedNatChar χ₂) (p * n),
      factorSum_swap (natChar χ₁) (weightedNatChar χ₂) n]
  exact factorSum_at_mul hp hn _ _ hχ

/-- The zero extension of a Dirichlet character vanishes at primes dividing
its modulus. For the constituent pair use the characters at their conductors. -/
theorem dirichlet_apply_prime_eq_zero {m p : ℕ} (hp : p.Prime) (hpm : p ∣ m)
    (χ : DirichletCharacter K m) : χ (p : ZMod m) = 0 :=
  χ.map_nonunit (fun h => (hp.coprime_iff_not_dvd.mp ((ZMod.isUnit_iff_coprime p m).mp h)) hpm)

/-- Positive coefficients of the degeneracy `f(q^d)`. -/
def degenerate (d : ℕ) (a : ℕ → K) (n : ℕ) : K :=
  if d ∣ n then a (n / d) else 0

/-- Degeneracy away from `p) preserves the eigenvalue of the Fourier shift. -/
theorem degenerate_mul {p d : ℕ} (hpd : d.Coprime p) {a : ℕ → K} {lam : K}
    (ha : ∀ n ≠ 0, a (p * n) = lam * a n) {n : ℕ} (hn : n ≠ 0) :
    degenerate d a (p * n) = lam * degenerate d a n := by
  by_cases h : d ∣ n
  · have hd : 0 < d := Nat.pos_of_dvd_of_pos h (Nat.pos_of_ne_zero hn)
    obtain ⟨k, rfl⟩ := h
    have hk : k ≠ 0 := (mul_ne_zero_iff.mp hn).2
    have hdvd : d ∣ p * (d * k) := hpd.dvd_mul_left.mpr (dvd_mul_right d k)
    rw [degenerate, ite_eq_left hdvd, degenerate, ite_eq_left (dvd_mul_right d k),
      show p * (d * k) = d * (p * k) by ac_rfl,
      Nat.mul_div_cancel_left _ hd, Nat.mul_div_cancel_left _ hd, ha k hk]
  · rw [degenerate, ite_eq_right (fun hh => h (hpd.dvd_mul_left.mp hh)),
      degenerate, ite_eq_right h, mul_zero]

#print axioms factorSum_at_mul
#print axioms factorSum_swap
#print axioms divisorCoeff_mul_of_right_zero
#print axioms divisorCoeff_mul_of_left_zero
#print axioms dirichlet_apply_prime_eq_zero
#print axioms degenerate_mul

end ZInQ.Manuscript.RC.O12Eisenstein
