import ZInQKernel.Contrib.OneProof.RC.ThetaClose.Assembly
import ZInQKernel.Contrib.OneProof.RC.TorusWeights.Actual

/-! Read the actual Schwartz product at the chosen class lift, retaining the
condition on the norm character of a right order unit. Tex 8495–8578, 9171–9179. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O7Assemble

open Eichler Adelic ThetaJoin ThetaClose LocalWeights O7Actual Visibility
open scoped Quaternion

variable {ell N M m : ℕ} [Fact ell.Prime]
variable (h : ell % 4 = 3) (hN : 0 < N) (H : DiscriminantData m N ell) (w : ℕ → ℤˣ)

abbrev primes := exceptionalPlaces m N ell (exceptionalProduct_ne_zero hN H)

omit [Fact ell.Prime] in
/-- The two bundled reduced norm homomorphisms compute the same scalar. -/
theorem localNrd_eq (p : Prime) (u : (Bp p.val (-1) (-(ell : ℚ)))ˣ) :
    TorusWeights.localNrd p u = localNormHom p u := rfl

theorem extend_order {X Y O : Type*} [MonoidWithZero O]
    (i : X → Y) (hi : Function.Injective i) (f : X → O)
    (hf : ∀ x, f x ≠ 0 → ∃ j : ℕ, f x ^ (2 ^ j : ℕ) = 1)
    (y : Y) (hy : extendWeight i f y ≠ 0) :
    ∃ j : ℕ, extendWeight i f y ^ (2 ^ j : ℕ) = 1 := by
  have hs := extendWeight_spec i f hi
  have hr : y ∈ Set.range i := by
    by_contra hy'
    exact hy (hs.2 y hy')
  obtain ⟨x, rfl⟩ := hr
  rw [hs.1] at hy ⊢
  exact hf x hy

theorem char_order {p : ℕ} [Fact p.Prime] {O : Type*} [Ring O] (x : ZMod p)
    (hx : (quadraticChar (ZMod p) x : O) ≠ 0) :
    ∃ j : ℕ, (quadraticChar (ZMod p) x : O) ^ (2 ^ j : ℕ) = 1 := by
  have hn : x ≠ 0 := by rintro rfl; simp at hx
  rcases quadraticChar_dichotomy hn with he | he <;> exact ⟨1, by simp [he]⟩

set_option maxHeartbeats 1200000 in
/-- Each nonzero local factor of the fixed Schwartz product has two-power
order. Only the positive-level case uses the chosen level characters. -/
theorem localFactor_order (p : Prime) (x : Bp p.val (-1) (-(ell : ℚ)))
    (hx : localFactor h (levelRoots hN H w) m p x ≠ 0) :
    ∃ j : ℕ, localFactor h (levelRoots hN H w) m p x ^ (2 ^ j : ℕ) = 1 := by
  classical
  let C := levelRoots hN H w
  unfold localFactor at hx ⊢
  by_cases hp : p.val = ell
  · have he : p = ⟨ell, Fact.out⟩ := Subtype.ext hp
    subst p
    simp only [dite_true] at hx ⊢
    let : Fact (ell % 4 = 3) := ⟨h⟩
    unfold divisionFactor at hx ⊢
    split at hx <;> rename_i hz
    · simp only [dite_eq_left hz]
      unfold DivisionCoordinates.divisionSchwartz
      refine extend_order _ (LocalDivision.coordinates ell).zeroInclusion_openEmbedding.injective _ ?_ _ hx
      · intro y hy
        unfold DivisionCoordinates.divisionWeight DivisionCoordinates.residueWeight at hy ⊢
        split at hy <;> rename_i h'
        · simp only [dite_eq_left h']
          exact char_order _ hy
        · exact (hy rfl).elim
    · exact (hx rfl).elim
  · simp only [dite_eq_right hp] at hx ⊢
    unfold splitFactor at hx ⊢
    split at hx <;> rename_i ht
    · simp only [dite_eq_left ht]
      by_cases hpN : p.val ∣ N
      · simp only [dite_eq_left hpN] at hx ⊢
        unfold levelSchwartz
        refine extend_order _ (affineZero_openEmbedding _ _).injective _ ?_ _ hx
        intro y hy
        unfold levelWeight at hy ⊢
        split at hy <;> rename_i hr
        · simp only [dite_eq_left hr]
          exact ⟨C.exponent, congrArg Units.val (C.order p hpN _)⟩
        · exact (hy rfl).elim
      · simp only [dite_eq_right hpN] at hx ⊢
        by_cases h₂ : p.val = 2
        · have he : p = ⟨2, Nat.prime_two⟩ := Subtype.ext h₂
          subst p
          simp only [dite_true] at hx ⊢
          unfold dyadicSchwartz
          refine extend_order _ (affineZero_openEmbedding 2 0).injective _ ?_ _ hx
          intro y hy
          unfold dyadicWeight at hy ⊢
          split at hy <;> rename_i hd
          · exact ⟨0, by simp [hd]⟩
          · exact (hy rfl).elim
        · simp only [dite_eq_right h₂] at hx ⊢
          by_cases hm : p.val ∣ m
          · simp only [ite_eq_left hm] at hx ⊢
            unfold nilSchwartz
            refine extend_order _ (integralZero_openEmbedding _).injective _ ?_ _ hx
            intro y hy
            unfold nilWeight at hy ⊢
            split at hy <;> rename_i hd
            · simp only [ite_eq_left hd]
              unfold nilSign at hy ⊢
              split at hy <;> rename_i hb
              · simp only [dite_eq_left hb]
                exact char_order _ hy
              · exact (hy (by simp)).elim
            · exact (hy rfl).elim
          · simp only [ite_eq_right hm] at hx ⊢
            unfold goodWeight at hx ⊢
            split at hx <;> rename_i hg
            · exact ⟨0, by simp [hg]⟩
            · exact (hx rfl).elim
    · exact (hx rfl).elim

variable (C : TorusWeights.NormFactors (levelRing h hN) (-(m : ℤ)))

/-- The actual Schwartz factors, using the ramified local unit characters
from the existing covariance calculation. -/
def schwartzFactors
    (hunit : ∀ (p : Prime) (u : localUnits (levelRing h hN) p),
      C.atPrime p (TorusWeights.localNrd p u.val) =
        if p.val ∣ m then legendreUnit p.val (normUnit h hN p u) else 1) :
    TorusWeights.SchwartzFactors (Coefficients hN H w) C where
  primes := primes hN H
  ramified p hp := (mem_exceptionalPlaces m N ell _ p).mpr
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (by simpa using hp : p.val ∣ m) 2) N) ell)
  value := localFactor h (levelRoots hN H w) m
  covariance p hp u x := by
    rw [hunit p u]
    let cov := levelNormCovariance h hN (levelRoots hN H w)
      (exceptionalProduct_ne_zero hN H) (discriminantDisjoint H)
    have hc := cov.local_conj p hp u x
    by_cases hm : p.val ∣ m
    · simpa only [cov, levelNormCovariance, ite_eq_left hm, legendreUnit_inv, legendreUnit_apply, Int.cast_id, mul_comm]
        using hc
    · simpa only [cov, levelNormCovariance, ite_eq_right hm, inv_one,
        Units.val_one, Int.cast_one, one_mul, mul_one] using hc
  local_order p _ x := localFactor_order h hN H w p x

variable (hcop : N.Coprime ell)
/-- Beside the finite exceptional product the actual Schwartz function has
a lattice gate, which is true at every nonzero supported vector. -/
theorem stageSchwartzRead
    (hunit : ∀ (p : Prime) (u : localUnits (levelRing h hN) p),
      C.atPrime p (TorusWeights.localNrd p u.val) =
        if p.val ∣ m then legendreUnit p.val (normUnit h hN p u) else 1)
    (z : ClassSet (levelRing h hN)) (x : B (-1) (-(ell : ℚ)))
    (hx : (actualPmLocal (M := M) h hN hcop H w).f z x ≠ 0) :
    (actualPmLocal (M := M) h hN hcop H w).f z x =
      (schwartzFactors h hN H w C hunit).eval (classRepresentative z) x := by
  classical
  change weightAt _ _ (classRepresentative z) x ≠ 0 at hx
  change weightAt _ _ (classRepresentative z) x = _
  by_cases hz : x ∈ (fromAdelic (classRepresentative z)).val.leftRing
  · exact ite_eq_left hz
  · exact (hx (ite_eq_right hz)).elim

end ZInQ.Manuscript.RC.O7Assemble
