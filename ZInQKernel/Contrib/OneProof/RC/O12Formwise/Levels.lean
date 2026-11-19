import ZInQKernel.Contrib.OneProof.RC.ThetaCoeff.Operators

/-! Formwise level bounds for the theta blocks (tex 9497–9555, 9754–9760).
The common level of `Blocks` does not record these bounds. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Formwise

open ThetaCoeff
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped Classical

variable {I K O G L : Type} [Fintype I] [Field K] [CommRing O] [IsDomain O]
  [CharZero O] [Algebra O K] [Group G] [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {avoid : Finset ℕ}
variable {M W R : ℕ} {S : AppF.ThetaStage (Odd.StageRing O M)} {δ : ℤ} {adm : ℕ → Prop}
variable {P : Window T.Good S W} {A : Basis I K G (Test T avoid)}
variable {E : Lift S} {D : Divisions E δ W R adm} {C : DiamondCharacters O G E.η}
variable {V : Blocks (P := P) A E D C}

/-- ELLIOT: retain the lower levels in the given block realization. Here
`level i` includes the degeneracy multiplier: it is the underlying newform
or Eisenstein level times the dilation of this occurrence. The old level
includes the fixed and moving sieves of the actual stage. The two bounds
are on the individual blocks before the integer division in (O.11). -/
structure BlockLevels (V : Blocks (P := P) A E D C) where
  oldLevel : ℕ
  old_good : ∀ q, T.Good q → q.Coprime oldLevel
  level : I → ℕ
  degree_dvd : ∀ i, A.degree i ∣ level i
  b_level : ∀ U (hU : U ⊆ P.pool) i, V.b U hU i ≠ 0 →
    level i ∣ oldLevel * ∏ p ∈ U, p
  unary_level : ∀ U (hU : U ⊆ P.pool) j, j ∈ subscripts U → ∀ i,
    V.unary U hU j i ≠ 0 → level i ∣ oldLevel * j

variable (N : BlockLevels V)

/-- The combination in (O.11) introduces no constituent of larger level.
This also holds for the zero extension, where there is no active coordinate.
The coordinate and divisibility argument is on-the-spot (c). -/
theorem seed_level_dvd {U : Finset ℕ} {i : I} (hi : V.seed U i ≠ 0) :
    N.level i ∣ N.oldLevel * ∏ p ∈ U, p := by
  by_cases hU : U ⊆ P.pool
  · by_contra hn
    have hb : V.b U hU i = 0 := by
      by_contra h
      exact hn (N.b_level U hU i h)
    have hu : ∀ j ∈ subscripts U, V.unary U hU j i = 0 := by
      intro j hj
      by_contra h
      obtain ⟨hsq, hsub⟩ := (mem_subscripts (fun p hp => (P.type_good p (hU hp)).1) j).mp hj
      have hjd : j ∣ ∏ p ∈ U, p := by
        rw [← Nat.prod_primeFactors_of_squarefree hsq]
        exact Finset.prod_dvd_prod_of_subset _ _ id hsub
      exact hn ((N.unary_level U hU j hj i h).trans (Nat.mul_dvd_mul_left _ hjd))
    apply hi
    rw [Blocks.seed, dite_eq_left hU, Blocks.vector]
    simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, hb, zero_sub]
    rw [Finset.sum_eq_zero (fun j hj => by rw [hu j hj, smul_zero]), neg_zero, smul_zero]
  · exact (hi (by simp [Blocks.seed, hU])).elim

/-- A good prime outside the active set misses the level of every occurring
coordinate, including its degeneracy multiplier. On-the-spot (c). -/
theorem seed_level_coprime {U : Finset ℕ} {q : ℕ} (hq : T.Good q) (hqU : q ∉ U)
    {i : I} (hi : V.seed U i ≠ 0) : q.Coprime (N.level i) := by
  have hU : U ⊆ P.pool := by
    by_contra hn
    exact hi (by simp [Blocks.seed, hn])
  have hp : q.Coprime (∏ p ∈ U, p) := by
    apply (Nat.Prime.coprime_iff_not_dvd hq.1).2
    intro hd
    obtain ⟨p, hp, hqp⟩ := (hq.1.prime.dvd_finsetProd_iff _).1 hd
    exact hqU (((Nat.prime_dvd_prime_iff_eq hq.1 (P.type_good p (hU hp)).1).mp hqp).symm ▸ hp)
  exact ((N.old_good q hq).mul_right hp).of_dvd_right (seed_level_dvd N hi)

#print axioms seed_level_dvd
#print axioms seed_level_coprime

end ZInQ.Manuscript.RC.O12Formwise
