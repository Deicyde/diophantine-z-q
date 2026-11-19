import ZInQKernel.Contrib.OneProof.ShimuraOrbitsCoprime

/-! Good-prime powers: the scalar part preserves the diamond and has multiplicity p. -/

noncomputable section

namespace ShimuraSteps.Orbits

set_option maxHeartbeats 800000

open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

def block {N : ℕ} (g : Gamma0 N) (a d : ℕ) (τ : ℍ) : Divisors N :=
  ∑ b : Fin d, term g a b.val d τ

def powBlock {N : ℕ} (p : ℕ) (hpN : p.Coprime N) (k r : ℕ) (τ : ℍ) : Divisors N :=
  block (lift N (p ^ r) (hpN.pow_left _)) (p ^ r) (p ^ (k - r)) τ

private def divPow {N p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (k : ℕ) :
    Fin (k + 1) ≃ Div N (p ^ k) := by
  let F : Fin (k + 1) → Div N (p ^ k) := fun r =>
    ⟨p ^ r.val, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨pow_dvd_pow _ (Nat.le_of_lt_succ r.isLt), pow_ne_zero _ hp.ne_zero⟩, hpN.pow_left _⟩⟩
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · intro r s e
    exact Fin.ext ((pow_right_injective₀ hp.pos hp.ne_one) (congrArg Subtype.val e))
  · intro a
    obtain ⟨r, hr, he⟩ := (Nat.dvd_prime_pow hp).1
      (Nat.mem_divisors.mp (Finset.mem_filter.mp a.property).1).1
    exact ⟨⟨r, Nat.lt_succ_of_le hr⟩, Subtype.ext he.symm⟩

theorem sumAt_pow {N p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (k : ℕ) (τ : ℍ) :
    sumAt N (p ^ k) τ = ∑ r : Fin (k + 1), powBlock p hpN k r.val τ := by
  rw [sumAt_lifts repLift (by simp [repLift])]
  symm
  refine Fintype.sum_equiv (divPow hp hpN k) _ _ fun r => ?_
  have he : (divPow hp hpN k r).val = p ^ r.val := rfl
  have hd : p ^ k / (divPow hp hpN k r).val = p ^ (k - r.val) := by
    have hpow : p ^ k = p ^ r.val * p ^ (k - r.val) := by
      rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)]
    rw [he, hpow, Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  dsimp only [powBlock, block]
  refine Fintype.sum_equiv (finCongr hd.symm) _ _ fun b => ?_
  simp only [finCongr_apply_coe]
  rw [hd, he]
  apply term_residue
  simp [repLift, he]

theorem sumAt_prime {N p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (τ : ℍ) :
    sumAt N p τ = block (1 : Gamma0 N) 1 p τ + term (lift N p hpN) p 0 1 τ := by
  have he := sumAt_pow hp hpN 1 τ
  rw [pow_one, Fin.sum_univ_two] at he
  rw [he]
  congr 1
  · change block (lift N 1 _) 1 (p ^ 1) τ = block 1 1 p τ
    rw [pow_one]
    apply Finset.sum_congr rfl
    intro b _
    apply term_residue
    change Gamma0Map N (lift N 1 _) = Gamma0Map N 1
    simpa only [Fin.val_zero, pow_zero, Nat.cast_one, map_one] using
      lift_residue N (p ^ (0 : Fin 2).val) (hpN.pow_left _)
  · change block (lift N (p ^ 1) _) (p ^ 1) 1 τ = term (lift N p hpN) p 0 1 τ
    simp [pow_one, block]

theorem prime_block {N p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (g : Gamma0 N)
    {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    R N p (block g a d τ) = block g a (p * d) τ +
      ∑ b : Fin d, term (g * lift N p hpN) (p * a) (p * b.val) d τ := by
  have h (b : Fin d) : R N p (term g a b.val d τ) =
      (∑ c : Fin p, term g a (b.val + c.val * d) (p * d) τ) +
        term (g * lift N p hpN) (p * a) (p * b.val) d τ := by
    rw [term, R_point, sumAt_covariant, sumAt_prime hp hpN, map_add]
    simp only [block, map_sum, term, diamond_point, ← mul_smul,
      Subgroup.coe_mul, Subgroup.coe_one, mul_one,
      triAct_comp one_pos ha hp.pos hd, triAct_comp hp.pos ha one_pos hd,
      one_mul, zero_mul, add_zero]
  simp only [block, map_sum, h, Finset.sum_add_distrib]
  congr 1
  let F (cb : Fin p × Fin d) := term g a (cb.2.val + cb.1.val * d) (p * d) τ
  change (∑ b : Fin d, ∑ c : Fin p, F (c, b)) = _
  rw [← Fintype.sum_prod_type_right F]
  refine Fintype.sum_equiv finProdFinEquiv _ _ ?_
  rintro ⟨c, b⟩
  simp [F, finProdFinEquiv, mul_comm]

theorem scalar_block {N p : ℕ} (hp : 0 < p) (g : Gamma0 N)
    {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    (∑ b : Fin (p * d), term g (p * a) (p * b.val) (p * d) τ) =
      p • block g a d τ := by
  simp_rw [term, triAct_scale ha hd hp]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [finProdFinEquiv, block, term]
  trans ∑ _ : Fin p, ∑ b : Fin d,
      point (orb N ((g : SL(2, ℤ)) • triAct a b.val d τ))
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro b hb
    exact (congrArg point (orb_triAct_mod ha hd g _ τ)).trans
      (by simp [Nat.mod_eq_of_lt b.isLt])
  · simp

private def lowerBlock {N p : ℕ} (g : Gamma0 N) (a d : ℕ) (τ : ℍ) : Divisors N :=
  ∑ b : Fin d, term g (p * a) (p * b.val) d τ

theorem good_count_basis {N p : ℕ} (hp : p.Prime) (hpN : p.Coprime N)
    (k : ℕ) (τ : ℍ) :
    R N p (R N (p ^ (k + 1)) (point (orb N τ))) =
      R N (p ^ (k + 2)) (point (orb N τ)) +
        p • diamond (lift N p hpN) (R N (p ^ k) (point (orb N τ))) := by
  classical
  let g := lift N p hpN
  let upper (r : Fin (k + 2)) := powBlock p hpN (k + 2) r.val τ
  let lower (r : Fin (k + 2)) :=
    lowerBlock (p := p) (lift N (p ^ r.val) (hpN.pow_left _) * g)
      (p ^ r.val) (p ^ (k + 1 - r.val)) τ
  have hstep (r : Fin (k + 2)) :
      R N p (powBlock p hpN (k + 1) r.val τ) = upper r + lower r := by
    simp only [powBlock, upper, lower, lowerBlock, g]
    rw [prime_block hp hpN _ (pow_pos hp.pos _) (pow_pos hp.pos _)]
    have hh : k + 2 - r.val = k + 1 - r.val + 1 := by have := r.isLt; omega
    rw [hh, pow_succ']
  have hlast : lower (Fin.last (k + 1)) = powBlock p hpN (k + 2) (k + 2) τ := by
    have e : p ^ (k + 2) = p * p ^ (k + 1) := pow_succ' _ _
    change lowerBlock (p := p) (lift N (p ^ (k + 1)) _ * g) (p ^ (k + 1))
      (p ^ (k + 1 - (k + 1))) τ =
      block (lift N (p ^ (k + 2)) _) (p ^ (k + 2)) (p ^ (k + 2 - (k + 2))) τ
    simp only [Nat.sub_self, pow_zero]
    change (∑ b : Fin 1, term (lift N (p ^ (k + 1)) _ * g)
      (p * p ^ (k + 1)) (p * b.val) 1 τ) =
      ∑ b : Fin 1, term (lift N (p ^ (k + 2)) _) (p ^ (k + 2)) b.val 1 τ
    simp only [Fin.sum_univ_one, Fin.val_zero, mul_zero]
    refine (term_residue (g := lift N (p ^ (k + 1)) (hpN.pow_left _) * g)
      (h := lift N (p ^ (k + 2)) (hpN.pow_left _)) (by simp [g, e, mul_comm])
      (p * p ^ (k + 1)) 0 1 τ).trans ?_
    rw [← e]
  have hmore (r : Fin (k + 1)) :
      lower r.castSucc = p • diamond g (powBlock p hpN k r.val τ) := by
    have hh : k + 1 - r.val = k - r.val + 1 := by have := r.isLt; omega
    change lowerBlock (p := p) (lift N (p ^ r.val) _ * g) (p ^ r.val)
      (p ^ (k + 1 - r.val)) τ = _
    rw [hh, pow_succ' p (k - r.val)]
    unfold lowerBlock
    rw [scalar_block hp.pos _ (pow_pos hp.pos r.val) (pow_pos hp.pos (k - r.val))]
    simp only [powBlock, block, map_sum, diamond_term]
    congr 1
    exact Finset.sum_congr rfl fun b _ => term_residue (by simp [mul_comm]) _ _ _ _
  simp only [R_point, sumAt_pow hp hpN, map_sum]
  simp_rw [hstep]
  rw [Finset.sum_add_distrib, Fin.sum_univ_castSucc lower, hlast]
  simp_rw [hmore]
  rw [← Finset.smul_sum, ← map_sum, Fin.sum_univ_castSucc (n := k + 2)]
  dsimp [upper]
  abel

#print axioms sumAt_pow
#print axioms sumAt_prime
#print axioms prime_block
#print axioms scalar_block
#print axioms good_count_basis

end ShimuraSteps.Orbits
