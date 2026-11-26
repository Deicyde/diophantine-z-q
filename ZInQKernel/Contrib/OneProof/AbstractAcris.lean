import ZInQKernel.Contrib.OneProof.AcrisImage

/-! # The tree's abstract `A_cris` inside `B_dR^+`

`PanBergerSplit.Acris p` is the `p`-adic completion of `PanBergerSplit.Acris0 p`, Fontaine's
`A_cris` (Astérisque 223 (1994), Exposé II, §2.3.3, p. 78). By `AcrisImage.acris_image` it has an
injective, Galois-equivariant ring map to `B_dR^+` with image `AcrisOf`; `acrisEmb` is one such
map, chosen. It sends the abstract logarithm `PanBergerSplit.logT` to the `ker θ`-adic logarithm
(`acrisEmb_logT`).
-/

noncomputable section

namespace HDec.PkgI4.AbstractPeriods

open BergerBst FontaineSt BmaxOne
open PanBergerSplit (Ainf AinfP theta Acris0 Acris acrisAct logT)
open _root_.ZInQ.Contrib.G9.BdrKer.Cp (xi)

variable (p : ℕ) [Fact p.Prime]

/-- The tree's abstract `A_cris` embedded in `B_dR^+` (`AcrisImage.acris_image`). -/
def acrisEmb : Acris p →+* BDeRhamPlus 𝓞_ℂ_[p] p :=
  Classical.choose (AcrisImage.acris_image (p := p))

theorem acrisEmb_injective : Function.Injective (acrisEmb p) :=
  (Classical.choose_spec (AcrisImage.acris_image (p := p))).1

/-- On `A_cris^0` the map is the inclusion `A_cris^0 ⊆ W(R)[1/p] → B_dR^+`. -/
theorem acrisEmb_algebraMap (x : Acris0 p) :
    acrisEmb p (algebraMap (Acris0 p) (Acris p) x) =
      (show BDeRhamPlus 𝓞_ℂ_[p] p from
        algebraMap (AinfP p) (AdicCompletion (Ith p) (AinfP p)) (x : AinfP p)) :=
  (Classical.choose_spec (AcrisImage.acris_image (p := p))).2.1 x

theorem range_acrisEmb : Set.range (acrisEmb p) = AcrisOf p (xi p) (theta_xi' p) :=
  (Classical.choose_spec (AcrisImage.acris_image (p := p))).2.2.1

theorem acrisEmb_acrisAct (σ : GQp p) (x : Acris p) :
    acrisEmb p (acrisAct p σ x) = DR.bdrPlusMap p (oAct p σ) (acrisEmb p x) :=
  (Classical.choose_spec (AcrisImage.acris_image (p := p))).2.2.2 σ x

/-! ### Proof of `acrisEmb_logT`

`acrisEmb` is not continuous from the `p`-adic topology to the `ker θ`-adic one, so the image of
the limit `logT` is not computed by continuity. Instead, write `x = c ξ`. For every `n`,
`log(1 + x) = (partial sum up to p^n) + p^n w_n` in `B_dR^+` with `w_n ∈ A_cris`
(`logPlus_eq_tail`), since `x^k/k = (k-1)! c^k ξ^k/k!` and `p^n ∣ (k-1)!` for `k > p^n`. Pulling
this back along the injective `acrisEmb` gives one element of `A_cris` that agrees with `logT`
modulo `p^n` for every `n`. -/

/-- A polynomial evaluates in the completion to the image of its value. -/
private theorem psEval_coe {A : Type*} [CommRing A] (I : Ideal A) {y : A} (hy : y ∈ I)
    (P : Polynomial A) :
    psEval I hy (P : PowerSeries A) = algebraMap A (AdicCompletion I A) (P.eval y) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_psEval, mk_eval_trunc I hy, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, AdicCompletion.evalₐ_of]

private theorem coeff_logSeries {k : ℕ} (hk : k ≠ 0) :
    PowerSeries.coeff k (logSeries p) = (-1) ^ (k + 1) * qpToLoc p ((k : ℚ_[p])⁻¹) := by
  rw [logSeries, PowerSeries.coeff_mk, ite_eq_right hk]

private theorem coeff_zero_logSeries : PowerSeries.coeff 0 (logSeries p) = 0 := by
  rw [logSeries, PowerSeries.coeff_mk, ite_eq_left rfl]

/-- `1/k = (k-1)!/k!`. -/
private theorem qpToLoc_inv_eq {k : ℕ} (hk : k ≠ 0) :
    qpToLoc p ((k : ℚ_[p])⁻¹) =
      (((k - 1).factorial : ℕ) : AinfP p) * qpToLoc p ((k.factorial : ℚ_[p])⁻¹) := by
  rw [← map_natCast (qpToLoc p), ← map_mul]
  congr 1
  have hf0 : ((k - 1).factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hfac : (k.factorial : ℚ_[p]) = (k : ℚ_[p]) * ((k - 1).factorial : ℚ_[p]) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hk]
  rw [hfac, mul_inv, ← mul_assoc, mul_comm _ (k : ℚ_[p])⁻¹, mul_assoc, mul_inv_cancel₀ hf0,
    mul_one]

/-- The partial sums of the logarithm are the truncations of `logSeries`. -/
private theorem eval_trunc_logSeries (x : Ainf p) (N : ℕ) :
    (PowerSeries.trunc (N + 1) (logSeries p)).eval (algebraMap (Ainf p) (AinfP p) x) =
      PanBergerSplit.logPartialVal p x N := by
  rw [Polynomial.eval, PowerSeries.eval₂_trunc_eq_sum_range, PanBergerSplit.logPartialVal,
    Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < N + 1)]
  simp only [coeff_zero_logSeries, map_zero, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 : j ≠ 0 := by
    rw [Finset.mem_Ico] at hj
    omega
  rw [RingHom.id_apply, coeff_logSeries p hj0, PanBergerSplit.logTerm, PanBergerSplit.dpow,
    qpToLoc_inv_eq p hj0]
  ring

/-- For `x = c ξ`, the tail `Σ_{k > p^n} (-1)^{k+1} x^k/k` divided by `p^n`, as the coefficients
`(-1)^{k+1} ((k-1)!/p^n) c^k` of a divided-power series in `ξ`. -/
private def tailSeries (c : Ainf p) (n : ℕ) : PowerSeries (Ainf p) :=
  PowerSeries.mk fun k => if k ≤ p ^ n then 0 else
    (-1) ^ (k + 1) * (((k - 1).factorial / p ^ n : ℕ) : Ainf p) * c ^ k

private theorem tailSeries_mem (c : Ainf p) (n : ℕ) : tailSeries p c n ∈ restricted p :=
  fun K => ⟨p * (n + K) + p ^ n + 1, fun k hk => by
    change (p : Ainf p) ^ K ∣ PowerSeries.coeff k (tailSeries p c n)
    rw [tailSeries, PowerSeries.coeff_mk, ite_eq_right (by omega)]
    have hd : p ^ K ∣ (k - 1).factorial / p ^ n := by
      apply Nat.dvd_div_of_mul_dvd
      rw [← pow_add]
      exact dvd_trans (FontaineSt.pow_dvd_factorial_mul p (n + K))
        (Nat.factorial_dvd_factorial (by omega))
    obtain ⟨d, hd⟩ := hd
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ⟨(d : Ainf p), ?_⟩ _) _
    rw [hd, Nat.cast_mul, Nat.cast_pow]⟩

/-- `log(1 + x) = (partial sum up to p^n) + p^n · (an element of A_cris)` in `B_dR^+`. -/
private theorem logPlus_eq_tail {x c : Ainf p} (hc : c * xi p = x)
    (hx' : algebraMap (Ainf p) (AinfP p) x ∈ Ith p) (n : ℕ) :
    logPlus p hx' =
      (show BDeRhamPlus 𝓞_ℂ_[p] p from
        algebraMap (AinfP p) (AdicCompletion (Ith p) (AinfP p))
          (PanBergerSplit.logPartialVal p x (p ^ n))) +
        (p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ n *
          evalB p (algebraMap_mem_ith p (theta_xi' p)) (dpSeries p (tailSeries p c n)) := by
  have h1 : logPlus p hx' =
      evalB p hx' ((PowerSeries.trunc (p ^ n + 1) (logSeries p) : Polynomial (AinfP p)) :
        PowerSeries (AinfP p)) +
      evalB p hx' (logSeries p - ((PowerSeries.trunc (p ^ n + 1) (logSeries p) :
        Polynomial (AinfP p)) : PowerSeries (AinfP p))) := by
    rw [logPlus, ← RingHom.map_add, add_sub_cancel]
  have h2 : evalB p hx' ((PowerSeries.trunc (p ^ n + 1) (logSeries p) : Polynomial (AinfP p)) :
        PowerSeries (AinfP p)) =
      (show BDeRhamPlus 𝓞_ℂ_[p] p from
        algebraMap (AinfP p) (AdicCompletion (Ith p) (AinfP p))
          (PanBergerSplit.logPartialVal p x (p ^ n))) := by
    have h := psEval_coe (Ith p) hx' (PowerSeries.trunc (p ^ n + 1) (logSeries p))
    rw [eval_trunc_logSeries] at h
    exact h
  have h3 : evalB p hx' (logSeries p - ((PowerSeries.trunc (p ^ n + 1) (logSeries p) :
        Polynomial (AinfP p)) : PowerSeries (AinfP p))) =
      evalB p (algebraMap_mem_ith p (theta_xi' p))
        (PowerSeries.C ((p : AinfP p) ^ n) * dpSeries p (tailSeries p c n)) := by
    apply psEval_eq_of_terms
    intro k
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, PowerSeries.coeff_C_mul, dpSeries,
      PowerSeries.coeff_mk, tailSeries, PowerSeries.coeff_mk]
    by_cases hk : k ≤ p ^ n
    · rw [ite_eq_left (by omega : k < p ^ n + 1), sub_self, ite_eq_left hk]
      simp only [map_zero, zero_mul, mul_zero]
    · rw [ite_eq_right (by omega : ¬ k < p ^ n + 1), sub_zero, ite_eq_right hk,
        coeff_logSeries p (by omega : k ≠ 0), qpToLoc_inv_eq p (by omega : k ≠ 0), ← hc]
      have hdvd : p ^ n ∣ (k - 1).factorial :=
        Nat.dvd_factorial (pow_pos (Fact.out : p.Prime).pos n) (by omega)
      have hcast : (p : AinfP p) ^ n * (((k - 1).factorial / p ^ n : ℕ) : AinfP p) =
          (((k - 1).factorial : ℕ) : AinfP p) := by
        rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      rw [← hcast]
      simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
      ring
  have h4 : evalB p (algebraMap_mem_ith p (theta_xi' p)) (PowerSeries.C ((p : AinfP p) ^ n)) =
      (p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ n := by
    refine (psEval_C (Ith p) (algebraMap_mem_ith p (theta_xi' p)) ((p : AinfP p) ^ n)).trans ?_
    rw [map_pow, map_natCast]
    rfl
  rw [h1, h2, h3, RingHom.map_mul, h4]

/-- **The abstract logarithm goes to the `ker θ`-adic logarithm**: for `x ∈ ker θ`, the limit in
`A_cris` of the partial sums `Σ_{j ≤ p^n} (-1)^{j+1} (j-1)! x^j/j!` is sent to
`log(1 + x) = Σ_{j ≥ 1} (-1)^{j+1} x^j/j ∈ B_dR^+`. -/
theorem acrisEmb_logT {x : Ainf p} (hx : theta p x = 0)
    (hx' : algebraMap (Ainf p) (AinfP p) x ∈ Ith p) :
    acrisEmb p (logT p hx) = logPlus p hx' := by
  have hk : x ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := hx
  rw [_root_.ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, hc⟩ := hk
  have key : ∀ n : ℕ, ∃ b : Acris p,
      acrisEmb p (algebraMap (Acris0 p) (Acris p) (PanBergerSplit.logPartial p hx (p ^ n)) +
        (p : Acris p) ^ n * b) = logPlus p hx' := by
    intro n
    have hmem : evalB p (algebraMap_mem_ith p (theta_xi' p)) (dpSeries p (tailSeries p c n)) ∈
        Set.range (acrisEmb p) := by
      rw [range_acrisEmb]
      exact ⟨tailSeries p c n, tailSeries_mem p c n, rfl⟩
    obtain ⟨b, hb⟩ := hmem
    refine ⟨b, ?_⟩
    rw [RingHom.map_add, RingHom.map_mul, RingHom.map_pow, map_natCast (acrisEmb p) p,
      acrisEmb_algebraMap, hb, logPlus_eq_tail p hc hx' n]
    rfl
  choose b hb using key
  have hp : ∀ n : ℕ,
      AdicCompletion.evalₐ (Ideal.span {(p : Acris0 p)}) n ((p : Acris p) ^ n) = 0 := by
    intro n
    rw [map_pow, map_natCast, ← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : Acris0 p)} ^ n)),
      ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n
  have hsum : ∀ (n : ℕ) (A B : Acris p),
      AdicCompletion.evalₐ (Ideal.span {(p : Acris0 p)}) n (A + (p : Acris p) ^ n * B) =
        AdicCompletion.evalₐ (Ideal.span {(p : Acris0 p)}) n A := by
    intro n A B
    simp only [map_add, map_mul, hp n, zero_mul, add_zero]
  have hA : ∀ n : ℕ, AdicCompletion.evalₐ (Ideal.span {(p : Acris0 p)}) n
      (algebraMap (Acris0 p) (Acris p) (PanBergerSplit.logPartial p hx (p ^ n))) =
        Ideal.Quotient.mk _ (PanBergerSplit.logPartial p hx (p ^ n)) := by
    intro n
    simp only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      AdicCompletion.evalₐ_of]
  have hT : logT p hx = algebraMap (Acris0 p) (Acris p) (PanBergerSplit.logPartial p hx (p ^ 0)) +
      (p : Acris p) ^ 0 * b 0 := by
    refine AdicCompletion.ext_evalₐ fun n => (PanBergerSplit.evalₐ_logT p hx n).trans ?_
    exact ((hsum n _ _).trans (hA n)).symm.trans
      (congrArg (AdicCompletion.evalₐ (Ideal.span {(p : Acris0 p)}) n)
        (acrisEmb_injective p ((hb n).trans (hb 0).symm)))
  exact (congrArg (acrisEmb p) hT).trans (hb 0)

end HDec.PkgI4.AbstractPeriods
