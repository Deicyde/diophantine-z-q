import ZInQKernel.Multiplication.FormalLog.ChordEval
import ZInQKernel.Multiplication.FormalLog.Identity
import ZInQKernel.Multiplication.Local.FormalLog

/-!
# The elliptic logarithm is a homomorphism on `W₁(K)`

Blueprint: `multiplication/local/formal-logarithm.md`, part 2.

Let `K` be a complete `ℤᵐ⁰`-valued field of residue characteristic `p` with `v(p) = e`
(`ResidueChar K p e`; then `K` has characteristic `0`), `v(A) ≥ 0`, and `t₁, t₂ ∈ K` with
`v(tᵢ) ≥ 1`. If `t₃ = F(t₁, t₂)` (`F = formalAdd A`), then `log t₃ = log t₁ + log t₂`
(`evalLog_add_of_hasSum`):

`log t₃ = Σ_r c_r t₃^r = Σ_r Σ_n c_r (F^r)_n t^n = Σ_n Σ_r c_r (F^r)_n t^n = Σ_n (log ∘ F)_n t^n`,

where `c_r = b_{r-1}/r`, `t^n = t₁^{n₀} t₂^{n₁}`; the double family is summable since its terms
vanish for `r > n₀ + n₁` and have valuation `≥ n₀ + n₁ - e v_p(r)`, so the sums may be
exchanged. Then `log ∘ F = log(T₁) + log(T₂)` (`formalLog_formalAdd_aux`) gives the claim. With
`z(P + Q) = F(z(P), z(Q))` (`hasSum_formalAdd`) this is `λ(P + Q) = λ(P) + λ(Q)`
(`evalLog_zCoord_add`).
-/

namespace ZInQ.Mult

open MvPowerSeries WithZero Filter

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]
variable {p e : ℕ} [Fact p.Prime]

theorem ResidueChar.charZero (h : ResidueChar K p e) : CharZero K :=
  charZero_of_inj_zero fun n hn => by
    by_contra h0
    exact h.natCast_ne_zero h0 hn

theorem degree_fin_two (n : Fin 2 →₀ ℕ) : n.degree = n 0 + n 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

theorem coeff_formalAdd_pow_eq_zero {R : Type*} [CommRing R] (A : R) {r : ℕ}
    {n : Fin 2 →₀ ℕ} (h : n 0 + n 1 < r) : coeff n (formalAdd A ^ r) = 0 :=
  coeff_pow_eq_zero_of_degree_lt (constantCoeff_formalAdd A) (by rw [degree_fin_two]; exact h)

/-- `v(b_{r-1}/r) ≥ -e v_p(r)`. -/
theorem vge_logCoeffA (h : ResidueChar K p e) {A : K} (hA : 0 ≤ vK K A) (r : ℕ) :
    Vge (vK K) (-((e : ℤ) * padicValNat p r)) (logCoeffA A r) := by
  have h1 : Vge (vK K) 0 (1 : K) := by
    show ((0 : ℤ) : WithTop ℤ) ≤ vK K 1; rw [(vK K).map_one]; rfl
  have := vge_logTerm h hA h1 r
  rw [one_pow, mul_one] at this
  exact this.mono (le_of_eq (by ring))

variable [CompleteSpace K]

/-- **`log F(t₁, t₂) = log t₁ + log t₂`** for `v(tᵢ) ≥ 1`. -/
theorem evalLog_add_of_hasSum (h : ResidueChar K p e) {A t₁ t₂ t₃ : K} (hA : 0 ≤ vK K A)
    (h₁ : 1 ≤ vK K t₁) (h₂ : 1 ≤ vK K t₂)
    (h₃ : HasSum (fun n => coeff n (formalAdd A) * monoVal t₁ t₂ n) t₃) :
    evalLog A t₃ = evalLog A t₁ + evalLog A t₂ := by
  have := h.charZero
  have iF := MvIntegral.formalAdd hA
  have ht₃ : t₃ = ev2 t₁ t₂ (formalAdd A) := h₃.tsum_eq.symm
  set f : ℕ × (Fin 2 →₀ ℕ) → K := fun q =>
    logCoeffA A q.1 * (coeff q.2 (formalAdd A ^ q.1) * monoVal t₁ t₂ q.2) with hf
  have hterm : ∀ q : ℕ × (Fin 2 →₀ ℕ),
      Vge (vK K) ((q.2 0 + q.2 1 : ℕ) - (e : ℤ) * padicValNat p q.1) (f q) := fun q =>
    ((vge_logCoeffA h hA q.1).mul (((iF.pow q.1).vge q.2).mul (vge_monoVal h₁ h₂ q.2))).mono
      (by push_cast; omega)
  have hzero : ∀ q : ℕ × (Fin 2 →₀ ℕ), q.2 0 + q.2 1 < q.1 → f q = 0 := fun q hq => by
    simp only [hf, coeff_formalAdd_pow_eq_zero A hq, zero_mul, mul_zero]
  have hsum : Summable f := by
    refine summable_of_vK_cofinite fun M => ?_
    rw [Filter.eventually_cofinite]
    refine ((Set.finite_Iio ((2 * M + 4 * e ^ 2 + 2 * e).toNat + 1)).prod
      (finite_degree_lt ((2 * M + 4 * e ^ 2 + 2 * e).toNat + 1))).subset ?_
    rintro ⟨r, n⟩ hq
    simp only [Set.mem_ofPred_eq] at hq
    have hrn : r ≤ n 0 + n 1 := by
      by_contra hc
      apply hq
      rw [hzero (r, n) (by simpa using hc), (vK K).map_zero]
      exact le_top
    have key : 2 * ((e : ℤ) * padicValNat p r) ≤ r + 4 * e ^ 2 + 2 * e := by
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · subst hr0; simp; positivity
      · have := two_mul_padicValNat_le (p := p) r e hr0.ne'
        have h' : ((2 * e * padicValNat p r : ℕ) : ℤ) ≤ ((r + 4 * e ^ 2 + 2 * e : ℕ) : ℤ) := by
          exact_mod_cast this
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at h'
        linarith
    have hdeg : n 0 + n 1 < (2 * M + 4 * e ^ 2 + 2 * e).toNat + 1 := by
      by_contra hc
      apply hq
      refine (hterm (r, n)).mono ?_
      have h1 := Int.self_le_toNat (2 * M + 4 * e ^ 2 + 2 * e)
      have h2 : ((2 * M + 4 * e ^ 2 + 2 * e).toNat : ℤ) + 1 ≤ ((n 0 + n 1 : ℕ) : ℤ) := by
        push_cast; omega
      have h3 : (r : ℤ) ≤ ((n 0 + n 1 : ℕ) : ℤ) := by exact_mod_cast hrn
      simp only
      linarith
    exact ⟨Set.mem_Iio.mpr (by omega), hdeg⟩
  have hrow : ∀ r, HasSum (fun n => f (r, n)) (logCoeffA A r * t₃ ^ r) := fun r => by
    rw [ht₃, ← ev2_pow h₁ h₂ iF r]
    exact (hasSum_ev2 h₁ h₂ (iF.pow r)).mul_left _
  have hcol : ∀ n : Fin 2 →₀ ℕ, HasSum (fun r => f (r, n))
      (coeff n (PowerSeries.subst (formalAdd A) (formalLog A)) * monoVal t₁ t₂ n) := fun n => by
    have hfin : ∀ r ∉ Finset.range (n 0 + n 1 + 1), f (r, n) = 0 := fun r hr => by
      rw [Finset.mem_range, not_lt] at hr
      exact hzero (r, n) (by simp only; omega)
    suffices e : coeff n (PowerSeries.subst (formalAdd A) (formalLog A)) * monoVal t₁ t₂ n =
        ∑ r ∈ Finset.range (n 0 + n 1 + 1), f (r, n) by
      rw [e]; exact hasSum_sum_of_ne_finset_zero hfin
    rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero
      (constantCoeff_formalAdd A)),
      finsum_eq_sum_of_support_subset _ (s := Finset.range (n 0 + n 1 + 1)), Finset.sum_mul]
    · refine Finset.sum_congr rfl fun r _ => ?_
      simp only [hf, formalLog, PowerSeries.coeff_mk, smul_eq_mul]
      ring
    · intro r hr
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra hc
      apply hr
      simp only [coeff_formalAdd_pow_eq_zero A (show n 0 + n 1 < r by omega), smul_zero]
  have hl₁ : HasSum (fun k => PowerSeries.coeff k (formalLog A) * t₁ ^ k) (evalLog A t₁) := by
    simpa only [formalLog, PowerSeries.coeff_mk, evalLog] using (summable_log h hA h₁).hasSum
  have hl₂ : HasSum (fun k => PowerSeries.coeff k (formalLog A) * t₂ ^ k) (evalLog A t₂) := by
    simpa only [formalLog, PowerSeries.coeff_mk, evalLog] using (summable_log h hA h₂).hasSum
  have hL : HasSum (fun n => coeff n (PowerSeries.subst (formalAdd A) (formalLog A)) *
      monoVal t₁ t₂ n) (evalLog A t₁ + evalLog A t₂) := by
    rw [formalLog_formalAdd_aux]
    simp only [map_add, add_mul]
    exact (hasSum_ev2_subst_X_zero hl₁).add (hasSum_ev2_subst_X_one hl₂)
  have hs' : Summable (Function.uncurry fun r n => f (r, n)) := hsum
  calc evalLog A t₃ = ∑' r, logCoeffA A r * t₃ ^ r := rfl
    _ = ∑' r, ∑' n, f (r, n) := tsum_congr fun r => (hrow r).tsum_eq.symm
    _ = ∑' n, ∑' r, f (r, n) := hs'.tsum_comm.symm
    _ = ∑' n, coeff n (PowerSeries.subst (formalAdd A) (formalLog A)) * monoVal t₁ t₂ n :=
        tsum_congr fun n => (hcol n).tsum_eq
    _ = evalLog A t₁ + evalLog A t₂ := hL.tsum_eq

/-- **The elliptic logarithm is a homomorphism**: `log z(P + Q) = log z(P) + log z(Q)` on
`W₁(K)`. -/
theorem evalLog_zCoord_add [DecidableEq K] (h : ResidueChar K p e) {A : K} (hA : 0 ≤ vK K A)
    {P Q : (shortCurve A).toAffine.Point} (hP : P ∈ W1 (vK K) A) (hQ : Q ∈ W1 (vK K) A) :
    evalLog A (zCoord (P + Q)) = evalLog A (zCoord P) + evalLog A (zCoord Q) := by
  have := h.charZero
  exact evalLog_add_of_hasSum h hA (one_le_val_zCoord hA hP) (one_le_val_zCoord hA hQ)
    (hasSum_formalAdd hA hP hQ)

end ZInQ.Mult
