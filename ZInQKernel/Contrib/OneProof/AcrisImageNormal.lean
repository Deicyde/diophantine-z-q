import ZInQKernel.Contrib.OneProof.AcrisImageBasic

/-! # Normalizing the coefficients of a divided-power series

Fontaine, Astérisque 223 (1994), Exposé II, §4.1.2, p. 83: for a generator `w` of `ker θ`,
the coefficients of `Σ a_n w^n/n!` can be chosen with `θ(a_n) ≠ 0` whenever `a_n ≠ 0`
(`exists_normalized`). For such a series, vanishing in `B_dR^+` forces every coefficient to
vanish (`eq_zero_of_normalized`), which gives the injectivity of `A_cris → B_dR^+`.
-/

noncomputable section

namespace HDec.PkgI4.AcrisImage

open BergerBst FontaineSt BmaxOne PowerSeries Ideal
open PanBergerSplit (Ainf AinfP theta)
open FontaineComparison (finiteDividedPowers)

variable {p : ℕ} [Fact p.Prime] {w : Ainf p}

/-! ## The carry construction

Every `x ∈ W(R)` is split as `x = r + w u`: on `w W(R)` take `r = 0` and `u` a chosen quotient
by `w`, off `w W(R)` take `r = x` and `u = 0`. With `t_0 = a_0` and `t_{n+1} = a_{n+1} + (n+1) u_n`
(where `t_n = r_n + w u_n`), the normalized coefficients are the `r_n`. -/

open Classical in
/-- A quotient of `x` by `w` when `x ∈ w W(R)`, and `0` otherwise. -/
private def wQuot (w x : Ainf p) : Ainf p :=
  if h : ∃ b, x = w * b then h.choose else 0

open Classical in
/-- The part of `x` kept as a coefficient: `0` when `x ∈ w W(R)`, and `x` otherwise. -/
private def wRem (w x : Ainf p) : Ainf p :=
  if ∃ b, x = w * b then 0 else x

private theorem wRem_add_wQuot (w x : Ainf p) : x = wRem w x + w * wQuot w x := by
  unfold wRem wQuot
  split_ifs with h
  · rw [zero_add]
    exact h.choose_spec
  · rw [mul_zero, add_zero]

private theorem wRem_normalized
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w}) (x : Ainf p) :
    wRem w x = 0 ∨ theta p (wRem w x) ≠ 0 := by
  unfold wRem
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr fun hx => h (exists_eq_mul_of_theta_eq_zero hgen hx)

private theorem dvd_wQuot
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w}) (k : ℕ) {x : Ainf p}
    (h : (p : Ainf p) ^ k ∣ x) : (p : Ainf p) ^ k ∣ wQuot w x := by
  unfold wQuot
  split_ifs with hx
  · apply p_pow_dvd_of_dvd_mul hgen k
    rw [← hx.choose_spec]
    exact h
  · exact dvd_zero _

private theorem dvd_wRem (k : ℕ) {x : Ainf p} (h : (p : Ainf p) ^ k ∣ x) :
    (p : Ainf p) ^ k ∣ wRem w x := by
  unfold wRem
  split_ifs
  · exact dvd_zero _
  · exact h

/-- The carried coefficients: `t_0 = a_0` and `t_{n+1} = a_{n+1} + (n+1) u_n`, where
`u_n = t_n / w` when `t_n ∈ w W(R)`, and `u_n = 0` otherwise. -/
private def carrySeq (w : Ainf p) (a : ℕ → Ainf p) : ℕ → Ainf p
  | 0 => a 0
  | n + 1 => a (n + 1) + ((n + 1 : ℕ) : Ainf p) * wQuot w (carrySeq w a n)

private theorem carrySeq_zero (w : Ainf p) (a : ℕ → Ainf p) : carrySeq w a 0 = a 0 := rfl

private theorem carrySeq_succ (w : Ainf p) (a : ℕ → Ainf p) (n : ℕ) :
    carrySeq w a (n + 1) = a (n + 1) + ((n + 1 : ℕ) : Ainf p) * wQuot w (carrySeq w a n) :=
  rfl

/-- The normalized series: its `n`-th coefficient is the kept part of `t_n`. -/
private def normSeries (w : Ainf p) (f : (Ainf p)⟦X⟧) : (Ainf p)⟦X⟧ :=
  PowerSeries.mk fun n => wRem w (carrySeq w (fun m => PowerSeries.coeff m f) n)

private theorem coeff_normSeries (w : Ainf p) (f : (Ainf p)⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (normSeries w f) =
      wRem w (carrySeq w (fun m => PowerSeries.coeff m f) n) := by
  rw [normSeries, PowerSeries.coeff_mk]

/-- The partial sums of `f` and of its normalization differ by a single carry term: using
`w u · γ_N = (N+1) u · γ_{N+1}`, the `w`-divisible part of `t_N` moves to the next index. -/
private theorem psum_sub_psum_normSeries (f : (Ainf p)⟦X⟧) (N : ℕ) :
    psum w f (N + 1) - psum w (normSeries w f) (N + 1) =
      algebraMap (Ainf p) (AinfP p)
          (((N + 1 : ℕ) : Ainf p) * wQuot w (carrySeq w (fun m => PowerSeries.coeff m f) N)) *
        gam w (N + 1) := by
  induction N with
  | zero =>
    have hs := congrArg (algebraMap (Ainf p) (AinfP p))
      (wRem_add_wQuot w (PowerSeries.coeff 0 f))
    have hγ := succ_mul_gam_succ w 0
    rw [map_add, map_mul] at hs
    rw [map_mul, map_natCast, psum_succ, psum_succ, psum_zero_right, psum_zero_right,
      coeff_normSeries, carrySeq_zero]
    linear_combination gam w 0 * hs -
      algebraMap (Ainf p) (AinfP p) (wQuot w (PowerSeries.coeff 0 f)) * hγ
  | succ N ih =>
    have hs := congrArg (algebraMap (Ainf p) (AinfP p))
      (wRem_add_wQuot w (carrySeq w (fun m => PowerSeries.coeff m f) (N + 1)))
    have ht := congrArg (algebraMap (Ainf p) (AinfP p))
      (carrySeq_succ w (fun m => PowerSeries.coeff m f) N)
    have hγ := succ_mul_gam_succ w (N + 1)
    rw [map_add, map_mul] at hs
    rw [map_add, map_mul, map_natCast] at ht
    rw [map_mul, map_natCast] at ih ⊢
    rw [psum_succ w f (N + 1), psum_succ w (normSeries w f) (N + 1), coeff_normSeries]
    linear_combination ih - gam w (N + 1) * ht + gam w (N + 1) * hs -
      algebraMap (Ainf p) (AinfP p)
        (wQuot w (carrySeq w (fun m => PowerSeries.coeff m f) (N + 1))) * hγ

/-- **The carried coefficients tend to `0`.** Fix `k` and `M` with `p^k ∣ a_n` for `n ≥ M`. For
`q ≤ k`, `p^q ∣ t_n` for all `n ≥ M + p q`: among `p` consecutive indices there is a multiple
`m + 1` of `p`, where `t_{m+1} = a_{m+1} + (m+1) u_m` gains a factor `p` (`p^q ∣ t_m` gives
`p^q ∣ u_m`, since `w` is a non-zero-divisor modulo `p^q`), and the divisibility then propagates
to all later indices. -/
private theorem pAdicNull_carrySeq
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w}) {a : ℕ → Ainf p}
    (ha : PAdicNull p a) : PAdicNull p (carrySeq w a) := by
  unfold PAdicNull at ha ⊢
  intro k
  obtain ⟨M, hM⟩ := ha k
  have hstep : ∀ q ≤ k, ∀ m, M ≤ m → (p : Ainf p) ^ q ∣ carrySeq w a m →
      (p : Ainf p) ^ q ∣ carrySeq w a (m + 1) := by
    intro q hq m hm h
    rw [carrySeq_succ]
    exact dvd_add ((pow_dvd_pow _ hq).trans (hM (m + 1) (by omega)))
      (dvd_mul_of_dvd_right (dvd_wQuot hgen q h) _)
  have hjump : ∀ q < k, ∀ m, M ≤ m → (p : Ainf p) ^ q ∣ carrySeq w a m → p ∣ m + 1 →
      (p : Ainf p) ^ (q + 1) ∣ carrySeq w a (m + 1) := by
    intro q hq m hm h hdvd
    rw [carrySeq_succ]
    refine dvd_add ((pow_dvd_pow _ (by omega : q + 1 ≤ k)).trans (hM (m + 1) (by omega))) ?_
    rw [pow_succ']
    exact mul_dvd_mul (Nat.cast_dvd_cast hdvd) (dvd_wQuot hgen q h)
  have hmain : ∀ q ≤ k, ∀ n, M + p * q ≤ n → (p : Ainf p) ^ q ∣ carrySeq w a n := by
    intro q
    induction q with
    | zero =>
      intro _ n _
      rw [pow_zero]
      exact one_dvd _
    | succ q ih =>
      intro hq n hn
      rw [mul_add_one] at hn
      have hp : 0 < p := (Fact.out : p.Prime).pos
      obtain ⟨n₁, h1, h2, hdiv⟩ : ∃ n₁, M + p * q < n₁ ∧ n₁ ≤ M + p * q + p ∧ p ∣ n₁ := by
        refine ⟨p * ((M + p * q) / p + 1), Nat.lt_mul_div_succ _ hp, ?_, Dvd.intro _ rfl⟩
        rw [mul_add_one]
        have := Nat.mul_div_le (M + p * q) p
        omega
      have hbase : (p : Ainf p) ^ (q + 1) ∣ carrySeq w a n₁ := by
        obtain ⟨m, rfl⟩ : ∃ m, n₁ = m + 1 := ⟨n₁ - 1, by omega⟩
        exact hjump q (by omega) m (by omega) (ih (by omega) m (by omega)) hdiv
      have hprop : ∀ j, (p : Ainf p) ^ (q + 1) ∣ carrySeq w a (n₁ + j) := by
        intro j
        induction j with
        | zero => exact hbase
        | succ j ihj => exact hstep (q + 1) hq (n₁ + j) (by omega) ihj
      obtain ⟨j, rfl⟩ : ∃ j, n = n₁ + j := ⟨n - n₁, by omega⟩
      exact hprop j
  exact ⟨M + p * k, fun n hn => hmain k le_rfl n hn⟩

/-- **Normalization** (carry the `θ`-null part `w b` of each carried coefficient to the next
index: `w b · w^n/n! = (n+1) b · w^{n+1}/(n+1)!`). The partial sums of `f` and of the
normalized `g` agree modulo `p^k D` from some point on. -/
theorem exists_normalized
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    {f : (Ainf p)⟦X⟧} (hf : f ∈ restricted p) :
    ∃ g ∈ restricted p, (∀ n, PowerSeries.coeff n g = 0 ∨ theta p (PowerSeries.coeff n g) ≠ 0) ∧
      ∀ k, ∃ N₀, ∀ N, N₀ ≤ N → ∃ e ∈ finiteDividedPowers p w,
        psum w f N - psum w g N = (p : AinfP p) ^ k * e := by
  have hf' : PAdicNull p fun n => PowerSeries.coeff n f := hf
  have ht : PAdicNull p (carrySeq w fun m => PowerSeries.coeff m f) :=
    pAdicNull_carrySeq hgen hf'
  refine ⟨normSeries w f, ?_, fun n => ?_, fun k => ?_⟩
  · show PAdicNull p fun n => PowerSeries.coeff n (normSeries w f)
    intro k
    obtain ⟨N, hN⟩ := ht k
    refine ⟨N, fun n hn => ?_⟩
    show (p : Ainf p) ^ k ∣ PowerSeries.coeff n (normSeries w f)
    rw [coeff_normSeries]
    exact dvd_wRem k (hN n hn)
  · rw [coeff_normSeries]
    exact wRem_normalized hgen _
  · obtain ⟨N₁, hN₁⟩ := ht k
    refine ⟨N₁ + 1, fun N hN => ?_⟩
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    obtain ⟨d, hd⟩ := dvd_mul_of_dvd_right (dvd_wQuot hgen k (hN₁ M (by omega)))
      ((M + 1 : ℕ) : Ainf p)
    refine ⟨algebraMap (Ainf p) (AinfP p) d * gam w (M + 1),
      Subring.mul_mem _ (algebraMap_mem_fdp w d) (gam_mem w _), ?_⟩
    rw [psum_sub_psum_normSeries, hd, map_mul, map_pow, map_natCast, mul_assoc]

/-- **A normalized series whose partial sums lie in the filtration is zero**: if the lowest
nonzero coefficient is `a_n`, then `a_n w^n/n! ∈ (ker θ)^{n+1}`, so `θ(a_n) = 0`. -/
theorem eq_zero_of_normalized
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    {g : (Ainf p)⟦X⟧} (hg : ∀ n, PowerSeries.coeff n g = 0 ∨ theta p (PowerSeries.coeff n g) ≠ 0)
    (h0 : ∀ m, psum w g m ∈ Ith p ^ m) : g = 0 := by
  have hw : algebraMap (Ainf p) (AinfP p) w ≠ 0 := by
    obtain ⟨c, hc⟩ := exists_unit_of_gen hgen
    have hw0 : w ≠ 0 := by
      rw [hc]
      exact mul_ne_zero (_root_.ZInQ.Contrib.G9.BdrKer.Cp.xi_ne_zero p) c.ne_zero
    intro h
    exact hw0 (algebraMap_injective (h.trans (map_zero _).symm))
  have hcoeff : ∀ n, PowerSeries.coeff n g = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have hlow : psum w g n = 0 :=
        Finset.sum_eq_zero fun m hm => by
          rw [ih m (Finset.mem_range.mp hm), map_zero, zero_mul]
      have h1 := h0 (n + 1)
      rw [psum_succ, hlow, zero_add, ith_pow_eq hgen] at h1
      have h2 := Ideal.mul_mem_left _ ((n.factorial : ℕ) : AinfP p) h1
      rw [mul_left_comm, factorial_mul_gam] at h2
      obtain ⟨c, hc⟩ := mem_span_singleton'.mp h2
      have h3 : algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff n g) =
          c * algebraMap (Ainf p) (AinfP p) w := by
        apply mul_right_cancel₀ (pow_ne_zero n hw)
        rw [← hc]
        ring
      have h4 : algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff n g) ∈ Ith p ^ 1 := by
        rw [ith_pow_eq hgen, pow_one, h3]
        exact Ideal.mul_mem_left _ _ (mem_span_singleton_self _)
      have h5 := mem_span_pow_of_algebraMap hgen 1 h4
      rw [pow_one, ← hgen, RingHom.mem_ker] at h5
      exact (hg n).resolve_right (not_not.mpr h5)
  ext n
  rw [hcoeff n, map_zero]

end HDec.PkgI4.AcrisImage
