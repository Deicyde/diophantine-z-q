import ZInQKernel.Contrib.OneProof.FontaineComparison

/-! # Fontaine's `A_cris` inside `B_dR^+`: the generator and the finite divided powers

Let `w` generate `ker(θ : W(R) → 𝓞_{ℂ_p})`, `R = 𝓞_{ℂ_p}^♭`. Then `w` is a unit multiple of
`ξ = p − [p̃]` (`exists_unit_of_gen`), and `W(R)[w^n/n! : n ≥ 1]`
(`FontaineComparison.finiteDividedPowers`) consists of the finite sums `Σ_{n<N} a_n w^n/n!`
with `a_n ∈ W(R)` (`exists_psum`). These are the objects of Fontaine, *Le corps des périodes
p-adiques*, Astérisque 223 (1994), Exposé II, §2.3.3 (p. 78) and §4.1.2 (p. 83).
-/

noncomputable section

namespace HDec.PkgI4.AcrisImage

open BergerBst FontaineSt BmaxOne PowerSeries Ideal
open PanBergerSplit (Ainf AinfP theta)
open FontaineComparison (finiteDividedPowers)
open _root_.ZInQ.Contrib.G9.BdrKer.Cp (xi xi_ne_zero ker_fontaineTheta_Cp witt_p_ne_zero pFlat
  untilt_pFlat)

variable {p : ℕ} [Fact p.Prime]

/-! ## §1. The generator -/

section Generator

variable {w : Ainf p}

/-- A generator of `ker θ` is a unit multiple of `ξ = p − [p̃]`. -/
theorem exists_unit_of_gen (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w}) :
    ∃ c : (Ainf p)ˣ, w = xi p * c := by
  have hw : w ∈ span {xi p} := by
    rw [← ker_fontaineTheta_Cp p, hgen]
    exact mem_span_singleton_self w
  have hx : xi p ∈ span {w} := by
    rw [← hgen, ker_fontaineTheta_Cp p]
    exact mem_span_singleton_self _
  obtain ⟨c, hc⟩ := mem_span_singleton'.mp hw
  obtain ⟨d, hd⟩ := mem_span_singleton'.mp hx
  have hcd : c * d = 1 := by
    apply mul_right_cancel₀ (xi_ne_zero p)
    rw [one_mul, mul_comm c d, mul_assoc, hc, hd]
  exact ⟨⟨c, d, hcd, by rw [mul_comm]; exact hcd⟩, hc.symm.trans (mul_comm _ _)⟩

theorem span_pow_eq (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    (m : ℕ) : span {w ^ m} = span {xi p ^ m} := by
  obtain ⟨c, rfl⟩ := exists_unit_of_gen hgen
  rw [mul_pow]
  exact span_singleton_mul_right_unit (c.isUnit.pow m) _

/-- `(ker θ)^m = (w^m)` in `W(R)[1/p]`. -/
theorem ith_pow_eq (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    (m : ℕ) : Ith p ^ m = span {algebraMap (Ainf p) (AinfP p) w ^ m} := by
  obtain ⟨c, rfl⟩ := exists_unit_of_gen hgen
  rw [ith_pow, map_mul, mul_pow]
  exact (span_singleton_mul_right_unit ((c.isUnit.map _).pow m) _).symm

/-- `W(R) ∩ (ker θ)^m ⊆ w^m W(R)` (the reverse inclusion is clear). -/
theorem mem_span_pow_of_algebraMap
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w}) (m : ℕ) {a : Ainf p}
    (h : algebraMap (Ainf p) (AinfP p) a ∈ Ith p ^ m) : a ∈ span {w ^ m} := by
  rw [span_pow_eq hgen]
  rw [ith_pow] at h
  exact mem_xi_pow_of_algebraMap p m a h

/-- `⋂_k (p^k W(R) + w^m W(R)) ⊆ w^m W(R)` (the reverse inclusion is clear). -/
theorem mem_span_pow_of_forall
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w}) (m : ℕ) {x : Ainf p}
    (h : ∀ k : ℕ, ∃ a b : Ainf p, x = (p : Ainf p) ^ k * a + w ^ m * b) :
    x ∈ span {w ^ m} := by
  rw [span_pow_eq hgen]
  obtain ⟨c, rfl⟩ := exists_unit_of_gen hgen
  refine mem_xi_pow_of_forall p m x fun k => ?_
  obtain ⟨a, b, hab⟩ := h k
  exact ⟨a, (c : Ainf p) ^ m * b, by rw [hab]; ring⟩

theorem p_dvd_of_dvd_xi_mul {u : Ainf p} (h : (p : Ainf p) ∣ xi p * u) : (p : Ainf p) ∣ u := by
  rw [← mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero] at h ⊢
  rw [WittVector.mul_coeff_zero] at h
  refine (mul_eq_zero.mp h).resolve_left fun h0 => ?_
  have h1 : WittVector.constantCoeff (xi p) = 0 := h0
  rw [xi, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub, neg_eq_zero] at h1
  have h2 : pFlat p = 0 := by simpa using h1
  have h3 := untilt_pFlat p
  rw [← WittVector.fontaineTheta_teichmuller, h2, WittVector.teichmuller_zero, map_zero] at h3
  exact ZInQ.Contrib.G9.BdrKer.Cp.p_ne_zero p h3.symm

/-- `w` is a non-zero-divisor modulo every `p^k`. -/
theorem p_pow_dvd_of_dvd_mul (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    (k : ℕ) {u : Ainf p} (h : (p : Ainf p) ^ k ∣ w * u) : (p : Ainf p) ^ k ∣ u := by
  obtain ⟨c, rfl⟩ := exists_unit_of_gen hgen
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    have h1 : (p : Ainf p) ∣ u := by
      have h2 : (p : Ainf p) ∣ xi p * (c * u) := by
        rw [← mul_assoc]
        exact (dvd_pow_self _ (Nat.succ_ne_zero k)).trans h
      have h3 := p_dvd_of_dvd_xi_mul h2
      have h4 : u = ↑c⁻¹ * (c * u) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      rw [h4]
      exact dvd_mul_of_dvd_right h3 _
    obtain ⟨v, rfl⟩ := h1
    have h5 : (p : Ainf p) * (p : Ainf p) ^ k ∣ (p : Ainf p) * (xi p * c * v) := by
      rw [← pow_succ']
      convert h using 1
      ring
    have h6 := (mul_dvd_mul_iff_left (witt_p_ne_zero p)).mp h5
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih h6)

theorem exists_eq_mul_of_theta_eq_zero
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w}) {a : Ainf p}
    (ha : theta p a = 0) : ∃ b, a = w * b := by
  have h : a ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := ha
  rw [hgen, mem_span_singleton'] at h
  obtain ⟨b, hb⟩ := h
  exact ⟨b, by rw [← hb, mul_comm]⟩

theorem algebraMap_injective : Function.Injective (algebraMap (Ainf p) (AinfP p)) :=
  IsLocalization.injective (AinfP p)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (witt_p_ne_zero p))

end Generator

/-! ## §2. Divided powers and their finite sums -/

section DividedPowers

variable (w : Ainf p)

/-- The divided power `γ_n = w^n/n!` in `W(R)[1/p]`. -/
def gam (n : ℕ) : AinfP p :=
  algebraMap (Ainf p) (AinfP p) w ^ n * qpToLoc p (((n.factorial : ℕ) : ℚ_[p])⁻¹)

theorem gam_zero : gam w 0 = 1 := by
  simp [gam]

theorem factorial_mul_gam (n : ℕ) :
    ((n.factorial : ℕ) : AinfP p) * gam w n = algebraMap (Ainf p) (AinfP p) w ^ n := by
  have h := natCast_mul_qp p n.factorial (Nat.factorial_ne_zero n)
  rw [gam, mul_left_comm, h, mul_one]

theorem isUnit_natCast_factorial (n : ℕ) : IsUnit ((n.factorial : ℕ) : AinfP p) := by
  have h := natCast_mul_qp p n.factorial (Nat.factorial_ne_zero n)
  exact ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩

theorem succ_mul_gam_succ (n : ℕ) :
    ((n + 1 : ℕ) : AinfP p) * gam w (n + 1) = algebraMap (Ainf p) (AinfP p) w * gam w n := by
  apply (isUnit_natCast_factorial n).mul_left_cancel
  calc ((n.factorial : ℕ) : AinfP p) * (((n + 1 : ℕ) : AinfP p) * gam w (n + 1))
      = (((n + 1).factorial : ℕ) : AinfP p) * gam w (n + 1) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
    _ = algebraMap (Ainf p) (AinfP p) w ^ (n + 1) := factorial_mul_gam w (n + 1)
    _ = ((n.factorial : ℕ) : AinfP p) * (algebraMap (Ainf p) (AinfP p) w * gam w n) := by
        rw [mul_left_comm, factorial_mul_gam, pow_succ']

theorem gam_mul (a b : ℕ) :
    gam w a * gam w b = (((a + b).choose a : ℕ) : AinfP p) * gam w (a + b) := by
  apply ((isUnit_natCast_factorial a).mul (isUnit_natCast_factorial b)).mul_left_cancel
  have hc := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  rw [Nat.add_sub_cancel_left] at hc
  calc ((a.factorial : ℕ) : AinfP p) * ((b.factorial : ℕ) : AinfP p) * (gam w a * gam w b)
      = (((a.factorial : ℕ) : AinfP p) * gam w a) * (((b.factorial : ℕ) : AinfP p) * gam w b) := by
        ring
    _ = algebraMap (Ainf p) (AinfP p) w ^ (a + b) := by
        rw [factorial_mul_gam, factorial_mul_gam, pow_add]
    _ = (((a + b).factorial : ℕ) : AinfP p) * gam w (a + b) := (factorial_mul_gam w (a + b)).symm
    _ = ((a.factorial : ℕ) : AinfP p) * ((b.factorial : ℕ) : AinfP p) *
          ((((a + b).choose a : ℕ) : AinfP p) * gam w (a + b)) := by
        rw [← hc]
        push_cast
        ring

/-- The partial sums `Σ_{n<N} a_n γ_n` of a divided-power series. -/
def psum (f : (Ainf p)⟦X⟧) (N : ℕ) : AinfP p :=
  ∑ n ∈ Finset.range N, algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff n f) * gam w n

theorem trunc_dpSeries_eval (f : (Ainf p)⟦X⟧) (N : ℕ) :
    (trunc N (dpSeries p f)).eval (algebraMap (Ainf p) (AinfP p) w) = psum w f N := by
  rw [Polynomial.eval, eval₂_trunc_eq_sum_range]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [dpSeries, PowerSeries.coeff_mk, RingHom.id_apply, gam]
  ring

/-- Modulo `(ker θ)^m`, the series `Σ a_n γ_n` is its partial sum below `m`. -/
theorem evB_evalB_dpSeries (hw : theta p w = 0) (f : (Ainf p)⟦X⟧) (m : ℕ) :
    evB p m (evalB p (algebraMap_mem_ith p hw) (dpSeries p f)) =
      Ideal.Quotient.mk _ (psum w f m) := by
  rw [evB_evalB, trunc_dpSeries_eval]

theorem psum_zero_right (f : (Ainf p)⟦X⟧) : psum w f 0 = 0 := by
  simp [psum]

theorem psum_succ (f : (Ainf p)⟦X⟧) (N : ℕ) :
    psum w f (N + 1) = psum w f N + algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff N f) * gam w N :=
  Finset.sum_range_succ _ _

theorem psum_add (f g : (Ainf p)⟦X⟧) (N : ℕ) : psum w (f + g) N = psum w f N + psum w g N := by
  simp only [psum, map_add, add_mul, Finset.sum_add_distrib]

theorem psum_neg (f : (Ainf p)⟦X⟧) (N : ℕ) : psum w (-f) N = -psum w f N := by
  simp only [psum, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem psum_sub (f g : (Ainf p)⟦X⟧) (N : ℕ) : psum w (f - g) N = psum w f N - psum w g N := by
  rw [sub_eq_add_neg, psum_add, psum_neg, ← sub_eq_add_neg]

theorem psum_zero_left (N : ℕ) : psum w 0 N = 0 := by
  simp [psum]

theorem psum_sub_psum (f : (Ainf p)⟦X⟧) {N M : ℕ} (h : N ≤ M) :
    psum w f M - psum w f N =
      ∑ n ∈ Finset.Ico N M, algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff n f) * gam w n := by
  rw [psum, psum, ← Finset.sum_range_add_sum_Ico _ h, add_sub_cancel_left]

/-- Beyond the last nonzero coefficient the partial sums are constant. -/
theorem psum_eq_of_le {f : (Ainf p)⟦X⟧} {N M : ℕ} (hNM : N ≤ M)
    (hf : ∀ n, N ≤ n → PowerSeries.coeff n f = 0) : psum w f M = psum w f N := by
  rw [← sub_eq_zero, psum_sub_psum w f hNM]
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [hf n (Finset.mem_Ico.mp hn).1, map_zero, zero_mul]

theorem psum_C (a : Ainf p) {N : ℕ} (hN : 1 ≤ N) :
    psum w (C a) N = algebraMap (Ainf p) (AinfP p) a := by
  rw [psum_eq_of_le w hN fun n hn => by rw [PowerSeries.coeff_C, ite_eq_right (by omega)]]
  simp [psum, gam_zero]

theorem psum_monomial (n : ℕ) (a : Ainf p) :
    psum w (monomial n a) (n + 1) = algebraMap (Ainf p) (AinfP p) a * gam w n := by
  rw [psum_succ]
  have h0 : psum w (monomial n a) n = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [PowerSeries.coeff_monomial, ite_eq_right (by have := Finset.mem_range.mp hi; omega), map_zero, zero_mul]
  rw [h0, zero_add, PowerSeries.coeff_monomial, ite_eq_left rfl]

/-- Pulling `p^k` out of a partial sum whose coefficients are divisible by `p^k`. -/
theorem exists_psum_eq_pow_mul {f : (Ainf p)⟦X⟧} {k : ℕ} (s : Finset ℕ)
    (h : ∀ n ∈ s, (p : Ainf p) ^ k ∣ PowerSeries.coeff n f) :
    ∃ g : (Ainf p)⟦X⟧, ∑ n ∈ s, algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff n f) * gam w n =
      (p : AinfP p) ^ k * ∑ n ∈ s, algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff n g) * gam w n := by
  classical
  choose! c hc using h
  refine ⟨mk c, ?_⟩
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [hc n hn, PowerSeries.coeff_mk, map_mul, map_pow, map_natCast]
  ring

end DividedPowers

/-! ## §3. `W(R)[w^n/n!]` is the set of finite sums `Σ a_n γ_n` -/

section Membership

variable (w : Ainf p)

theorem gam_mem (n : ℕ) : gam w n ∈ finiteDividedPowers p w := by
  cases n with
  | zero => rw [gam_zero]; exact Subring.one_mem _
  | succ n => exact Subring.subset_closure (Or.inr ⟨n, rfl⟩)

theorem algebraMap_mem_fdp (a : Ainf p) :
    algebraMap (Ainf p) (AinfP p) a ∈ finiteDividedPowers p w :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem psum_mem (f : (Ainf p)⟦X⟧) (N : ℕ) : psum w f N ∈ finiteDividedPowers p w :=
  Subring.sum_mem _ fun n _ => Subring.mul_mem _ (algebraMap_mem_fdp w _) (gam_mem w n)

theorem sum_gam_mem (s : Finset ℕ) (c : ℕ → Ainf p) :
    ∑ n ∈ s, algebraMap (Ainf p) (AinfP p) (c n) * gam w n ∈ finiteDividedPowers p w :=
  Subring.sum_mem _ fun n _ => Subring.mul_mem _ (algebraMap_mem_fdp w _) (gam_mem w n)

/-- An element is a finite sum `Σ_{n<N} a_n γ_n`, with `a_n = 0` for `n ≥ N`. -/
def IsPsum (x : AinfP p) : Prop :=
  ∃ (f : (Ainf p)⟦X⟧) (N : ℕ), (∀ n, N ≤ n → PowerSeries.coeff n f = 0) ∧ x = psum w f N

theorem isPsum_add {x y : AinfP p} (hx : IsPsum w x) (hy : IsPsum w y) : IsPsum w (x + y) := by
  obtain ⟨f, N, hf, rfl⟩ := hx
  obtain ⟨g, M, hg, rfl⟩ := hy
  refine ⟨f + g, max N M, fun n hn => ?_, ?_⟩
  · rw [map_add, hf n (le_of_max_le_left hn), hg n (le_of_max_le_right hn), add_zero]
  · rw [psum_add, psum_eq_of_le w (le_max_left N M) hf, psum_eq_of_le w (le_max_right N M) hg]

theorem isPsum_zero : IsPsum w 0 :=
  ⟨0, 0, fun _ _ => map_zero _, (psum_zero_left w 0).symm⟩

theorem isPsum_sum (s : Finset ℕ) (g : ℕ → AinfP p) (h : ∀ i ∈ s, IsPsum w (g i)) :
    IsPsum w (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isPsum_zero w
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isPsum_add w (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isPsum_term (a : Ainf p) (n : ℕ) : IsPsum w (algebraMap (Ainf p) (AinfP p) a * gam w n) :=
  ⟨monomial n a, n + 1, fun m hm => by rw [PowerSeries.coeff_monomial, ite_eq_right (by omega)],
    (psum_monomial w n a).symm⟩

theorem isPsum_neg {x : AinfP p} (hx : IsPsum w x) : IsPsum w (-x) := by
  obtain ⟨f, N, hf, rfl⟩ := hx
  exact ⟨-f, N, fun n hn => by rw [map_neg, hf n hn, neg_zero], (psum_neg w f N).symm⟩

theorem isPsum_mul {x y : AinfP p} (hx : IsPsum w x) (hy : IsPsum w y) : IsPsum w (x * y) := by
  obtain ⟨f, N, -, rfl⟩ := hx
  obtain ⟨g, M, -, rfl⟩ := hy
  rw [psum, psum, Finset.sum_mul_sum]
  refine isPsum_sum w _ _ fun i _ => isPsum_sum w _ _ fun j _ => ?_
  have h : algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff i f) * gam w i *
      (algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff j g) * gam w j) =
      algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff i f * PowerSeries.coeff j g * ((i + j).choose i : ℕ)) *
        gam w (i + j) := by
    rw [map_mul, map_mul, map_natCast, mul_mul_mul_comm, gam_mul]
    ring
  rw [h]
  exact isPsum_term w _ _

/-- **Every element of `W(R)[w^n/n!]` is a finite sum `Σ_{n<N} a_n w^n/n!`.** -/
theorem exists_psum {x : AinfP p} (hx : x ∈ finiteDividedPowers p w) : IsPsum w x := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨n, rfl⟩
    · have h := isPsum_term w a 0
      rwa [gam_zero, mul_one] at h
    · have h := isPsum_term w 1 (n + 1)
      rwa [map_one, one_mul] at h
  | zero => exact isPsum_zero w
  | one =>
    have h := isPsum_term w 1 0
    rwa [gam_zero, mul_one, map_one] at h
  | add x y _ _ hx hy => exact isPsum_add w hx hy
  | neg x _ hx => exact isPsum_neg w hx
  | mul x y _ _ hx hy => exact isPsum_mul w hx hy

/-- `γ_n ∈ (ker θ)^m` for `n ≥ m`. -/
theorem gam_mem_ith_pow (hw : theta p w = 0) {m n : ℕ} (h : m ≤ n) : gam w n ∈ Ith p ^ m := by
  rw [gam]
  refine Ideal.mul_mem_right _ _ ?_
  rw [← Nat.sub_add_cancel h, pow_add]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (algebraMap_mem_ith p hw) m)

/-- The tail of a partial sum beyond `m` lies in `(ker θ)^m`. -/
theorem psum_sub_psum_mem (hw : theta p w = 0) (f : (Ainf p)⟦X⟧) {m N : ℕ} (h : m ≤ N) :
    psum w f N - psum w f m ∈ Ith p ^ m := by
  rw [psum_sub_psum w f h]
  exact Ideal.sum_mem _ fun n hn =>
    Ideal.mul_mem_left _ _ (gam_mem_ith_pow w hw (Finset.mem_Ico.mp hn).1)

end Membership

end HDec.PkgI4.AcrisImage
