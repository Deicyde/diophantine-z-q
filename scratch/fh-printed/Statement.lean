import ZInQKernel.Contrib.OneProof.FHNonvanishing.TwistFE
import ZInQKernel.Contrib.OneProof.FHPrinted.LocalNorm

open HeckeRing.GL2 UpperHalfPlane

namespace ZInQ.FHPrinted

open ZInQ.GZDecomp ZInQ.GZFH

/-! ## The printed objects -/

/-- **The local component `χ_{d,v}` of the quadratic idele class character of `ℚ(√d)`** at a
place `v` with completion `K = ℚ_v`: the character of `K^×` whose kernel is the norm group
`N(K(√d)^×)` (local class field theory), i.e. the Hilbert symbol `(d, ·)_v`:
`χ_{d,v}(x) = 1` if `x = y² − d z²` with `y, z ∈ K`, and `−1` otherwise. -/
noncomputable def localChar (K : Type*) [Field K] (d : ℤ) (x : Kˣ) : ℤ := by
  classical
  exact if IsLocalNorm K d (x : K) then 1 else -1

/-- The Dirichlet coefficients `aₙ(f) χ_d(n)` of `L(s, π_f ⊗ χ_d)` (classical normalization
`s ↦ s − ½`), with `χ_d(n)` the Dirichlet coefficient of the idele class character of `ℚ(√d)`
(`idelicChar`). -/
noncomputable def printedTwistCoeff {N : ℕ} [NeZero N] (f : Newform N 2) (d : ℤ) (n : ℕ) : ℂ :=
  coeff f n * (idelicChar d n : ℂ)

/-- **`ε(½, π_f ⊗ χ_{D₀}) = 1`**: the completed L-function of `π_f ⊗ χ_{D₀}`,
`Λ(s) = q^{s/2} (2π)^{−s} Γ(s) L(s − ½, π_f ⊗ χ_{D₀})` (`ZInQ.Literature.completedL`, the entire
continuation `G` of `∑ aₙ(f) χ_{D₀}(n) n^{−s}`), satisfies the functional equation
`Λ(2 − s) = Λ(s)` (sign `+1`) for some conductor `q ≥ 1`, on the strip `0 < Re s < 2`. -/
def RootNumberTwistEqOne {N : ℕ} [NeZero N] (f : Newform N 2) (D₀ : ℤ) : Prop :=
  ∃ q : ℕ, 0 < q ∧ ∃ G : ℂ → ℂ, IsEntireCont (printedTwistCoeff f D₀) 2 G ∧
    ∀ s : ℂ, 0 < s.re → s.re < 2 →
      ZInQ.Literature.completedL q G (2 - s) = ZInQ.Literature.completedL q G s

/-- **`L(½, π_f ⊗ χ_d) ≠ 0`**, read classically: the entire continuation `G` of
`∑ aₙ(f) χ_d(n) n^{−s}` does not vanish at the centre `s = 1`. -/
def CentralValueNeZero {N : ℕ} [NeZero N] (f : Newform N 2) (d : ℤ) : Prop :=
  ∀ G : ℂ → ℂ, IsEntireCont (printedTwistCoeff f d) 2 G → G 1 ≠ 0

/-- **Friedberg–Hoffstein 1995, Theorem B, printed form** (specialized). -/
def FriedbergHoffsteinB_Printed : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
  ∀ S : Finset ℕ, (∀ p : ℕ, p.Prime → p ∣ 2 * N → p ∈ S) →
  ∀ D₀ : ℤ, IsOddFundDisc D₀ → (∀ p ∈ S, ¬ (p : ℤ) ∣ D₀) →
    RootNumberTwistEqOne f D₀ →
    Set.Infinite {d : ℤ | Squarefree d ∧ d ≠ 1 ∧
      (∀ (p : ℕ) [Fact p.Prime], p ∈ S → localChar ℚ_[p] d = localChar ℚ_[p] D₀) ∧
      localChar ℝ d = localChar ℝ D₀ ∧ CentralValueNeZero f d}

/-! ## The dictionary -/

theorem localNorm_iff_of_localChar_eq {K : Type*} [Field K] {d D : ℤ}
    (h : localChar K d = localChar K D) {x : K} (hx : x ≠ 0) :
    IsLocalNorm K d x ↔ IsLocalNorm K D x := by
  have := congrFun h (Units.mk0 x hx)
  simp only [localChar, Units.val_mk0] at this
  by_cases h1 : IsLocalNorm K d x <;> by_cases h2 : IsLocalNorm K D x <;>
    simp only [h1, h2, ite_true, ite_false, iff_true, iff_false, not_true] at this ⊢
  · norm_num at this
  · norm_num at this

theorem printedTwistCoeff_eq {N : ℕ} [NeZero N] (f : Newform N 2) {d : ℤ} (hd : IsOddFundDisc d)
    {n : ℕ} (hn : n ≠ 0) : printedTwistCoeff f d n = twistCoeff f d n := by
  rw [printedTwistCoeff, twistCoeff, chiD, idelicChar_eq_jacobiSym hd.2.1 hd.2.2 n hn]

theorem exists_natAbs_gt_of_infinite {s : Set ℤ} (hs : s.Infinite) (B : ℕ) :
    ∃ d ∈ s, B < d.natAbs := by
  obtain ⟨d, hd, hdB⟩ := hs.exists_notMem_finset (Finset.Icc (-(B : ℤ)) B)
  refine ⟨d, hd, ?_⟩
  rw [Finset.mem_Icc] at hdB
  omega

/-- **The dictionary: the printed form of Friedberg–Hoffstein gives the functional-equation
form.** -/
theorem friedbergHoffsteinB_FE_of_printed (h : FriedbergHoffsteinB_Printed) :
    FriedbergHoffsteinB_FE := by
  intro N _ f hχ S hS D₀ hD₀ hSD₀ ⟨G, hG, hFE⟩ B
  have hD₀0 : D₀ ≠ 0 := by have := hD₀.2.1; omega
  have hroot : RootNumberTwistEqOne f D₀ :=
    ⟨N * D₀.natAbs ^ 2, by have := NeZero.pos N; positivity, G,
      isEntireCont_congr (fun n hn => (printedTwistCoeff_eq f hD₀ hn).symm) hG, hFE⟩
  obtain ⟨d, ⟨hdsq, hd1, hloc, hinf, hL⟩, hdB⟩ :=
    exists_natAbs_gt_of_infinite (h N f hχ S hS D₀ hD₀ hSD₀ hroot) B
  have h2S : 2 ∈ S := hS 2 Nat.prime_two (dvd_mul_right 2 N)
  obtain ⟨hd4, hsq2⟩ := isSquare_div_two_of_localNorm_iff hdsq hD₀.2.1
    (fun x hx => localNorm_iff_of_localChar_eq (hloc 2 h2S) hx)
  have hdf : IsOddFundDisc d := ⟨hd1, hd4, hdsq⟩
  refine ⟨d, hdB, hdf, ?_, ?_, ?_⟩
  · exact pos_mul_of_real_iff hdsq.ne_zero hD₀0
      (localNorm_iff_of_localChar_eq hinf (by norm_num))
  · intro p _ hpS
    by_cases hp2 : p = 2
    · subst hp2; exact hsq2
    · exact isSquare_div_of_localNorm_iff hp2 hdsq (hSD₀ p hpS)
        (fun x hx => localNorm_iff_of_localChar_eq (hloc p hpS) hx)
  · intro G' hG'
    exact hL G' (isEntireCont_congr (fun n hn => (printedTwistCoeff_eq f hdf hn).symm) hG')

/-! ## The root-number clause is `ε(½, π_f ⊗ χ_{D₀}) = χ_{D₀}(−N) ε(f) = 1` -/

theorem isOpen_strip : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 2} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

/-- A nonzero entire function does not vanish identically on the strip `0 < Re s < 2`. -/
theorem exists_ne_zero_on_strip {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hG0 : G ≠ 0) :
    ∃ s : ℂ, 0 < s.re ∧ s.re < 2 ∧ G s ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hU : {s : ℂ | 0 < s.re ∧ s.re < 2} ∈ nhds (1 : ℂ) :=
    isOpen_strip.mem_nhds (by simp)
  have hev : G =ᶠ[nhds (1 : ℂ)] 0 := Filter.mem_of_superset hU (fun s hs => hcon s hs.1 hs.2)
  have hGa := Complex.analyticOnNhd_univ_iff_differentiable.mpr hG
  apply hG0
  funext z
  exact hGa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 1)
    hev (Set.mem_univ z)

open CongruenceSubgroup in
/-- The entire continuation of `L(f ⊗ χ_D, s)` is not identically zero (`a₁ = 1`). -/
theorem twist_cont_ne_zero {N : ℕ} [NeZero N] (f : Newform N 2) {D : ℤ} (hD : D ≠ 0)
    {G : ℂ → ℂ} (hG : IsEntireCont (twistCoeff f D) 2 G) : G ≠ 0 := by
  have : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD⟩
  have : NeZero (N * D.natAbs * D.natAbs) :=
    ⟨mul_ne_zero (mul_ne_zero (NeZero.ne N) (NeZero.ne _)) (NeZero.ne _)⟩
  have hk : (0 : ℤ) < 2 := by norm_num
  set g := CuspForm.twist (chiDMod D) (L := N * D.natAbs * D.natAbs) (dvd_mul_right _ _)
    ⟨N, by ring⟩ f.toCuspForm with hg
  have hcoef : ∀ n : ℕ, (qExpansion 1 g).coeff n = twistCoeff f D n := by
    intro n
    rw [hg, CuspForm.qExpansion_twist_coeff, chiDMod_natCast]
    simp only [twistCoeff, coeff]
    ring
  have hGg : IsEntireCont (twistCoeff f D) 2 (ModularForm.L hk g) := by
    refine ⟨CuspForm.differentiable_L hk g, fun s hs => ?_⟩
    have h := CuspForm.LSeries_qExpansion_coeff_eq hk g (s := s) (by norm_num; linarith)
    simp only [strictWidthInfty_Gamma1, Complex.ofReal_one, Complex.one_cpow, one_mul] at h
    rw [← h]
    exact LSeries_congr (fun {n} _ => hcoef n) s
  rw [hG.eq hGg]
  apply CuspForm.L_ne_zero_of_qExpansion_coeff_ne_zero g hk one_ne_zero
  simp only [strictWidthInfty_Gamma1, Complex.ofReal_one]
  rw [hcoef 1, twistCoeff, coeff, f.isNorm, chiD]
  simp

theorem completedL_eq (q : ℕ) (G : ℂ → ℂ) (s : ℂ) :
    ZInQ.Literature.completedL q G s =
      (q : ℂ) ^ (s / 2) * ((2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * G s) := by
  rw [ZInQ.Literature.completedL]; ring

/-- **Uniqueness of the sign.** If `Λ_q(2 − s) = Λ_q(s)` and `Λ_Q(2 − s) = w Λ_Q(s)` on the strip
for one function `G` not vanishing identically there, then `w = 1`. -/
theorem sign_eq_one_of_functionalEquations {G : ℂ → ℂ} (hGd : Differentiable ℂ G)
    {q Q : ℕ} (hq : 0 < q) (hQ : 0 < Q) {w : ℂ}
    (hne : ∃ s : ℂ, 0 < s.re ∧ s.re < 2 ∧ G s ≠ 0)
    (h1 : ∀ s : ℂ, 0 < s.re → s.re < 2 →
      ZInQ.Literature.completedL q G (2 - s) = ZInQ.Literature.completedL q G s)
    (h2 : ∀ s : ℂ, 0 < s.re → s.re < 2 →
      ZInQ.Literature.completedL Q G (2 - s) = w * ZInQ.Literature.completedL Q G s) :
    w = 1 := by
  set E : ℂ → ℂ := fun s => (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * G s with hE
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  set H : ℂ → ℂ := fun s => (Q : ℂ) ^ ((2 - s) / 2) * (q : ℂ) ^ (s / 2) -
    w * (q : ℂ) ^ ((2 - s) / 2) * (Q : ℂ) ^ (s / 2) with hH
  have hHE : ∀ s : ℂ, 0 < s.re → s.re < 2 → H s * E s = 0 := by
    intro s hs1 hs2
    have e1 := h1 s hs1 hs2
    have e2 := h2 s hs1 hs2
    rw [completedL_eq, completedL_eq] at e1 e2
    simp only [hH, hE]
    linear_combination (q : ℂ) ^ ((2 - s) / 2) * e2 - (Q : ℂ) ^ ((2 - s) / 2) * e1
  obtain ⟨s₀, hs1, hs2, hs₀⟩ := hne
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hEs₀ : E s₀ ≠ 0 := by
    simp only [hE]
    refine mul_ne_zero (mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos hs1)) hs₀
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => h2π h.1
  have hEc : ContinuousAt E s₀ := by
    have hΓ : DifferentiableAt ℂ Complex.Gamma s₀ := by
      apply Complex.differentiableAt_Gamma
      intro m hm
      rw [hm] at hs1
      simp at hs1
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hc : DifferentiableAt ℂ (fun s : ℂ => (2 * Real.pi : ℂ) ^ (-s)) s₀ :=
      (differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow (Or.inl h2π)
    exact ((hc.mul hΓ).mul (hGd s₀)).continuousAt
  have hev : H =ᶠ[nhds s₀] 0 := by
    filter_upwards [hEc.eventually_ne hEs₀, isOpen_strip.mem_nhds ⟨hs1, hs2⟩] with s hs hs'
    have := hHE s hs'.1 hs'.2
    exact (mul_eq_zero.mp this).resolve_right hs
  have hHd : Differentiable ℂ H := by
    intro s
    have hd1 : DifferentiableAt ℂ (fun s : ℂ => (2 - s) / 2) s :=
      ((differentiableAt_const _).sub differentiableAt_id).div_const _
    have hd2 : DifferentiableAt ℂ (fun s : ℂ => s / 2) s := differentiableAt_id.div_const _
    simp only [hH]
    exact ((hd1.const_cpow (Or.inl hQ0)).mul (hd2.const_cpow (Or.inl hq0))).sub
      (((differentiableAt_const _).mul (hd1.const_cpow (Or.inl hq0))).mul
        (hd2.const_cpow (Or.inl hQ0)))
  have hHa := Complex.analyticOnNhd_univ_iff_differentiable.mpr hHd
  have hH1 : H 1 = 0 :=
    hHa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ s₀) hev
      (Set.mem_univ 1)
  simp only [hH] at hH1
  have e : ((2 : ℂ) - 1) / 2 = 1 / 2 := by norm_num
  rw [e] at hH1
  have hqh : (q : ℂ) ^ ((1 : ℂ) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hq0 h.1
  have hQh : (Q : ℂ) ^ ((1 : ℂ) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hQ0 h.1
  have : ((Q : ℂ) ^ ((1 : ℂ) / 2) * (q : ℂ) ^ ((1 : ℂ) / 2)) * (1 - w) = 0 := by
    linear_combination hH1
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (mul_ne_zero hQh hqh)
  · linear_combination -h

/-- **The root-number clause, in closed form.** For `D₀` an odd fundamental discriminant prime to
`N`, `RootNumberTwistEqOne f D₀` holds exactly when `χ_{D₀}(−N) ε(f) = 1`, which is
`ε(½, π_f ⊗ χ_{D₀}) = 1` by the twisted root-number formula (Atkin–Li 1978; Iwaniec–Kowalski
Prop. 14.20). Uses the proved twisted functional equation (`twistFunctionalEquation`, gz-fh). -/
theorem rootNumberTwistEqOne_iff {N : ℕ} [NeZero N] (f : Newform N 2) (hχ : f.χ = 1) {D₀ : ℤ}
    (hD₀ : IsOddFundDisc D₀) (hcop : Nat.Coprime D₀.natAbs N) :
    RootNumberTwistEqOne f D₀ ↔ (jacobiSym (-(N : ℤ)) D₀.natAbs : ℂ) * rootNumber f hχ = 1 := by
  have hD₀0 : D₀ ≠ 0 := by have := hD₀.2.1; omega
  have hQ : 0 < N * D₀.natAbs ^ 2 := by
    have := NeZero.pos N; have := Int.natAbs_pos.mpr hD₀0; positivity
  constructor
  · rintro ⟨q, hq, G, hG, hFE⟩
    have hG' : IsEntireCont (twistCoeff f D₀) 2 G :=
      isEntireCont_congr (fun n hn => printedTwistCoeff_eq f hD₀ hn) hG
    exact sign_eq_one_of_functionalEquations hG'.1 hq hQ
      (exists_ne_zero_on_strip hG'.1 (twist_cont_ne_zero f hD₀0 hG')) hFE
      (twistFunctionalEquation N f hχ D₀ hD₀ hcop G hG')
  · intro h
    obtain ⟨G, hG⟩ := exists_isEntireCont_twist f hD₀0
    refine ⟨N * D₀.natAbs ^ 2, hQ, G,
      isEntireCont_congr (fun n hn => (printedTwistCoeff_eq f hD₀ hn).symm) hG,
      fun s hs1 hs2 => ?_⟩
    rw [twistFunctionalEquation N f hχ D₀ hD₀ hcop G hG s hs1 hs2, h, one_mul]

/-! ## The converse: the functional-equation form gives the printed form -/

theorem localChar_eq_of_isSquare_div {K : Type*} [Field K] {d D : ℤ} (hd : (d : K) ≠ 0)
    (hD : (D : K) ≠ 0) (h : IsSquare ((d : K) / D)) : localChar K d = localChar K D := by
  funext x
  have hiff := isLocalNorm_iff_of_isSquare_div hd hD h (x : K)
  simp only [localChar]
  by_cases h1 : IsLocalNorm K d (x : K)
  · simp [h1, hiff.mp h1]
  · simp [h1, mt hiff.mpr h1]

theorem infinite_of_forall_exists_natAbs_gt {s : Set ℤ} (h : ∀ B : ℕ, ∃ d ∈ s, B < d.natAbs) :
    s.Infinite := by
  intro hs
  obtain ⟨M, hM⟩ := (hs.image Int.natAbs).bddAbove
  obtain ⟨d, hd, hdM⟩ := h M
  exact absurd (hM ⟨d, hd, rfl⟩) (not_le.mpr hdM)

theorem coprime_of_not_dvd {N : ℕ} {S : Finset ℕ} (hS : ∀ p : ℕ, p.Prime → p ∣ 2 * N → p ∈ S)
    {D₀ : ℤ} (hSD₀ : ∀ p ∈ S, ¬ (p : ℤ) ∣ D₀) : Nat.Coprime D₀.natAbs N := by
  refine Nat.coprime_of_dvd fun p hp hpD hpN => ?_
  exact hSD₀ p (hS p hp (dvd_mul_of_dvd_right hpN 2)) (Int.natCast_dvd.mpr hpD)

/-- **The printed form and the functional-equation form of Friedberg–Hoffstein are
equivalent** (all three dictionary clauses proved). -/
theorem friedbergHoffsteinB_printed_of_FE (h : FriedbergHoffsteinB_FE) :
    FriedbergHoffsteinB_Printed := by
  intro N _ f hχ S hS D₀ hD₀ hSD₀ hroot
  have hD₀0 : D₀ ≠ 0 := by have := hD₀.2.1; omega
  have hcop := coprime_of_not_dvd hS hSD₀
  have hw := (rootNumberTwistEqOne_iff f hχ hD₀ hcop).mp hroot
  obtain ⟨G, hG⟩ := exists_isEntireCont_twist f hD₀0
  have hFE : ∀ s : ℂ, 0 < s.re → s.re < 2 →
      ZInQ.Literature.completedL (N * D₀.natAbs ^ 2) G (2 - s) =
        ZInQ.Literature.completedL (N * D₀.natAbs ^ 2) G s := by
    intro s hs1 hs2
    rw [twistFunctionalEquation N f hχ D₀ hD₀ hcop G hG s hs1 hs2, hw, one_mul]
  have hall := h N f hχ S hS D₀ hD₀ hSD₀ ⟨G, hG, hFE⟩
  apply infinite_of_forall_exists_natAbs_gt
  intro B
  obtain ⟨D, hDB, hDf, hsign, hloc, hL⟩ := hall B
  have hD0 : D ≠ 0 := by have := hDf.2.1; omega
  refine ⟨D, ⟨hDf.2.2, hDf.1, fun p _ hpS => ?_, ?_, fun G' hG' => ?_⟩, hDB⟩
  · have hpD₀ := hSD₀ p hpS
    exact localChar_eq_of_isSquare_div (by exact_mod_cast hD0)
      (padic_intCast_ne_zero_of_not_dvd hpD₀) (hloc p hpS)
  · exact localChar_eq_of_isSquare_div (by exact_mod_cast hD0) (by exact_mod_cast hD₀0)
      (real_isSquare_div_of_pos_mul hsign)
  · exact hL G' (isEntireCont_congr (fun n hn => printedTwistCoeff_eq f hDf hn) hG')

theorem friedbergHoffsteinB_printed_iff_FE :
    FriedbergHoffsteinB_Printed ↔ FriedbergHoffsteinB_FE :=
  ⟨friedbergHoffsteinB_FE_of_printed, friedbergHoffsteinB_printed_of_FE⟩

end ZInQ.FHPrinted

#print axioms ZInQ.FHPrinted.friedbergHoffsteinB_FE_of_printed
#print axioms ZInQ.FHPrinted.friedbergHoffsteinB_printed_iff_FE
#print axioms ZInQ.FHPrinted.rootNumberTwistEqOne_iff
