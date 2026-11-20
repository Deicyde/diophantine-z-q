import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Statement
import ZInQKernel.Contrib.RC53Assist.NewformGlueG0.HeckeBridge
import TauCeti.NumberTheory.ModularForms.LFunction.Basic

/-!
# From the printed Theorem A to modularity over `Γ₀(N)`

The step that turns the printed condition (2) into the tree's `PoleS12.IsModular` is proved
here, with no input; the print is the only hypothesis of `bcdtThmA_of_printed`.

* `coeff_eq_of_eq_cuspLSeries`: equality of `L(E, s)` and `L(f, s)` on a right half-plane, for
  a nonzero cusp form `f`, gives `c_n(f) = a_n(E)` for every `n ≥ 1`. Hecke's bound
  (Mathlib, `CuspFormClass.qExpansion_isBigO`) makes `L(f, s)` converge somewhere; uniqueness of
  Dirichlet coefficients is Mathlib's `LSeries.eq_of_LSeries_eventually_eq`.
* `diamondOpCuspNat_eq_self_of_good`: at a prime `p` of good reduction, a `T_p`-eigenvector
  with the coefficients of `E` is fixed by the diamond operator `⟨p⟩`. This compares the Hecke
  coefficient formula `a_m(T_p f) = a_{pm}(f) + p a_{m/p}(⟨p⟩ f)` (Diamond–Shurman, Prop. 5.3.1,
  proved in the vendored library for every cusp form on `Γ₁(N)`) with the good-prime recurrence
  `a_{pm}(E) = a_p(E) a_m(E) − p a_{m/p}(E)` of the Euler product. For a form with nebentypus
  `χ` the case `m = p` reads `a_{p²} = a_p² − χ(p) p`, against `a_{p²} = a_p² − p` for `E`; no
  nebentypus is assumed here.
* `diamondOpCusp_eq_self_of_eigen`: by Dirichlet's theorem on primes in arithmetic progressions
  (Mathlib, `Nat.forall_exists_prime_gt_and_eq_mod`), every unit modulo `N` is the class of a
  prime of good reduction not dividing `N`, so every diamond operator fixes the form: its
  nebentypus is trivial.
* `isModular_of_condition2At`, `bcdtThmA_of_printed`: the form is invariant under `Γ₀(N)`, so it
  is a cusp form on `Γ₀(N)` with the same `q`-expansion; this is `PoleS12.BCDTThmA`.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.BCDTPrint

open Filter CongruenceSubgroup UpperHalfPlane Matrix.SpecialLinearGroup HeckeRing.GL2
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary ZInQ.Contrib.RC53Assist.NewformGlueG0

variable {N : ℕ} [NeZero N]

/-! ### The L-function equality as an equality of coefficients -/

/-- **PROVED**, from Hecke's bound for cusp forms (Mathlib, `CuspFormClass.qExpansion_isBigO`;
vendored `CuspForm.abscissaOfAbsConv_qExpansion_coeff_le`) and the width one of `Γ₁(N)` at `∞`:
the Dirichlet series of the coefficients of a cusp form on `Γ₁(N)` converges somewhere. -/
theorem abscissaOfAbsConv_cuspCoeff_lt_top {k : ℤ} (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    LSeries.abscissaOfAbsConv (fun n ↦ (qExpansion 1 f).coeff n) < ⊤ := by
  have h := CuspForm.abscissaOfAbsConv_qExpansion_coeff_le f
  rw [strictWidthInfty_Gamma1] at h
  exact h.trans_lt (EReal.add_lt_top (EReal.coe_ne_top _) (EReal.coe_ne_top 1))

omit [NeZero N] in
/-- **PROVED**, by `CuspForm.qExpansion_injective` (vendored) and the vanishing of the zeroth
coefficient: a nonzero cusp form on `Γ₁(N)` has a nonzero coefficient at a positive index. -/
theorem exists_cuspCoeff_ne_zero {k : ℤ} {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ≠ 0) : ∃ n : ℕ, n ≠ 0 ∧ (qExpansion 1 f).coeff n ≠ 0 := by
  by_contra! h
  apply hf
  apply CuspForm.qExpansion_injective one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N)
  ext n
  simp only [FunLike.coe_zero, qExpansion_zero, map_zero]
  rcases eq_or_ne n 0 with rfl | hn
  · exact CuspFormClass.qExpansion_coeff_zero f one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map N)
  · exact h n hn

/-- **PROVED**, by uniqueness of Dirichlet coefficients (Mathlib,
`LSeries.eq_of_LSeries_eventually_eq`). If `L(E, s) = L(f, s)` on a right half-plane for a
nonzero cusp form `f` on `Γ₁(N)`, then `c_n(f) = a_n(E)` for every `n ≥ 1`. The Dirichlet series
of `f` converges somewhere (`abscissaOfAbsConv_cuspCoeff_lt_top`) and is not eventually zero on
the real axis, so neither is `L(E, s)`, which therefore converges somewhere as well; no growth
bound for the coefficients of `E` is assumed. -/
theorem coeff_eq_of_eq_cuspLSeries (E : WeierstrassCurve ℚ) {k : ℤ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ≠ 0) {σ : ℝ}
    (hL : ∀ s : ℂ, σ < s.re → E.LSeries s = cuspLSeries f s) :
    ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ) := by
  set a : ℕ → ℂ := fun n ↦ (qExpansion 1 f).coeff n
  set b : ℕ → ℂ := fun n ↦ (E.LFunction n : ℂ)
  have hab : ∀ x : ℝ, σ < x → LSeries b x = LSeries a x := fun x hx ↦
    hL x (by simpa using hx)
  have ha : LSeries.abscissaOfAbsConv a < ⊤ := abscissaOfAbsConv_cuspCoeff_lt_top f
  have hb : LSeries.abscissaOfAbsConv b < ⊤ := by
    by_contra hbt
    rw [not_lt, top_le_iff] at hbt
    have hb0 := LSeries_eq_zero_of_abscissaOfAbsConv_eq_top hbt
    have hev : (fun x : ℝ ↦ LSeries a x) =ᶠ[atTop] 0 := by
      filter_upwards [eventually_gt_atTop σ] with x hx
      rw [← hab x hx, hb0]
      rfl
    rcases LSeries_eventually_eq_zero_iff'.mp hev with h0 | htop
    · obtain ⟨n, hn, hne⟩ := exists_cuspCoeff_ne_zero hf
      exact hne (h0 n hn)
    · exact ha.ne htop
  intro n hn
  refine LSeries.eq_of_LSeries_eventually_eq ha hb ?_ hn.ne'
  filter_upwards [eventually_gt_atTop σ] with x hx
  exact (hab x hx).symm

/-! ### Trivial nebentypus -/

/-- **PROVED**, the coefficient comparison at one prime. Locators: Diamond–Shurman,
Prop. 5.3.1 (vendored `qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime`:
`a_m(T_p f) = a_{pm}(f) + p^{k−1} a_{m/p}(⟨p⟩ f)` for every cusp form on `Γ₁(N)`, with no
nebentypus) and the good-prime recurrence of the Euler product
(`NewformGlueG0.lFunction_good_prime_mul`). If `f` has the coefficients of `E`, `T_p f = c f`,
and `E` has good reduction at `p`, then the diamond operator `⟨p⟩` fixes `f`. No coprimality
is assumed: for `p ∣ N` the operator `⟨p⟩` is zero, and the statement then shows that the
hypotheses are inconsistent. -/
theorem diamondOpCuspNat_eq_self_of_good (E : WeierstrassCurve ℚ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {p : ℕ} (hp : p.Prime) (hgood : GoodReductionAt E (primeIdealQ p hp)) {c : ℂ}
    (hc : heckeTCuspNat 2 p (_hn := ⟨hp.ne_zero⟩) f = c • f) :
    diamondOpCuspNat 2 p f = f := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hΓ := TauCeti.one_mem_strictPeriods_Gamma1_map N
  have hall : ∀ n : ℕ, (qExpansion 1 f).coeff n = (E.LFunction n : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [CuspFormClass.qExpansion_coeff_zero f one_pos hΓ]
      simp
    · exact hf n hn
  have h1 : (qExpansion 1 f).coeff 1 = 1 := by
    rw [hall 1, lFunction_one]
    simp
  rw [heckeTCuspNat_def] at hc
  have hcp : c = (qExpansion 1 f).coeff p :=
    eq_qExpansion_coeff_of_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_eq_smul 2 hp hc h1
  refine CuspForm.qExpansion_injective one_pos hΓ (PowerSeries.ext fun n ↦ ?_)
  have h := qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime 2 hp f (p * n)
  rw [hc, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos hΓ, map_smul, smul_eq_mul,
    ite_eq_left (dvd_mul_right p n), Nat.mul_div_cancel_left n hp.pos] at h
  have hE := lFunction_good_prime_mul E p hp hgood (p * n)
  rw [ite_eq_left (dvd_mul_right p n), Nat.mul_div_cancel_left n hp.pos] at hE
  have hE' : ((E.LFunction (p * (p * n)) : ℤ) : ℂ) =
      (E.LFunction p : ℂ) * (E.LFunction (p * n) : ℂ) - (p : ℂ) * (E.LFunction n : ℂ) := by
    exact_mod_cast hE
  rw [hcp, hall p, hall (p * n), hall (p * (p * n)), hE',
    show (2 : ℤ) - 1 = 1 by norm_num, zpow_one] at h
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hn : (p : ℂ) * (qExpansion 1 (diamondOpCuspNat 2 p f)).coeff n =
      (p : ℂ) * (qExpansion 1 f).coeff n := by
    rw [hall n]
    linear_combination -h
  exact mul_left_cancel₀ hp0 hn

/-- **PROVED**, by Dirichlet's theorem on primes in arithmetic progressions (Mathlib,
`Nat.forall_exists_prime_gt_and_eq_mod`) and good reduction outside a finite set
(`NewformPeriodsDictionary.goodReductionAt_almost_all_primes`). A cusp form on `Γ₁(N)` with the
coefficients of an elliptic curve `E` which is a `T_p`-eigenvector at every prime `p ∤ N` is
fixed by every diamond operator. -/
theorem diamondOpCusp_eq_self_of_eigen (E : WeierstrassCurve ℚ) (hE : E.IsElliptic)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (heig : ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ N →
      ∃ c : ℂ, heckeTCuspNat 2 p (_hn := ⟨hp.ne_zero⟩) f = c • f)
    (d : (ZMod N)ˣ) : diamondOpCusp 2 d f = f := by
  obtain ⟨S, hS⟩ := goodReductionAt_almost_all_primes E hE
  obtain ⟨p, hpgt, hp, hpd⟩ := Nat.forall_exists_prime_gt_and_eq_mod d.isUnit (S.sup id + N)
  have hpS : p ∉ S := fun h ↦ by
    have hle : id p ≤ S.sup id := Finset.le_sup h
    simp only [id] at hle
    omega
  have hpN : ¬p ∣ N := fun h ↦ by
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) h
    omega
  have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  obtain ⟨c, hc⟩ := heig p hp hpN
  have h := diamondOpCuspNat_eq_self_of_good E f hf hp (hS p hp hpS) hc
  rw [diamondOpCuspNat_of_coprime 2 hcop] at h
  have hu : ZMod.unitOfCoprime p hcop = d := Units.ext (by rw [ZMod.coe_unitOfCoprime, hpd])
  rwa [hu] at h

/-- **PROVED**, from `diamondOpCusp_eq_self_of_eigen`: such a form has trivial nebentypus, i.e.
lies in the vendored character space `S_2(Γ₁(N), 1)`. -/
theorem mem_cuspFormCharSpace_one_of_eigen (E : WeierstrassCurve ℚ) (hE : E.IsElliptic)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (heig : ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ N →
      ∃ c : ℂ, heckeTCuspNat 2 p (_hn := ⟨hp.ne_zero⟩) f = c • f) :
    f ∈ cuspFormCharSpace 2 (1 : (ZMod N)ˣ →* ℂˣ) := by
  rw [mem_cuspFormCharSpace_iff]
  intro d
  rw [diamondOpCuspHom_apply, diamondOpCusp_eq_self_of_eigen E hE f hf heig d,
    MonoidHom.one_apply, Units.val_one, one_smul]

/-- **PROVED**, by the trivial-character identification `TauCeti.cuspFormCharSpaceOneEquiv`,
which keeps the underlying function: condition (2) at a level `N` gives the tree's
`PoleS12.IsModular`, at the same level. -/
theorem isModular_of_condition2At {E : WeierstrassCurve ℚ} (hE : E.IsElliptic)
    (h : Condition2At E N) : ZInQ.Manuscript.PoleS12.IsModular E := by
  obtain ⟨f, ⟨hf0, heig⟩, σ, hL⟩ := h
  have hf := coeff_eq_of_eq_cuspLSeries E hf0 hL
  have hmem := mem_cuspFormCharSpace_one_of_eigen E hE f hf heig
  set g := TauCeti.cuspFormCharSpaceOneEquiv N 2 ⟨f, hmem⟩
  have hg : ⇑g = ⇑f := TauCeti.coe_cuspFormCharSpaceOneEquiv_apply _
  refine ⟨N, Nat.pos_of_ne_zero (NeZero.ne N), g, fun n hn ↦ ?_⟩
  rw [show qExpansion 1 g = qExpansion 1 f from congrArg (qExpansion 1) hg]
  exact hf n hn

/-- **PROVED**, Breuil–Conrad–Diamond–Taylor's Theorem A as printed (with condition (2)) implies
the tree's `PoleS12.BCDTThmA`: the eigenform of the print has trivial nebentypus, so it is a
cusp form on `Γ₀(N)` whose `q`-expansion coefficients are the Dirichlet coefficients of
Mathlib's `L(E, s)`. -/
theorem bcdtThmA_of_printed (hB : BCDTThmAPrinted) : ZInQ.Manuscript.PoleS12.BCDTThmA := by
  intro E hE
  obtain ⟨N, _, h⟩ := hB E hE
  exact isModular_of_condition2At hE h

/-- **PROVED**, `bcdtThmAPrinted_of_atLevel` and `bcdtThmA_of_printed`: Theorem A with condition
(2) at any prescribed positive level function — for the conductor, the printed statement word
for word — gives `PoleS12.BCDTThmA`. -/
theorem bcdtThmA_of_printedAtLevel {level : WeierstrassCurve ℚ → ℕ+}
    (hB : BCDTThmAPrintedAtLevel level) : ZInQ.Manuscript.PoleS12.BCDTThmA :=
  bcdtThmA_of_printed (bcdtThmAPrinted_of_atLevel hB)

end ZInQ.Contrib.RC53Assist.BCDTPrint
