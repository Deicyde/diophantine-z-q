import ZInQKernel.Contrib.OneProof.FHNonvanishing.Basic

/-!
# gz-fh, variant: Friedberg–Hoffstein with the root number read off the functional equation

The root number `ε(½, π ⊗ χ₀)` is by definition the sign of the functional equation of the
completed L-function of `π ⊗ χ₀`. This file states Friedberg–Hoffstein in that form
(`FriedbergHoffsteinB_FE`), states the twisted functional equation `TwistFunctionalEquation`
(GLUE: the conjugation of the Fricke involution through the twist by Gauss sums, no newform
theory; proved in `FHNonvanishing/TwistFE.lean` as `twistFunctionalEquation`), and proves:

* `fhNonvanishing_of_printed_fe : FriedbergHoffsteinB_FE → TwistFunctionalEquation → FHNonvanishing`;
* `twistFunctionalEquation_of_twistNewformRootNumber`: the printed leaf `TwistNewformRootNumber`
  implies `TwistFunctionalEquation` (via Tau Ceti's proved functional equation of a newform);
* `friedbergHoffsteinB_of_fe`: `FriedbergHoffsteinB_FE` implies `FriedbergHoffsteinB` (so the FE
  form is the stronger-looking of the two Friedberg–Hoffstein statements; both are
  specializations of the printed theorem).

So `FHNonvanishing` rests either on {`FriedbergHoffsteinB`, `TwistNewformRootNumber`} (two printed
leaves, `fhNonvanishing_of_printed`) or on {`FriedbergHoffsteinB_FE` (printed leaf),
`TwistFunctionalEquation` (glue, proved)}, i.e. on `FriedbergHoffsteinB_FE` alone
(`fhNonvanishing_of_friedbergHoffsteinB_FE` in `FHNonvanishing.lean`).
-/

open HeckeRing.GL2 CongruenceSubgroup

namespace ZInQ.GZFH

open ZInQ.GZDecomp

/-! ## Statements -/

/-- **Friedberg–Hoffstein, Theorem B, with `ε(½, π ⊗ χ₀) = 1` written as the functional equation of
`Λ(f ⊗ χ_{D₀}, s)` with sign `+1`.** As `FriedbergHoffsteinB`, except that the compatibility
hypothesis reads: the entire continuation `G` of `L(f ⊗ χ_{D₀}, s) = ∑ aₙ(f) χ_{D₀}(n) n^{−s}`
satisfies `Λ(2 − s) = Λ(s)` on `0 < Re s < 2`, where
`Λ(s) = (N D₀²)^{s/2} (2π)^{−s} Γ(s) G(s)` (`ZInQ.Literature.completedL`). For `(D₀, N) = 1`
(forced by `p ∤ D₀` for `p ∈ S ⊇ {p ∣ N}`) the conductor of `π_f ⊗ χ₀` is `N D₀²`, its completed
L-function satisfies `Λ(2 − s) = ε(½, π ⊗ χ₀) Λ(s)`, and `Λ ≢ 0` on the strip (since `G ≢ 0`, as
`a₁ = 1`), so the hypothesis says exactly `ε(½, π ⊗ χ₀) = 1`. The strip avoids the junk values of
Mathlib's `Complex.Gamma` at the poles (as in `ZInQ.Literature.FunctionalEquation5`).

Source: Friedberg–Hoffstein, Ann. of Math. (2) 142 (1995) 385–423, Theorem B (UNVERIFIED; see
`FriedbergHoffsteinB` for the dictionary and the open checks). -/
def FriedbergHoffsteinB_FE : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
  ∀ S : Finset ℕ, (∀ p : ℕ, p.Prime → p ∣ 2 * N → p ∈ S) →
  ∀ D₀ : ℤ, IsOddFundDisc D₀ → (∀ p ∈ S, ¬ (p : ℤ) ∣ D₀) →
    (∃ G : ℂ → ℂ, IsEntireCont (twistCoeff f D₀) 2 G ∧
      ∀ s : ℂ, 0 < s.re → s.re < 2 →
        ZInQ.Literature.completedL (N * D₀.natAbs ^ 2) G (2 - s) =
          ZInQ.Literature.completedL (N * D₀.natAbs ^ 2) G s) →
    ∀ B : ℕ, ∃ D : ℤ, B < D.natAbs ∧ IsOddFundDisc D ∧ 0 < D * D₀ ∧
      (∀ (p : ℕ) [Fact p.Prime], p ∈ S → IsSquare ((D : ℚ_[p]) / (D₀ : ℚ_[p]))) ∧
      ∀ G : ℂ → ℂ, IsEntireCont (twistCoeff f D) 2 G → G 1 ≠ 0

/-- **The functional equation of a quadratic twist** (GLUE target). For `f` a newform of weight
2, level `N`, trivial nebentypus, and `D` an odd fundamental discriminant `≠ 1` prime to `N`, the
entire continuation `G` of `L(f ⊗ χ_D, s)` satisfies
`Λ(2 − s) = χ_D(−N) ε(f) Λ(s)` on `0 < Re s < 2`, with `Λ(s) = (N D²)^{s/2} (2π)^{−s} Γ(s) G(s)`.

Textbook (Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971),
Prop. 3.64; Iwaniec, *Topics in classical automorphic forms* (1997), Thm 7.5;
Iwaniec–Kowalski Prop. 14.20; all UNVERIFIED numbers). GLUE, proved:
`twistFunctionalEquation` (`FHNonvanishing/TwistFE.lean`), from Tau Ceti's `CuspForm.twist` and
the Fricke-eigenvector functional equation
`CuspForm.frickeCompletedL_sub_eq_of_normalizedFrickeOperatorCusp_eq_smul`, by conjugating
`W_{N D²}` through the twist (Gauss sums), without newform theory. It also follows from
`TwistNewformRootNumber` (`twistFunctionalEquation_of_twistNewformRootNumber`). -/
def TwistFunctionalEquation : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2) (hχ : f.χ = 1),
  ∀ D : ℤ, IsOddFundDisc D → Nat.Coprime D.natAbs N →
    ∀ G : ℂ → ℂ, IsEntireCont (twistCoeff f D) 2 G →
      ∀ s : ℂ, 0 < s.re → s.re < 2 →
        ZInQ.Literature.completedL (N * D.natAbs ^ 2) G (2 - s) =
          (jacobiSym (-(N : ℤ)) D.natAbs : ℂ) * rootNumber f hχ *
            ZInQ.Literature.completedL (N * D.natAbs ^ 2) G s

/-! ## The completed L-function of a newform -/

/-- For a newform `g` of weight 2 and level `M`, and the entire continuation `G` of `L(g, s)`,
`completedL M G s` is Tau Ceti's `frickeCompletedL g M s` for `Re s > 0`. -/
theorem completedL_eq_frickeCompletedL {M : ℕ} [NeZero M] (g : Newform M 2) {G : ℂ → ℂ}
    (hG : IsEntireCont (coeff g) 2 G) {s : ℂ} (hs : 0 < s.re) :
    ZInQ.Literature.completedL M G s =
      CuspForm.frickeCompletedL g.toCuspForm (M.toPNat (NeZero.pos M)) s := by
  have hk : (0 : ℤ) < 2 := by norm_num
  have hEq : G = ModularForm.L hk g.toCuspForm := by
    have := CuspForm.eq_strictWidthInfty_cpow_mul_L g.toCuspForm hk hG.1 (fun {s} hs => by
      simp only [strictWidthInfty_Gamma1]
      exact hG.2 s (by norm_num at hs; linarith))
    simpa [strictWidthInfty_Gamma1] using this
  rw [hEq, ZInQ.Literature.completedL,
    CuspForm.frickeCompletedL_eq_cpow_mul_Λ g.toCuspForm _ hk s, ModularForm.L]
  have hMc : (((M.toPNat (NeZero.pos M) : ℕ+) : ℕ) : ℂ) = (M : ℂ) := rfl
  rw [hMc, Complex.Gammaℂ_def]
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hπ : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => by exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero) (by exact_mod_cast h.1)
  field_simp

/-- Tau Ceti's functional equation of a newform of trivial nebentypus, for the entire
continuation of its L-series and `ZInQ.Literature.completedL`, on the strip. -/
theorem completedL_newform_sub {M : ℕ} [NeZero M] (g : Newform M 2) (hg : g.χ = 1) {G : ℂ → ℂ}
    (hG : IsEntireCont (coeff g) 2 G) {s : ℂ} (hs1 : 0 < s.re) (hs2 : s.re < 2) :
    ZInQ.Literature.completedL M G (2 - s) = rootNumber g hg * ZInQ.Literature.completedL M G s := by
  have hk : (0 : ℤ) < 2 := by norm_num
  have h2s : 0 < (2 - s).re := by simp only [Complex.sub_re]; norm_num; linarith
  rw [completedL_eq_frickeCompletedL g hG h2s, completedL_eq_frickeCompletedL g hG hs1]
  have e := Newform.frickeCompletedL_sub_eq g hg hk s
  have e2 : ((2 : ℤ) : ℂ) = 2 := by norm_num
  rw [e2] at e
  rw [e]
  rfl

theorem isEntireCont_congr {a b : ℕ → ℂ} (hab : ∀ n : ℕ, n ≠ 0 → a n = b n) {σ : ℝ} {G : ℂ → ℂ}
    (hG : IsEntireCont a σ G) : IsEntireCont b σ G :=
  ⟨hG.1, fun s hs => (hG.2 s hs).trans (LSeries_congr (fun {n} hn => hab n hn) s)⟩

/-! ## Relations between the statements -/

/-- **The printed twisted root number gives the twisted functional equation.** -/
theorem twistFunctionalEquation_of_twistNewformRootNumber (h : TwistNewformRootNumber) :
    TwistFunctionalEquation := by
  intro N _ f hχ D hD hcop G hG s hs1 hs2
  obtain ⟨M, _, g, hg, hM, hcoef, hroot⟩ := h N f hχ D hD hcop
  subst hM
  have hGg : IsEntireCont (coeff g) 2 G := isEntireCont_congr (fun n hn => (hcoef n hn).symm) hG
  rw [completedL_newform_sub g hg hGg hs1 hs2, hroot]

/-- **The FE form of Friedberg–Hoffstein implies the newform form.** -/
theorem friedbergHoffsteinB_of_fe (h : FriedbergHoffsteinB_FE) : FriedbergHoffsteinB := by
  intro N _ f hχ S hS D₀ hD₀ hSD₀ ⟨M, _, g, hg, hM, hcoef, hroot⟩
  refine h N f hχ S hS D₀ hD₀ hSD₀ ?_
  have hD0 : D₀ ≠ 0 := by
    rintro rfl; exact absurd hD₀.2.1 (by decide)
  obtain ⟨G, hG⟩ := exists_isEntireCont_twist f hD0
  refine ⟨G, hG, fun s hs1 hs2 => ?_⟩
  subst hM
  have hGg : IsEntireCont (coeff g) 2 G := isEntireCont_congr (fun n hn => (hcoef n hn).symm) hG
  rw [completedL_newform_sub g hg hGg hs1 hs2, hroot, one_mul]

/-! ## The reduction, FE form -/

/-- **`FHNonvanishing` from the FE form of Friedberg–Hoffstein and the twisted functional
equation.** -/
theorem fhNonvanishing_of_printed_fe (hFH : FriedbergHoffsteinB_FE)
    (hTw : TwistFunctionalEquation) : FHNonvanishing := by
  intro N _ f hχ hw B
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain ⟨D₀, hD₀, hH₀, h8N⟩ := exists_aux_disc hN0
  have hD₀f : IsOddFundDisc D₀ := ⟨by have := hD₀.1; omega, hD₀.2.1, hD₀.2.2⟩
  have hJ := ZInQ.GZStatements.jacobiSym_neg_level hN0 hD₀ hH₀
  obtain ⟨G, hG⟩ := exists_isEntireCont_twist f (ne_of_lt hD₀.1)
  have hFE : ∀ s : ℂ, 0 < s.re → s.re < 2 →
      ZInQ.Literature.completedL (N * D₀.natAbs ^ 2) G (2 - s) =
        ZInQ.Literature.completedL (N * D₀.natAbs ^ 2) G s := by
    intro s hs1 hs2
    rw [hTw N f hχ D₀ hD₀f (ZInQ.GZStatements.coprime_of_heegnerHyp (ne_of_lt hD₀.1) hH₀) G hG
      s hs1 hs2, hJ, hw]
    push_cast; ring
  obtain ⟨D, hDB, hDf, hsign, hloc, hGD⟩ :=
    hFH N f hχ (2 * N).primeFactors (fun p hp hpd => mem_primeFactors_two_mul hN0 hp hpd) D₀
      hD₀f (not_dvd_of_mem_primeFactors h8N) ⟨G, hG, hFE⟩ B
  obtain ⟨hDisc, hH⟩ := heegner_of_local hN0 hD₀.1 h8N hDf hsign hloc
  exact ⟨D, by have := hDisc.1; omega, hDisc, hH, hGD⟩

end ZInQ.GZFH
