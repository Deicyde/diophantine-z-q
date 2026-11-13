import ZInQKernel.Contrib.GaussFE.Headline
import ZInQKernel.Contrib.HeckeAll.Provider

/-!
# gz-decomp, step (1): the scope of `Literature.GrossZagier`

`ZInQ.Literature.GrossZagier` (`Hypotheses/CR3Literature.lean`) is stated for every elliptic curve
over `ℚ`. Every Lean use (`git grep -n GrossZagier`) reaches it only through
`Literature.certifiedRankTYZClRk_of_literature`, which applies it to `C_d = shortCurve (−d²)` with
`d ≡ 5 (mod 8)` squarefree. This file states the two restricted forms and proves that the
headline chain goes through with the smallest one.

* `GrossZagierCd`: Gross–Zagier for `C_d`, `d ≡ 5 (mod 8)` squarefree (what is used);
* `GrossZagierCongruent`: Gross–Zagier for every `C_d`, `d ≥ 1` squarefree (the congruent-number
  family, closed under the quadratic twists that the decomposition uses: the twist of `C_d` by
  `ℚ(√D)` is `C_{|dD|}`).

Replacing the premise in the headline is the owner's decision; nothing is edited here.
-/

namespace ZInQ.GZDecomp

open ZInQ.Literature

/-- **Gross–Zagier for the curves `C_d`, `d ≡ 5 (mod 8)` squarefree** (positive-rank half): if the
entire continuation of `L(C_d, s)` has a simple zero at `s = 1`, then `C_d(ℚ)` has a point of
infinite order. The case of `Literature.GrossZagier` that the headline uses. -/
def GrossZagierCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F → analyticOrderAt F 1 = 1 →
      ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P

/-- **Gross–Zagier for the congruent-number curves `C_d`, `d ≥ 1` squarefree.** -/
def GrossZagierCongruent : Prop :=
  ∀ d : ℕ, Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F → analyticOrderAt F 1 = 1 →
      ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P

theorem shortCurve_cd_isElliptic {d : ℕ} (hd : d ≠ 0) :
    (shortCurve (-(d : ℚ) ^ 2)).IsElliptic := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  exact shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero 2 hd0))

/-- The premise as stated implies the family form. -/
theorem grossZagierCongruent_of_grossZagier (h : GrossZagier) : GrossZagierCongruent :=
  fun _ hsq F hF h1 => h _ (shortCurve_cd_isElliptic hsq.ne_zero) F hF h1

/-- The family form implies the form that is used. -/
theorem grossZagierCd_of_grossZagierCongruent (h : GrossZagierCongruent) : GrossZagierCd :=
  fun d _ hsq F hF h1 => h d hsq F hF h1

theorem grossZagierCd_of_grossZagier (h : GrossZagier) : GrossZagierCd :=
  grossZagierCd_of_grossZagierCongruent (grossZagierCongruent_of_grossZagier h)

/-- **CR₃ from TYZ reading A and `GrossZagierCd`** (the two other CR₃ Props are proved:
`ZInQ.Contrib.heckeContinuation`, `ZInQ.Contrib.functionalEquation5`). -/
theorem certifiedRankTYZClRk_of_readingA_grossZagierCd (hA : TYZThm35ReadingA)
    (hG : GrossZagierCd) : RouteK.Rank.CertifiedRankTYZClRk := by
  intro d hd hsq h5b
  obtain ⟨F, hF, h1⟩ := analyticOrder_eq_one (tyzRow5b_of_readingA hA ZInQ.Contrib.heckeContinuation)
    (rootNumberVanishing_of_functionalEquation ZInQ.Contrib.functionalEquation5) hd hsq h5b
  exact hG d hd hsq F hF h1

/-- **CR₃ from the TYZ inputs I1–I7 and `GrossZagierCd`.** -/
theorem certifiedRankTYZClRk_of_tyzInputs_grossZagierCd (hT : PropN.TYZInputs)
    (hG : GrossZagierCd) : RouteK.Rank.CertifiedRankTYZClRk := by
  intro d hd hsq h5b
  obtain ⟨F, hF, h1⟩ := analyticOrder_eq_one (PropN.tyzRow5b_of_tyzInputs hT)
    (rootNumberVanishing_of_functionalEquation ZInQ.Contrib.functionalEquation5) hd hsq h5b
  exact hG d hd hsq F hF h1

/-- **Theorem 1.1 from `SixContactMin`, TYZ Theorem 3.5(2) in reading A and `GrossZagierCd`.** The
headline `…_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier` with the proved
premises discharged and `Literature.GrossZagier` replaced by its case `GrossZagierCd`. -/
theorem frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagierCd (hH : SixContactMin)
    (hA : TYZThm35ReadingA) (hG : GrossZagierCd) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk hH
    (certifiedRankTYZClRk_of_readingA_grossZagierCd hA hG)

/-- **Theorem 1.1 from `SixContactMin`, the TYZ inputs and `GrossZagierCd`.** -/
theorem frozenTarget_of_sixContactMin_tyzInputs_grossZagierCd (hH : SixContactMin)
    (hT : PropN.TYZInputs) (hG : GrossZagierCd) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk hH
    (certifiedRankTYZClRk_of_tyzInputs_grossZagierCd hT hG)

/-- The old headline's conclusion follows from the new one: the replacement is a weakening of the
premise (`grossZagierCd_of_grossZagier`). -/
theorem frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagier' (hH : SixContactMin)
    (hA : TYZThm35ReadingA) (hG : GrossZagier) : FrozenTarget :=
  frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagierCd hH hA (grossZagierCd_of_grossZagier hG)

end ZInQ.GZDecomp
