import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Kato
import ZInQKernel.Contrib.OneProof.RC.Even.EvenSource

/-!
# Theorem 5.3, Lane RC11-even: where Kato's printed theorems enter the even source

The 11/5 manuscript (`diophantine_zq.tex`), Section 7.1 (tex 1884–1893) and Appendix E,
Proposition `ex:app-kato-system` (tex 6846–7361). The printed results of Kato
(*`p`-adic Hodge theory and values of zeta functions of modular forms*, Astérisque 295 (2004),
117–290) are lane RC9's PRINT leaves:
* `KatoZetaLeaf` — Kato's zeta elements furnish a `KatoZetaInterface E Σ`: Prop. 8.12 (p. 186) with
  the Euler-system relation (13.1.1) of 13.1 and Example 13.3 (pp. 224–225), Thm. 13.4(1)(2)
  (p. 226), and the central-value anchor Thm. 6.6 (p. 163) with Thm. 9.7 (p. 189);
* `KatoThm13_5_2` — Rohrlich's finiteness of zero twisted central values (p. 227), which Elliot
  uses to verify hypothesis (i) of Thm. 13.4 for the twisted system (tex 7210–7221).

Elliot's own construction on these prints — the fixed symbol combination, the retained smoothing
(K5)–(K6), the integral `j_*` condition through ramified transfer (K7), the primitive twisted
Euler system (K8)–(K9), the coefficient map (K10) and the class `Z_F` (E.1)–(E.2), the central
normalization (K12)–(K14), the verification of Thm. 13.4's hypotheses (K15), the payment for the
full complex (K16), and the positive complex and calibration of Propositions `ex:app-even-scalar`
and `ex:app-central-calibration` — is the ELLIOT step `AppEFromKato`. This file only makes the
dependency explicit: `evenScalar32_of_kato` (PROVED) derives (3.2) from the PRINT leaf and the
ELLIOT step.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Even

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.PrintsArith

/-- **Elliot's Appendix E construction on Kato's Euler system** (ELLIOT; tex 6846–7787). From
Kato's zeta elements for `E` at `p = 2` (for every finite `S_bad ∋ 2` outside which the model is
good, a `KatoZetaInterface E Σ S_bad` with `Σ ⊇ S_bad`, as lane RC9's `KatoZetaLeaf` provides), Elliot constructs, with constants
fixed before the family, the outputs `AppEOutputs` of Propositions `ex:app-kato-system`,
`ex:app-even-scalar` and `ex:app-central-calibration` for every admissible binary family. -/
def AppEFromKato (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) (L : CentralNormalization E) :
    Prop :=
  (∀ Sbad : Finset ℕ, 2 ∈ Sbad →
      (∀ p : ℕ, p.Prime → p ∉ Sbad →
        (¬ p ∣ E.a₁.den ∧ ¬ p ∣ E.a₂.den ∧ ¬ p ∣ E.a₃.den ∧ ¬ p ∣ E.a₄.den ∧ ¬ p ∣ E.a₆.den) ∧
          ¬ (p : ℤ) ∣ E.Δ.num) →
      ∃ Sig : Finset ℕ, Sbad ⊆ Sig ∧ Nonempty (KatoZetaInterface E Sig Sbad)) →
    AppEOutputs E N L

/-- **(3.2) from Kato's printed theorems and Elliot's construction** (PROVED wiring): lane RC9's
PRINT leaf `KatoZetaLeaf`, the non-CM property of `E` (for `E_ℓ`: `j = 35152/9 ∉ ℤ`, lane RC9's
`curve_hasNoCM`), and the ELLIOT step `AppEFromKato` give Proposition `ex:sec7-even-scalar`. -/
theorem evenScalar32_of_kato (hK : KatoZetaLeaf) {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (hCM : HasNoCM E) {N : ℕ} (hN : N ≠ 0) {L : CentralNormalization E}
    (hE : AppEFromKato E N L) : EvenScalar32 E N L :=
  evenScalar32_of_appE hN (hE fun Sbad h2 hgood => hK E hCM Sbad h2 hgood)

end ZInQ.Manuscript.RC.Even
