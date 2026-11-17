import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Odd.DivisionsFinal
import ZInQKernel.Contrib.OneProof.RC.Odd.Visibility

/-!
# Lane RC12-odd: Elliot's App F constructions as statements, and their consumers

Manuscript (11/5), Appendix F. The constructions below are Elliot's own and are not formalized
(kind ELLIOT): the weighted ternary theta form and its transformation law (tex 8409–9100, with
Weil, Acta Math. 111 (1964), I.13–I.14, II.25–II.30, III Thm 6 — PRINT, locators UNVERIFIED; Voight,
*Quaternion algebras*, Main Thm 14.6.1, Prop. 14.6.7 — PRINT, UNVERIFIED; Jetchev–Kane
arXiv:0908.3905 §§1.1–1.2, 2.5 — PRINT, UNVERIFIED), and the depth minimum chosen in App G
(tex 10151–10256, batch-3 area). Half-integral-weight forms, quaternion orders and the Weil
representation do not exist in Mathlib, so each construction is stated by the property its
consumers use: the coefficient function of one actual stage, with its recurrence (O.6), support and
depth inequality (`OddStageSource`), and the comparison (O.7) (`ThetaComparison`).

The consumers are PROVED: `O9_odd_stage`, `O11_odd_stage` (the integer divisions at one stage,
over `𝒪/2^M𝒪`, here modelled by `ZMod (2^M)` after phase removal) and `visibility_of_comparison`
((O.8) in the skeleton's shape).
-/

namespace ZInQ.Manuscript.RC.Odd

/-- **ELLIOT (`ex:app-theta-form` (O.4)–(O.6), tex 8409–9100; depth: `ex:app-odd-minimum`,
tex 10151–10256).** At one actual stage of precision `M` and depth `δ`, the phase-removed odd
coefficients `a : ℕ → ZMod (2^M)` (`a(n) = H_M(mn)`) satisfy: the recurrence (O.6) at every good prime
(`a_q ≡ q + 1 (mod 4)`, `ψ/η = ±1`), `a(0) = 0`, the depth inequality truncated at `M`, and
`η` completely multiplicative. Non-vacuity: the hypotheses do not force `a = 0` (the witness `D_w`
has `v₂ a_M(D_w) = c_θ + c_w < M`, `witness_vZ`). -/
def OddStageSource (M δ : ℕ) (η : ℕ → ZMod (2 ^ M)) (Good : ℕ → Prop) (ap : ℕ → ℤ)
    (a : ℕ → ZMod (2 ^ M)) : Prop :=
  SourceHyp M δ η Good ap a

/-- **PROVED ((O.9) at one odd stage, tex 9578–9584).** -/
theorem O9_odd_stage {M δ : ℕ} {η : ℕ → ZMod (2 ^ M)} {Good : ℕ → Prop} {ap : ℕ → ℤ}
    {a : ℕ → ZMod (2 ^ M)} (H : OddStageSource M δ η Good ap a) (U : List ℕ) (hnd : U.Nodup)
    (hU : ∀ p ∈ U, Good p) (n : ℕ) :
    (2 : ZMod (2 ^ M)) ^ (min M (δ + U.length + (oddPart n \ U.toFinset).card)) ∣ TL η U a n :=
  O9 H U hnd hU n

/-- **PROVED ((O.11) at one odd stage, tex 9618–9636).** -/
theorem O11_odd_stage {M δ : ℕ} {η : ℕ → ZMod (2 ^ M)} {Good : ℕ → Prop} {ap : ℕ → ℤ}
    {a : ℕ → ZMod (2 ^ M)} (H : OddStageSource M δ η Good ap a) (U : List ℕ) (hnd : U.Nodup)
    (hU : ∀ p ∈ U, Good p) (θ : ℕ → ℤ) (hθ : ∀ m, Odd m → Odd (θ m)) {n m : ℕ} (hn : n ≠ 0)
    (hm : m ≠ 0) (hmodd : Odd m) (hJ : oddPart n ⊆ U.toFinset) (hgood : ∀ q ∈ m.primeFactors, Good q) :
    (2 : ZMod (2 ^ M)) ^ (min M (δ + U.length + 1)) ∣
      TL η U a (n * m ^ 2) - TL η U a n * (η m * (θ m : ZMod (2 ^ M))) :=
  O11_theta H U hnd hU θ hθ hn hm hmodd hJ hgood

/-- **ELLIOT + PRINT (`ex:app-theta-comparison` (O.7), tex 9101–9405; Cornut–Jetchev Thm 3.1,
`CornutJetchevThm31`).** At every stage `θ` and admissible `D` with `(D/ℓ₀) = 1`, the phase-removed
coefficient is congruent to `c₀ 2^{ω(N)} ζ λ_θ(D)` modulo `2^{M_θ}`, `ζ` odd, `λ_θ(D)` an integer lift
of `λ_{M_θ}(\overline{LP_D})`. The orientation count behind it is PROVED (`O7_assembly`,
`orbit_sum`, `orientation_signs`, `cj_kappa_eq_one`, `cj_bijection_of_kappa_one`). -/
def ThetaComparison (M : ℕ → ℕ) (aθ lam : ℕ → ℤ → ℤ) (admissible : ℕ → ℤ → Prop) (ω : ℕ) : Prop :=
  ∀ θ D, admissible θ D → ∃ ζ : ℤ, Odd ζ ∧ (2 : ℤ) ^ M θ ∣ aθ θ D - (c0 : ℤ) * 2 ^ ω * ζ * lam θ D

/-- **PROVED ((O.8), tex 9407–9445)** from (O.7), the native-index bound (ELLIOT/GLUE) and the
height formula (Cai–Shu–Tian Thm 1.1, PRINT; `CST.CSTThm11Split` of the shared layer). The last
conjunct is the skeleton's `RCSteps.visibility` with `SimpleZero D := ord_{s=1} L(E^{(D)}, s) = 1`. -/
theorem visibility_of_comparison (M : ℕ → ℕ) (aθ lam : ℕ → ℤ → ℤ) (admissible : ℕ → ℤ → Prop)
    (SimpleZero : ℤ → Prop) (jgen : ℤ → ℤ) (ω : ℕ) (C : ℤ)
    (hO7 : ThetaComparison M aθ lam admissible ω)
    (hnative : ∀ θ D, admissible θ D → SimpleZero D → ∀ k : ℕ, k ≤ M θ → (k : ℤ) ≤ jgen D - C →
      (2 : ℤ) ^ k ∣ lam θ D)
    (htorsion : ∀ θ D, admissible θ D → ¬ SimpleZero D → (2 : ℤ) ^ M θ ∣ lam θ D) :
    ∃ Cdet : ℤ, ∀ θ D, admissible θ D → vZ (aθ θ D) < ((M θ : ℤ) : WithTop ℤ) →
      SimpleZero D ∧ ((jgen D : ℤ) : WithTop ℤ) ≤ vZ (aθ θ D) + (Cdet : WithTop ℤ) :=
  (visibility_O8 M aθ lam admissible SimpleZero jgen ω C hO7 hnative htorsion).2.2

end ZInQ.Manuscript.RC.Odd
