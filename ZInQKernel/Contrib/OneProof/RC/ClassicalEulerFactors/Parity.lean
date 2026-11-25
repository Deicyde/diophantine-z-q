import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Parity
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.ModularNewformPrinted
import ZInQKernel.Contrib.CloudB3RC53.Hasse.Final
import ZInQKernel.Contrib.CloudB3RC53.Assembly

/-! # Analytic-order parity (a consequence form, GLUE) for the restricted converse

This supplies the sign used in `diophantine_zq.tex` lines 1792–1796.
It does not change the curve, the Selmer hypothesis or the subsequent proof.
- a consequence form of the earlier parity interface is derived, not assumed;
- the existing newform development supplies a nonzero analytic continuation
  and proves that its order of vanishing at the center is finite;
- no local epsilon-sign identification is an input to this argument. -/

namespace ZInQ.Manuscript.RC.PrintsAnalytic

open ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Contrib.RC53Assist.NewformGlueG0 (Li1975StrongMultiplicityOneWeightTwo)
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent
  (Shimura1973ConjugateEigenforms Carayol1986RationalNewformEulerFactors
    Faltings1983EulerFactorRigidityQ)

/-- **GLUE (consequence form).** Dokchitser–Dokchitser, *On the Birch–Swinnerton-Dyer quotients
modulo squares*, Annals of Mathematics 172 (2010), Theorem 4.19 (= Theorem 1.4), specialized to
`p = 2`, with the analytic order in place of the root number. It absorbs the root-number bridge
that `DokchitserThm18` already marks GLUE. Locator UNVERIFIED: no reading of the Annals statement
is on record (p. 593 is as cited, not read).
The two integers stand for the corank of the genuine `2^∞`-Selmer group and the order of the
actual complex Hasse–Weil `L`-function at 1. The print assumes no rational isogeny and no
finiteness of Sha. The premises specifying the two integers do not assert the existence of those
integers; the analytic order is witnessed independently in the application. -/
def DokchitserAnnalsThm419AtTwo : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ r m : ℕ,
    Z2Corank (selmerTwoPower E) r → AnalyticRank E m → Nat.ModEq 2 r m

private theorem neg_one_pow_eq_pow_mod_two' (n : ℕ) :
    (-1 : ℤ) ^ n = (-1 : ℤ) ^ (n % 2) := by
  calc
    (-1 : ℤ) ^ n = (-1 : ℤ) ^ (n % 2 + 2 * (n / 2)) :=
      congrArg (fun k : ℕ => (-1 : ℤ) ^ k) (Nat.mod_add_div n 2).symm
    _ = (-1 : ℤ) ^ (n % 2) := by
      rw [pow_add, pow_mul, show (-1 : ℤ) ^ 2 = 1 by decide, one_pow, mul_one]

/-- Use the newform functional equation and its actual finite analytic order.
The corresponding power of `-1` determines the sign of that same equation. -/
theorem rootNumber_of_annals419 (hA : DokchitserAnnalsThm419AtTwo)
    (hM : ModularNewform) {E : WeierstrassCurve ℚ} (hE : E.IsElliptic)
    {r : ℕ} (hr : Z2Corank (selmerTwoPower E) r) : RootNumber E ((-1) ^ r) := by
  letI : E.IsElliptic := hE
  have hH : HasseConvergence := Hasse.hasseConvergence_proved
  obtain ⟨N, hN, f, hf⟩ := hM E hE
  letI : NeZero N := hN
  obtain ⟨w, -, hw⟩ := rootNumber_of_isNewformOf hH hf
  let m : ℕ := f.analyticRank (show (0 : ℤ) < 2 by decide)
  have hm : AnalyticRank E m := (analyticRank_iff_newformAnalyticRank hH hf m).mpr rfl
  have hpar := hA E hE r m hr hm
  change r % 2 = m % 2 at hpar
  have hs := rootNumber_parity_of_analyticRank hw hm
  have hsign : (-1 : ℤ) ^ r = w := by
    calc
      (-1 : ℤ) ^ r = (-1 : ℤ) ^ (r % 2) := neg_one_pow_eq_pow_mod_two' r
      _ = (-1 : ℤ) ^ (m % 2) := congrArg (fun n : ℕ => (-1 : ℤ) ^ n) hpar
      _ = (-1 : ℤ) ^ m := (neg_one_pow_eq_pow_mod_two' m).symm
      _ = w := hs
  rw [hsign]
  exact hw

/-- Supply the old analytic consequence interface. The 2-torsion condition
of that interface is unused by this consequence form of the Annals theorem over `ℚ`. -/
theorem dokchitserThm18_of_annals419 (hA : DokchitserAnnalsThm419AtTwo)
    (hM : ModularNewform) : DokchitserThm18 := by
  intro E hE _ r hr
  exact rootNumber_of_annals419 hA hM hE hr

/-- Reconstruct the existing bundle without asking for a completed `Prints`.
The modularity and newform inputs already occur on this route. -/
theorem prints_of_annals419 (hA : DokchitserAnnalsThm419AtTwo)
    (hB : ZInQ.Manuscript.PoleS12.BCDTThmA)
    (hK : KolyvaginThm1Printed) (hCST : CST.CSTThm11Split)
    (hS : Shimura1973ConjugateEigenforms) (hL : Li1975StrongMultiplicityOneWeightTwo)
    (hC : Carayol1986RationalNewformEulerFactors) (hF : Faltings1983EulerFactorRigidityQ) : Prints :=
  ⟨hB, hK, dokchitserThm18_of_annals419 hA (modularNewform_of_printed hB hS hL hC hF), hCST⟩

/-- The exact node needed before selecting the manuscript's genus partner. -/
theorem rootNumberNode_of_annals419 (hA : DokchitserAnnalsThm419AtTwo)
    (hM : ModularNewform) : RootNumberNode := by
  intro ℓ hadm hSel
  have hℓ : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hadm.1.ne'
  simpa using rootNumber_of_annals419 hA hM (ZInQ.Manuscript.PoleRC.curve_isElliptic hℓ) hSel

end ZInQ.Manuscript.RC.PrintsAnalytic
