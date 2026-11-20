import ZInQKernel.Contrib.OneProof.HKRefereed.HKRefereedConsumed
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.ModularNewformPrinted
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent
import ZInQKernel.Contrib.RC53Assist.G0Prints.Carayol

/-! # The rational point in Gross–Zagier (7.3)(1) and the pole argument -/

namespace ZInQ.Manuscript.HKGZ73

open ZInQ.Contrib.CloudB3RC53 (IsLContinuation)
open ZInQ.Contrib.CloudB3RC53.CST (HasCuspFormAtLevel newformLevel)
open ZInQ.Contrib.RC53Assist.BCDTPrint (BCDTThmAPrinted bcdtThmA_of_printed)
open ZInQ.Contrib.RC53Assist.G0Prints (associatedGeometricConductorExponent)
open ZInQ.Contrib.RC53Assist.NewformGlueG0 (Li1975StrongMultiplicityOneWeightTwo)
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent
  (Shimura1973ConjugateEigenforms Carayol1986RationalNewformEulerFactors
    Faltings1983EulerFactorRigidityQ liCarayolNewformOfModular_of_printed_corollaries)
open RC.PrintsAnalytic
  (IsNewformOf isLContinuation_eq isModular_of_isNewformOf modularNewform_of_printed)
open HeckeRing.GL2 (Newform)
open UpperHalfPlane

/-- A positive integer is the geometric conductor of `E` if its prime exponents
are the Artin conductor exponents of the cohomological Tate representations.
At a place `p` the auxiliary Tate prime `q` is distinct from `p`. -/
def IsGeometricConductorLevel (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) : Prop :=
  0 < N ∧
    ∀ (q p : ℕ) [Fact q.Prime] [Fact p.Prime], p ≠ q →
      associatedGeometricConductorExponent E q p = (N.factorization p : ℚ)

/-- **Print draft**: Gross–Zagier, Invent. Math. 84 (1986), Thm (7.3)(1), p. 231 (AI-READ).
Under the standing assumption of a weight-two newform of `E/ℚ` at its conductor,
if `L(E,1) = 0` and `L'(E,1) ≠ 0`, then `E(ℚ)` has a point of infinite order.
The value and derivative are of the uncompleted continuation. -/
def GZ73Print : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2),
    IsGeometricConductorLevel E N → IsNewformOf E f →
    ∀ F : ℂ → ℂ, IsLContinuation E F → F 1 = 0 → deriv F 1 ≠ 0 →
      ∃ P : E.toAffine.Point, ¬ IsOfFinAddOrder P

/-- The modular level used for a pole curve (tex L1779–1784) is its geometric
conductor. This comparison is GLUE: `newformLevel` is defined by cusp forms,
while `IsGeometricConductorLevel` uses the cohomological Tate representations. -/
def PoleNewformLevelIsConductor : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 →
    ∀ [(curve (ℓ : ℚ)).IsElliptic], PoleS12.IsModular (curve (ℓ : ℚ)) →
      IsGeometricConductorLevel (curve (ℓ : ℚ)) (newformLevel (curve (ℓ : ℚ)))

/-- The tree's newform has the least matching cusp-form level. Extract a newform
from the cusp form at that least level; divisibility and minimality give equality.
Li's uniqueness of the level then applies to any matching newform. -/
theorem level_eq_newformLevel_of_isNewformOf
    (hS : Shimura1973ConjugateEigenforms) (hL : Li1975StrongMultiplicityOneWeightTwo)
    (hC : Carayol1986RationalNewformEulerFactors) (hF : Faltings1983EulerFactorRigidityQ)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) {N : ℕ} [NeZero N]
    {f : Newform N 2} (hf : IsNewformOf E f) : N = newformLevel E := by
  obtain ⟨K, hK, g, hg⟩ := isModular_of_isNewformOf hf
  have hne : {j : ℕ | 0 < j ∧ HasCuspFormAtLevel E j}.Nonempty := ⟨K, hK, g, hg⟩
  have hmin : 0 < newformLevel E ∧ HasCuspFormAtLevel E (newformLevel E) :=
    Nat.sInf_mem hne
  obtain ⟨hpos, g₀, hg₀⟩ := hmin
  obtain ⟨M, hM, G, hdiv, hχ, hcoeff⟩ :=
    liCarayolNewformOfModular_of_printed_corollaries hS hL hC hF
      E hE (newformLevel E) hpos g₀ hg₀
  let : NeZero M := hM
  have hG : IsNewformOf E G := ⟨hχ, hcoeff⟩
  have hmem : G.toCuspForm ∈ cuspFormCharSpace 2 (1 : (ZMod M)ˣ →* ℂˣ) := by
    have h := G.mem_charSpace
    rwa [hχ] at h
  have hAt : HasCuspFormAtLevel E M := by
    refine ⟨TauCeti.cuspFormCharSpaceOneEquiv M 2 ⟨G.toCuspForm, hmem⟩, fun n hn => ?_⟩
    rw [TauCeti.coe_cuspFormCharSpaceOneEquiv_apply]
    exact hcoeff n hn
  have hle : newformLevel E ≤ M :=
    Nat.sInf_le (s := {j : ℕ | 0 < j ∧ HasCuspFormAtLevel E j}) ⟨NeZero.pos M, hAt⟩
  have hMN : M = newformLevel E := le_antisymm (Nat.le_of_dvd hpos hdiv) hle
  have hNM : N = M := (hL N M f G hf.1 hG.1
    ⟨∅, fun p hp _ => (hf.2 p hp.pos).trans (hG.2 p hp.pos).symm⟩).1
  exact hNM.trans hMN

/-- Analytic rank one is precisely the two central conditions on the entire
continuation, in the arithmetic normalization of the print. -/
theorem analyticRankOne_iff_exists_value_deriv (E : WeierstrassCurve ℚ) :
    AnalyticRankOne E ↔
      ∃ F : ℂ → ℂ, IsLContinuation E F ∧ F 1 = 0 ∧ deriv F 1 ≠ 0 := by
  have horder (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
      analyticOrderAt F 1 = 1 ↔ F 1 = 0 ∧ deriv F 1 ≠ 0 := by
    rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by rfl,
      analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hF.analyticAt (1 : ℂ))]
    simp
  constructor
  · rintro ⟨F, hFd, hFL, h⟩
    exact ⟨F, ⟨hFd, hFL⟩, (horder F hFd).mp h⟩
  · rintro ⟨F, hF, h⟩
    exact ⟨F, hF.1, hF.2, (horder F hF.1).mpr h⟩

/-- The value and derivative criterion holds for any given continuation, since
two entire continuations agree everywhere. -/
theorem analyticRankOne_iff_value_deriv {E : WeierstrassCurve ℚ} {F : ℂ → ℂ}
    (hF : IsLContinuation E F) : AnalyticRankOne E ↔ F 1 = 0 ∧ deriv F 1 ≠ 0 := by
  rw [analyticRankOne_iff_exists_value_deriv]
  constructor
  · rintro ⟨G, hG, h⟩
    rwa [isLContinuation_eq hG hF] at h
  · exact fun h => ⟨F, hF, h⟩

/-- The infinite-order point needed in the pole argument from Gross–Zagier's
printed central-derivative implication, the existing modularity route, and
the geometric conductor comparison. -/
theorem hkConsumed_of_gz73 (hGZ : GZ73Print) (hB : BCDTThmAPrinted)
    (hS : Shimura1973ConjugateEigenforms) (hL : Li1975StrongMultiplicityOneWeightTwo)
    (hC : Carayol1986RationalNewformEulerFactors) (hF : Faltings1983EulerFactorRigidityQ)
    (hCond : PoleNewformLevelIsConductor) :
    HKRefereed.HKConsumed := by
  intro ℓ hℓ hsf hmod _ hModular hA
  let E := curve (ℓ : ℚ)
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
  let : E.IsElliptic := PoleRC.curve_isElliptic hℓ0
  obtain ⟨N, hN, f, hf⟩ :=
    modularNewform_of_printed (bcdtThmA_of_printed hB) hS hL hC hF E inferInstance
  let : NeZero N := hN
  have hlevel := level_eq_newformLevel_of_isNewformOf hS hL hC hF
    (inferInstance : E.IsElliptic) hf
  have hNcond : IsGeometricConductorLevel E N := by
    rw [hlevel]
    exact hCond ℓ hℓ hsf hmod hModular
  obtain ⟨F, hcont, hval, hderiv⟩ := (analyticRankOne_iff_exists_value_deriv E).mp hA
  exact hGZ E N f hNcond hf F hcont hval hderiv

end ZInQ.Manuscript.HKGZ73
