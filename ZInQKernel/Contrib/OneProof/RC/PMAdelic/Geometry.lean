import ZInQKernel.Contrib.OneProof.RC.PMAdelic.Comparison

/-!
# Appendix F geometry for the proved level order

After the class-set comparison (GLUE, `JetchevKane`) and the operator
comparison (ELLIOT, `OperatorComparison`), only ELLIOT's modular special-fibre
statements are needed for the supersingular stage. The divisor identities and the
affine cusp term are handled by the imported `PMGeometry.Geometry`.
-/

noncomputable section

open FreeAbelianGroup (of)

namespace ZInQ.Manuscript.RC.PMAdelic

open Eichler Adelic Stages
open PMGeometry (DivZero center)

/-- The remaining ELLIOT inputs for the coarse model `X`. The class-set
comparison is supplied by `JetchevKane` (GLUE) and all operator comparisons on
supersingular points by `OperatorComparison` (ELLIOT). -/
structure SpecialFibre (ell N : ℕ) [Fact ell.Prime]
    (K : Type*) [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
    (Ebar : WeierstrassCurve (ZMod ell)) (ap : ℕ → ℤ) (X : CoarseFibre) where
  infinity : X.Point
  /-- The coarse points are over the quadratic residue field (tex 8470–8473). -/
  frobenius_sq : Function.Involutive X.frobenius
  /-- The good Hecke correspondence at the base cusp (tex 8480–8487). -/
  T_infinity : ∀ p, p.Prime → ¬ p ∣ N * ell → X.T p infinity = (p + 1) • of infinity
  /-- The base cusp is rational (tex 8479–8487, 9347–9355). -/
  frobenius_infinity : X.frobenius infinity = infinity
  J : Type
  [jacobianGroup : AddCommGroup J]
  divisorClass : DivZero X.Point →+ J
  /-- Good reduction and extension of the quotient (tex 8476–8481). -/
  quotient : J →+ PM.ReducedPoints (K := K) Ebar
  /-- The specialized quotient intertwines good Hecke operators (tex 8481–8487). -/
  hecke_quotient : ∀ p, p.Prime → ¬ p ∣ N * ell → ∀ x ∈ X.ss,
    quotient (divisorClass (center infinity (X.T p x - X.T p infinity))) =
      ap p • quotient (divisorClass (center infinity (of x)))
  atkinSign : ℕ → ℤ
  atkinSign_eq : ∀ p : ℕ, p.Prime → 0 < N.factorization p →
    atkinSign p = 1 ∨ atkinSign p = -1
  /-- Atkin–Lehner eigenrelation on the degree-zero class (tex 8487–8489, 9336–9339). -/
  atkin_quotient : ∀ p : ℕ, p.Prime → 0 < N.factorization p → ∀ x ∈ X.ss,
    quotient (divisorClass (center infinity (of (X.W p x) - of (X.W p infinity)))) =
      atkinSign p • quotient (divisorClass (center infinity (of x)))
  /-- Frobenius compatibility of the rational quotient (tex 9347–9355). -/
  frobenius_quotient : ∀ x ∈ X.ss,
    quotient (divisorClass (center infinity (of (X.frobenius x) - of (X.frobenius infinity)))) =
      fixedFrob (curveFrob (K := K) Ebar) (quotient (divisorClass (center infinity (of x))))

attribute [instance] SpecialFibre.jacobianGroup

variable {ell N : ℕ} [Fact ell.Prime] {h : ell % 4 = 3} {hN : 0 < N} {hcop : N.Coprime ell}
  {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
  {Ebar : WeierstrassCurve (ZMod ell)} {ap : ℕ → ℤ} {X : CoarseFibre}

/-- The special-fibre model with its comparison fields discharged on the
proved level order. -/
def geometricInput (C : JetchevKane ell h N hN hcop X)
    (O : OperatorComparison ell h N hN hcop X C) (S : SpecialFibre ell N K Ebar ap X) :
    PMGeometry.GeometricInput (adelic ell h N hN hcop) K Ebar ap where
  Point := X.Point
  ss := X.ss
  infinity := S.infinity
  classes := C.idealClasses
  T := X.T
  W := X.W
  frobenius := X.frobenius
  frobenius_sq := S.frobenius_sq
  frobenius_ss := O.frobenius_ss
  hecke_compare := O.hecke_compare
  atkin_compare := O.atkin_compare
  frobenius_compare := O.frobenius_compare
  T_infinity := S.T_infinity
  frobenius_infinity := S.frobenius_infinity
  J := S.J
  jacobianGroup := S.jacobianGroup
  divisorClass := S.divisorClass
  quotient := S.quotient
  hecke_quotient := S.hecke_quotient
  atkinSign := S.atkinSign
  atkinSign_eq := S.atkinSign_eq
  atkin_quotient := S.atkin_quotient
  frobenius_quotient := S.frobenius_quotient

/-- Appendix F's geometry at the constructed level order, conditional on
the class-set comparison (GLUE), the operator comparison (ELLIOT) and the
indicated modular special-fibre statements. -/
def geometry (C : JetchevKane ell h N hN hcop X)
    (O : OperatorComparison ell h N hN hcop X C) (S : SpecialFibre ell N K Ebar ap X) :
    PM.Geometry K (levelOrder ell h N hN) N Ebar ap :=
  (geometricInput C O S).geometry


end ZInQ.Manuscript.RC.PMAdelic
