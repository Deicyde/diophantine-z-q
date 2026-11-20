import ZInQKernel.Contrib.OneProof.RC.PMAdelic.Geometry

/-! Use the level signs of (O.3) in the special-fibre quotient relation
of Appendix F (tex 8487–8489, 8505–8507, 9331–9339). -/

noncomputable section

open FreeAbelianGroup (of)

namespace ZInQ.Manuscript.RC.AtkinSign

open PMGeometry (DivZero center)
open Stages

/-- The ELLIOT special-fibre inputs with the Atkin–Lehner signs fixed
by the theta stage. The quotient identity is still required on each
supersingular point, before applying the multiplier or detector. -/
structure SpecialFibreAtSigns (ell N : ℕ) [Fact ell.Prime]
    (K : Type*) [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
    (Ebar : WeierstrassCurve (ZMod ell)) (ap : ℕ → ℤ) (X : PMAdelic.CoarseFibre)
    (w : ℕ → ℤˣ) where
  infinity : X.Point
  frobenius_sq : Function.Involutive X.frobenius
  T_infinity : ∀ p, p.Prime → ¬ p ∣ N * ell → X.T p infinity = (p + 1) • of infinity
  frobenius_infinity : X.frobenius infinity = infinity
  J : Type
  [jacobianGroup : AddCommGroup J]
  divisorClass : DivZero X.Point →+ J
  quotient : J →+ PM.ReducedPoints (K := K) Ebar
  hecke_quotient : ∀ p, p.Prime → ¬ p ∣ N * ell → ∀ x ∈ X.ss,
    quotient (divisorClass (center infinity (X.T p x - X.T p infinity))) =
      ap p • quotient (divisorClass (center infinity (of x)))
  /-- ELLIOT (tex 8487–8489): the action on `[W x] - [W infinity]`
  uses the same `w_{p^e}` as (O.3). -/
  atkin_quotient : ∀ p : ℕ, p.Prime → 0 < N.factorization p → ∀ x ∈ X.ss,
    quotient (divisorClass (center infinity (of (X.W p x) - of (X.W p infinity)))) =
      (w p : ℤ) • quotient (divisorClass (center infinity (of x)))
  frobenius_quotient : ∀ x ∈ X.ss,
    quotient (divisorClass (center infinity (of (X.frobenius x) - of (X.frobenius infinity)))) =
      fixedFrob (curveFrob (K := K) Ebar) (quotient (divisorClass (center infinity (of x))))

attribute [instance] SpecialFibreAtSigns.jacobianGroup

namespace SpecialFibreAtSigns

variable {ell N : ℕ} [Fact ell.Prime]
  {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
  {Ebar : WeierstrassCurve (ZMod ell)} {ap : ℕ → ℤ} {X : PMAdelic.CoarseFibre}
  {w : ℕ → ℤˣ}

/-- On-the-spot (c): supply the existing special-fibre interface. All
fields apart from the sign and its proofs are copied directly. -/
def toSpecialFibre (S : SpecialFibreAtSigns ell N K Ebar ap X w) :
    PMAdelic.SpecialFibre ell N K Ebar ap X where
  infinity := S.infinity
  frobenius_sq := S.frobenius_sq
  T_infinity := S.T_infinity
  frobenius_infinity := S.frobenius_infinity
  J := S.J
  jacobianGroup := S.jacobianGroup
  divisorClass := S.divisorClass
  quotient := S.quotient
  hecke_quotient := S.hecke_quotient
  atkinSign := fun p => (w p : ℤ)
  atkinSign_eq := fun p _ _ => Int.isUnit_iff.mp (w p).isUnit
  atkin_quotient := S.atkin_quotient
  frobenius_quotient := S.frobenius_quotient

theorem atkinSign_eq (S : SpecialFibreAtSigns ell N K Ebar ap X w) (p : ℕ) :
    (w p : ℤ) = S.toSpecialFibre.atkinSign p :=
  rfl

/-- On-the-spot (c): any old input already compatible at the level
primes supplies the new input, with the same underlying geometry. -/
def ofSpecialFibre (S : PMAdelic.SpecialFibre ell N K Ebar ap X)
    (hSign : ∀ p : ℕ, p.Prime → 0 < N.factorization p → (w p : ℤ) = S.atkinSign p) :
    SpecialFibreAtSigns ell N K Ebar ap X w where
  infinity := S.infinity
  frobenius_sq := S.frobenius_sq
  T_infinity := S.T_infinity
  frobenius_infinity := S.frobenius_infinity
  J := S.J
  jacobianGroup := S.jacobianGroup
  divisorClass := S.divisorClass
  quotient := S.quotient
  hecke_quotient := S.hecke_quotient
  atkin_quotient := fun p hp he x hx => by
    rw [hSign p hp he]
    exact S.atkin_quotient p hp he x hx
  frobenius_quotient := S.frobenius_quotient

end SpecialFibreAtSigns


end ZInQ.Manuscript.RC.AtkinSign
