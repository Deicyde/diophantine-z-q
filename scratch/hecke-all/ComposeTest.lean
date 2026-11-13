import ZInQKernel.Contrib.HeckeAll.Continuation

/-! Composition test: a GaussPointCount stated over independent verbatim copies of normFiber, unitOf, gz
(as in another task's copy of HeckeFE.lean) is accepted by heckeContinuation_of_gaussPointCount (defeq). -/

open Complex
namespace HeckeAllComposeTest
noncomputable def gz (a b : ℝ) (p : ℤ × ℤ) : ℂ := ((p.1 : ℂ) + a) + ((p.2 : ℂ) + b) * I

def normFiber (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
    (fun p => p.1 ^ 2 + p.2 ^ 2 = n)


def unitOf (t : ZMod 4 × ZMod 4) : ℂ :=
  if t = (1, 0) ∨ t = (3, 2) then 1
  else if t = (3, 0) ∨ t = (1, 2) then -1
  else if t = (0, 3) ∨ t = (2, 1) then I
  else if t = (0, 1) ∨ t = (2, 3) then -I
  else 0

def GaussPointCount : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 →
    (p : ℂ) - (Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - xy.1} : ℂ) =
      (1 / 4) * ∑ q ∈ normFiber p, unitOf ((q.1 : ZMod 4), (q.2 : ZMod 4)) * gz 0 0 q

end HeckeAllComposeTest

example (h : HeckeAllComposeTest.GaussPointCount) : ZInQ.Literature.HeckeContinuation :=
  ZInQ.Contrib.heckeContinuation_of_gaussPointCount h
