import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.AtkinLehner.Sign

/-! The unit form of the eigenvalue at an exact divisor (tex 8505–8507,
9331–9341; conversion to integer units is on-the-spot, provenance (c)). -/

set_option autoImplicit false

noncomputable section

open scoped TauCeti.ExactDivisor

namespace ZInQ.Manuscript.RC.AtkinPin

variable {N Q : ℕ} [NeZero N] {k : ℤ}

/-- The two possible complex eigenvalues as units of the integers. -/
def signUnit (f : HeckeRing.GL2.Newform N k) (hχ : f.χ = 1)
    (hQ : Q ∥ N) : ℤˣ :=
  if f.atkinLehnerSign hχ hQ = 1 then 1 else -1

theorem signUnit_cast (f : HeckeRing.GL2.Newform N k) (hχ : f.χ = 1)
    (hQ : Q ∥ N) :
    ((signUnit f hχ hQ : ℤ) : ℂ) = f.atkinLehnerSign hχ hQ := by
  rcases f.atkinLehnerSign_eq_one_or_neg_one hχ hQ with h | h
  · simp [signUnit, h]
  · simp [signUnit, h, show (-1 : ℂ) ≠ 1 by norm_num]

/-- The stage sign at `p` uses the full prime power in the level. Off
the prime support the exact divisor is 1, which has sign 1. -/
def wNew (f : HeckeRing.GL2.Newform N k) (hχ : f.χ = 1) (p : ℕ) : ℤˣ :=
  signUnit f hχ (TauCeti.Nat.isExactDivisor_primePow (p := p))

theorem wNew_cast (f : HeckeRing.GL2.Newform N k) (hχ : f.χ = 1) (p : ℕ) :
    ((wNew f hχ p : ℤ) : ℂ) =
      f.atkinLehnerSign hχ (TauCeti.Nat.isExactDivisor_primePow (p := p)) :=
  signUnit_cast f hχ _


end ZInQ.Manuscript.RC.AtkinPin
