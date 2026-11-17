/-
Lean 4.35 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 compatibility lemma for the H5 lane4
port of anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2 (source written
against Mathlib db584cd6d46c92f209a44c0f1c829460d327499d).

Mathlib 56a redefined `MvPolynomial.coeff` as the `AddMonoidAlgebra.coeff` field (`p.coeff m`)
and turned `MvPolynomial.coeff_zero` into a deprecated, type-changed, argument-free lemma
`(0 : MvPolynomial σ R).coeff = 0`.  The source applies the db584 lemma
`coeff_zero (m : σ →₀ ℕ) : coeff m (0 : MvPolynomial σ R) = 0` to an argument.  This file restates
that lemma, with the argument, in Mathlib 56a's `p.coeff m` notation (the port writes the source's
`coeff m p` as `p.coeff m`), under the port prefix `ZInQ.Contrib.CloudW03NeronSurj.FLT`. No axiom.
Source of the statement: Mathlib (Apache License 2.0) db584, Mathlib/Algebra/MvPolynomial/Basic.lean.
NOTICE OF MODIFICATION (Apache-2.0 §4(b)), H5 lane4, 2026-11-14: statement adapted to the
Mathlib 56a coefficient notation; proof `by simp`.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace MvPolynomial

theorem coeff_zero {R : Type*} [CommSemiring R] {σ : Type*} (m : σ →₀ ℕ) :
    (0 : _root_.MvPolynomial σ R).coeff m = 0 := by
  simp

end MvPolynomial

end ZInQ.Contrib.CloudW03NeronSurj.FLT
