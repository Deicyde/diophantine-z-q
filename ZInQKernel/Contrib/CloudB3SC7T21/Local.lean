import ZInQKernel.Contrib.OneProof.TYZLemma29Mod2
import ZInQKernel.Contrib.CloudB3SC7T21.LocalPred
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# t21-proof: components of `B̂ = ℍ[𝔸ᶠ_ℚ]` in `ℍ[ℚ_p]`

Task t21-proof. The component of a finite adele at a place `w` of `ℚ`, transported to `ℚ_[p]`
(`p = primesEquiv w`) by Mathlib's `Rat.HeightOneSpectrum.adicCompletion.padicEquiv`; its
coordinatewise extension `piQ w : ℍ[𝔸ᶠ_ℚ] →+* ℍ[ℚ_[p]]`; the components of `qι γ`, of the
centre and of TYZ's `twoRep`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open ZInQ.Contrib.TYZDecomp.H29Split IsDedekindDomain NumberField
open scoped Quaternion

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-! ## Components at a place -/

/-- The prime of a place `w` of `ℚ`. -/
abbrev Pw (w : HeightOneSpectrum (𝓞 ℚ)) : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv w

/-- Mathlib's `padicEquiv` as a ring isomorphism. -/
def pe (w : HeightOneSpectrum (𝓞 ℚ)) : w.adicCompletion ℚ ≃+* ℚ_[Pw w] :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv w : w.adicCompletion ℚ ≃+* ℚ_[Pw w])

/-- The component at `w` of a finite adele, in `ℚ_[p]`. -/
def ev (w : HeightOneSpectrum (𝓞 ℚ)) : AQ →+* ℚ_[Pw w] :=
  (pe w : w.adicCompletion ℚ →+* ℚ_[Pw w]).comp
  { toFun := fun a => a w
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl }

theorem ev_apply (w : HeightOneSpectrum (𝓞 ℚ)) (a : AQ) : ev w a = pe w (a w) := rfl

theorem ev_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) :
    ev w (algebraMap ℚ AQ q) = (q : ℚ_[Pw w]) :=
  eq_ratCast ((ev w).comp (algebraMap ℚ AQ)) q

/-- The component at `w` of an element of `ℍ[𝔸ᶠ_ℚ]`. -/
def piQ (w : HeightOneSpectrum (𝓞 ℚ)) : ℍ[AQ] →+* ℍ[ℚ_[Pw w]] := qmap (ev w)

theorem piQ_qι (w : HeightOneSpectrum (𝓞 ℚ)) (γ : ℍ[ℚ]) : piQ w (qι γ) = qp (Pw w : ℕ) γ := by
  ext <;> simp [piQ, qp, qι]

theorem piQ_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (z : AQ) :
    piQ w (algebraMap AQ ℍ[AQ] z) = ((ev w z : ℚ_[Pw w]) : ℍ[ℚ_[Pw w]]) := by
  rw [← qmap_coe]; rfl

theorem ev_eAt_self (v : HeightOneSpectrum (𝓞 ℚ)) : ev v (eAt v) = 1 := by
  have : (eAt v) v = 1 := if_pos rfl
  rw [ev_apply, this, map_one]

theorem ev_eAt_ne {w v : HeightOneSpectrum (𝓞 ℚ)} (h : w ≠ v) : ev w (eAt v) = 0 := by
  have : (eAt v) w = 0 := if_neg h
  rw [ev_apply, this, map_zero]

theorem piQ_ιAt_self (v : HeightOneSpectrum (𝓞 ℚ)) (α : ℍ[ℚ]) :
    piQ v (ιAt v α) = qp (Pw v : ℕ) α := by
  simp only [ιAt, map_add, map_mul, piQ_algebraMap, piQ_qι, map_sub, map_one, ev_eAt_self]
  simp

theorem piQ_ιAt_ne {w v : HeightOneSpectrum (𝓞 ℚ)} (h : w ≠ v) (α : ℍ[ℚ]) :
    piQ w (ιAt v α) = 1 := by
  simp only [ιAt, map_add, map_mul, piQ_algebraMap, piQ_qι, map_sub, map_one, ev_eAt_ne h]
  simp

/-- An element of `ℍ[𝔸ᶠ_ℚ]` is determined by its components. -/
theorem piQ_injective {x y : ℍ[AQ]} (h : ∀ w, piQ w x = piQ w y) : x = y := by
  have hev : ∀ a b : AQ, (∀ w, ev w a = ev w b) → a = b := fun a b hab => by
    ext1 w
    have := hab w
    rw [ev_apply, ev_apply] at this
    exact (pe w).injective this
  apply QuaternionAlgebra.ext
  · exact hev _ _ fun w => congrArg (·.re) (h w)
  · exact hev _ _ fun w => congrArg (·.imI) (h w)
  · exact hev _ _ fun w => congrArg (·.imJ) (h w)
  · exact hev _ _ fun w => congrArg (·.imK) (h w)

end ZInQ.Contrib.T21Proof
