import Mathlib
import ZInQKernel.Contrib.OneProof.RC.AppF.Stage

/-!
# App F: the fields of `ThetaStage` are jointly satisfiable (consistency check only)

Given the PRINT `VoightMainThm1461` (for `ram`), a one-class stage with zero lift `P = 0` and empty
lattices satisfies every field of `ThetaStage`. This only shows that the record is not contradictory
(its `aθ` is `0`); it is not the manuscript's stage, whose existence is the missing theory described
in `docs/research/rc-appF-theta.md`. PROVED.
-/

namespace ZInQ.Manuscript.RC.AppF

open ZInQ.Manuscript.RC.Odd

/-- The empty `p`-frame. -/
def emptyFrame (p : ℕ) (R : Type*) [CommRing R] : PFrame p R where
  V := Empty
  vecs := fun _ => ∅
  coord := fun x => x.elim
  F := fun x => x.elim
  scale := fun x => x.elim
  coord_det := fun _ x hx => by simp at hx
  scale_mem := fun _ x _ => x.elim
  div_mem := fun _ y _ _ => y.elim
  scale_inj := fun x => x.elim
  coord_scale := fun x => x.elim

/-- **PROVED.** A (trivial) `ThetaStage` exists, relative to the leaf `VoightMainThm1461`. -/
noncomputable def trivialStage (R : Type*) [CommRing R] (hV : VoightMainThm1461) (ℓ₀ m : ℕ)
    (hℓ₀ : ℓ₀.Prime) : ThetaStage R where
  ℓ₀ := ℓ₀
  qa := (hV ℓ₀ hℓ₀).choose
  qb := (hV ℓ₀ hℓ₀).choose_spec.choose
  ram := (hV ℓ₀ hℓ₀).choose_spec.choose_spec
  X := Unit
  w := fun _ => 1
  w_pos := fun _ => one_pos
  w_dvd := fun _ => one_dvd _
  P := fun _ => 0
  χN := fun _ => 1
  θ := fun _ _ => 0
  m := m
  Good := fun p => p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ m
  good_prime := fun _ h => h.1
  good_ne_two := fun _ h => h.2.1
  good_m := fun _ h => h.2.2
  ap := fun _ => 0
  s := fun p => (jacobiSym (-(m : ℤ)) p : R)
  sinv := fun p => (jacobiSym (-(m : ℤ)) p : R)
  s_unit := fun p hp => by
    haveI := Fact.mk hp.1
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    have h0 : ((-(m : ℤ) : ℤ) : ZMod p) ≠ 0 := by
      intro h
      apply hp.2.2
      have : (p : ℤ) ∣ -(m : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h
      exact Int.natCast_dvd_natCast.mp (dvd_neg.mp this)
    rcases legendreSym.eq_one_or_neg_one p h0 with h | h <;> rw [h] <;> push_cast <;> ring
  η := fun _ => 1
  η_mul := fun _ _ => (mul_one 1).symm
  η_one := rfl
  η_good := fun p hp => by
    haveI := Fact.mk hp.1
    show (1 : R) = (jacobiSym (-(m : ℤ)) p : R) * (jacobiSym (-(m : ℤ)) p : R)
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    have h0 : ((-(m : ℤ) : ℤ) : ZMod p) ≠ 0 := by
      intro h
      apply hp.2.2
      have : (p : ℤ) ∣ -(m : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h
      exact Int.natCast_dvd_natCast.mp (dvd_neg.mp this)
    rcases legendreSym.eq_one_or_neg_one p h0 with h | h <;> rw [h] <;> push_cast <;> ring
  nb := fun _ _ _ => ()
  hecke := fun _ _ _ => by simp
  adjoint := fun _ _ _ _ => rfl
  frame := fun p _ _ => emptyFrame p R
  frame_theta := fun _ _ _ _ => by simp [PFrame.theta, emptyFrame]
  frame_scale := fun _ _ _ x => x.elim
  frame_nbr := fun p _ _ _ _ => by
    haveI : IsEmpty (emptyFrame p R).V := inferInstanceAs (IsEmpty Empty)
    simp [PFrame.nbrSum, Finset.eq_empty_of_isEmpty]
  theta_zero := fun _ => rfl

end ZInQ.Manuscript.RC.AppF
