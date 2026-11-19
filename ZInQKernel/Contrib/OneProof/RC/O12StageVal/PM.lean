import ZInQKernel.Contrib.OneProof.RC.PM.Theta
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Source

/-! The integral and finite-precision weighted sums use the same ideal classes, local
weights and (P_M) (tex 8476–8494, 8600–8621, 9059–9093). -/

noncomputable section

open scoped Quaternion

namespace ZInQ.Manuscript.RC.O12StageVal
set_option maxHeartbeats 800000

open Eichler ZInQ.Manuscript.RC.Odd ThetaCoeff
open Finset

variable {O : Type} [CommRing O] {a b : ℚ} {R : Order a b} {M : ℕ}

/-- The integral ternary coefficients of the one local theta datum. -/
def inner (f : ClassSet R → ℍ[ℚ,a,0,b] → O) (z : ClassSet R) (n : ℕ) : O :=
  ∑ᶠ x ∈ {x : ℍ[ℚ,a,0,b] | x.re = 0 ∧ Visibility.nrd x = (n : ℚ)}, f z x

/-- Local input to (O.4) and the Brandt calculation, with its actual Fourier support
specified by `support`. No neighbour eigenfunction or coefficient-lift equality is a field.
The local weights, line indices, and frame comparisons are the existing App F inputs. -/
structure PMLocal (O : Type) [CommRing O] {a b : ℚ} (R : Order a b)
    (M N ell : ℕ) where
  ha : a < 0
  hb : b < 0
  m : ℕ
  support : Finset ℕ
  away : ∀ p, p.Prime → p ∉ support → ¬ p ∣ N * ell
  neTwo : ∀ p, p.Prime → p ∉ support → p ≠ 2
  goodM : ∀ p, p.Prime → p ∉ support → ¬ p ∣ m
  lines : ∀ p (hp : p.Prime ∧ p ∉ support), LineIndex R p hp.1.ne_zero
  f : ClassSet R → ℍ[ℚ,a,0,b] → O
  f_conj : ∀ z, ∀ u ∈ classG ha hb z, ∀ x, f z (↑u * x * ↑u⁻¹) = f z x
  χN : ClassSet R → O
  finiteSupp : ∀ z (n : ℚ),
    {x : ℍ[ℚ,a,0,b] | x.re = 0 ∧ Visibility.nrd x = n ∧ f z x ≠ 0}.Finite
  thetaZero : ∀ z, inner f z 0 = 0
  s : ℕ → O
  sinv : ℕ → O
  sUnit : ∀ p, p.Prime → p ∉ support → s p * sinv p = 1
  sOrder : ∀ p, p.Prime → p ∉ support → ∃ k : ℕ, s p ^ (2 ^ k : ℕ) = 1
  η : ℕ → O
  ηMul : ∀ x y, η (x * y) = η x * η y
  ηOne : η 1 = 1
  ηGood : ∀ p, p.Prime → p ∉ support → η p = s p * (jacobiSym (-(m : ℤ)) p : O)
  parity : Fin 2
  frame : ∀ p, p.Prime ∧ p ∉ support → ClassSet R → AppF.PFrame p (StageRing O M)
  frameTheta : ∀ p hp z n,
    stageReduction O M (inner f z n) = (frame p hp z).theta n
  frameScale : ∀ p hp z x,
    (frame p hp z).F ((frame p hp z).scale x) = stageReduction O M (s p) * (frame p hp z).F x
  frameNb : ∀ p (hp : p.Prime ∧ p ∉ support) z i n,
    stageReduction O M
      (χN (nb (fun _ h => h.1) lines p z i) * inner f (nb (fun _ h => h.1) lines p z i) n) =
      (jacobiSym (-(m : ℤ)) p : StageRing O M) * stageReduction O M (χN z) *
        (stageReduction O M (sinv p) * (frame p hp z).nbrSum i n)

variable {N ell : ℕ} [Fact ell.Prime]
variable {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K] [IsSepClosed K]
variable {Ebar : WeierstrassCurve (ZMod ell)} [Ebar.IsElliptic] {ap : ℕ → ℤ}
variable (G : PM.Geometry K R N Ebar ap) (d : PM.Evaluation K Ebar M) (L : ℕ)
variable (F : PMLocal O R M N ell)

/-- The existing App F stage assembled with the actual finite (P_M) and the reductions
of the chosen integral local data. Its elliptic coefficient function is `ap` by construction. -/
def pmStage : AppF.ThetaStage (StageRing O M) :=
  PM.appFStage G d L F.ha F.hb
    (fun z => stageReduction O M (F.χN z))
    (fun z n => stageReduction O M (inner F.f z n))
    F.m (fun p => p.Prime ∧ p ∉ F.support) (fun _ hp => hp.1)
    (fun p hp => F.away p hp.1 hp.2) (fun p hp => F.neTwo p hp.1 hp.2)
    (fun p hp => F.goodM p hp.1 hp.2) F.lines
    (fun p => stageReduction O M (F.s p)) (fun p => stageReduction O M (F.sinv p))
    (fun p => stageReduction O M (F.η p))
    (fun p hp => by rw [← map_mul, F.sUnit p hp.1 hp.2, map_one])
    (fun x y => by rw [F.ηMul, map_mul]) (by rw [F.ηOne, map_one])
    (fun p hp => by rw [F.ηGood p hp.1 hp.2, map_mul, map_intCast])
    F.frame F.frameTheta F.frameScale
    (fun p hp z i n => by simpa only [map_mul] using F.frameNb p hp z i n)
    (fun z => by rw [F.thetaZero, map_zero])

/-- Use any chosen integral lift of (P_M) on those very ideal classes. The same
integral sum reduces coefficientwise via `Lift.aθ_reduce`. -/
def pmLift (u : ClassSet R → ℤ) (hu : PM.IsLift G d L u) : Lift (pmStage G d L F) where
  geom := PM.visibilityStage G d L F.ha F.hb F.f F.f_conj F.χN F.finiteSupp u hu
  classes := Equiv.refl _
  mass := fun _ => rfl
  P := fun z => by
    change stageReduction O M (u z : O) = PM.stageCast O M (PM.P G d L z)
    rw [PM.stageCast_P G d L hu z, map_intCast]
  normChar := fun _ => rfl
  localSum := fun _ _ => rfl
  η := F.η
  phase := fun _ => rfl
  parity := F.parity

/-- One choice of the integral lift: the least nonnegative representatives of (P_M). -/
def pmValLift : Lift (pmStage G d L F) :=
  pmLift G d L F (PM.valLift G d L) (PM.isLift_valLift G d L)

/-- The lift vanishes at zero because the local inner sums do (tex 9092). -/
theorem pmLift_zero (u : ClassSet R → ℤ) (hu : PM.IsLift G d L u) :
    (pmLift G d L F u hu).aθ 0 = 0 := by
  unfold Lift.aθ Lift.H Visibility.thetaCoeff
  simp only [mul_zero, Nat.cast_zero]
  apply Finset.sum_eq_zero
  intro z _
  change _ * inner F.f z 0 = 0
  exact mul_eq_zero_of_right _ (F.thetaZero z)

/-- The actual signed Brandt recurrence on the chosen lifts after stage reduction.
The finite Hecke eigenrelation is the one proved for (P_M) in `PM.P_hecke`. -/
theorem pmLift_recur (u : ClassSet R → ℤ) (hu : PM.IsLift G d L u)
    {p : ℕ} (hp : (pmStage G d L F).Good p) :
    @RecAt (StageRing O M) _ p ⟨(pmStage G d L F).good_prime p hp⟩
      (stageReduction O M ((pmLift G d L F u hu).η p))
      (O12Theta.ratio p ((pmStage G d L F).good_prime p hp)) (ap p)
      (fun n => stageReduction O M ((pmLift G d L F u hu).aθ n)) := by
  simp only [(pmLift G d L F u hu).phase, (pmLift G d L F u hu).aθ_reduce, O12Theta.ratio]
  exact (pmStage G d L F).recAt hp

omit [Fact ell.Prime] in
/-- The exact order statement for the good character follows from the two-power
order of the root character and the quadratic twist value (tex 8424–8426, 8504–8512). -/
theorem PMLocal.eta_order {p : ℕ} (hp : p.Prime) (hs : p ∉ F.support) :
    ∃ k : ℕ, F.η p ^ (2 ^ k : ℕ) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hχ : jacobiSym (-(F.m : ℤ)) p = 1 ∨ jacobiSym (-(F.m : ℤ)) p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    exact legendreSym_neg_eq_one_or (F.goodM p hp hs) (ε := 1) (Or.inl rfl) |>.imp
      (fun h => by simpa using h) (fun h => by simpa using h)
  obtain ⟨k, hk⟩ := F.sOrder p hp hs
  have hsq : ((jacobiSym (-(F.m : ℤ)) p : ℤ) : O) ^ 2 = 1 := by
    rcases hχ with h | h <;> rw [h] <;> push_cast <;> ring
  refine ⟨k + 1, ?_⟩
  rw [F.ηGood p hp hs, mul_pow, pow_succ (2 : ℕ), pow_mul, hk, one_pow,
    mul_comm (2 ^ k) 2, pow_mul, hsq, one_pow, one_mul]

#print axioms inner
#print axioms pmStage
#print axioms pmLift
#print axioms pmValLift
#print axioms pmLift_zero
#print axioms pmLift_recur
#print axioms PMLocal.eta_order

end ZInQ.Manuscript.RC.O12StageVal
