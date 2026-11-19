import ZInQKernel.Contrib.OneProof.RC.ThetaCoeff.Blocks
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Determinant

/-! Good Frobenius operators and the determinant Fourier calculation for the theta blocks. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaCoeff

open Finset TraceLimits AddressGenuine Symbols PrintsArith
open ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups Classical
set_option maxHeartbeats 800000

variable {I K O G L₀ : Type} [Fintype I] [Field K] [CommRing O] [IsDomain O] [CharZero O]
  [Algebra O K] [Group G] [AddCommGroup L₀] {ε : L₀ →+ ZMod 2}
variable {T : TypeData L₀ ε} {avoid : Finset ℕ} {frob : ℕ → GalQ}
variable {M W R : ℕ} {S : AppF.ThetaStage (StageRing O M)} {δ : ℤ} {adm : ℕ → Prop}
variable {m : Ideal O}

abbrev Test (T : TypeData L₀ ε) (avoid : Finset ℕ) (q : ℕ) := T.Good q ∧ q ∉ avoid

variable {P : Window T.Good S W} (A : Basis I K G (Test T avoid))
    (E : Lift S) (D₀ : Divisions E δ W R adm) (C : DiamondCharacters O G E.η)
    (V : Blocks (P := P) A E D₀ C)

variable {A E D₀ C}

variable [TopologicalSpace K]

/-- Carayol's good polynomial (PRINT, tex 9773–9797) for the cuspidal sources;
the diagonal pair is the Eisenstein input (ELLIOT, tex 9653–9654, 9762–9767).
The entries are continuous and the realizations are unramified at the tests. -/
structure Attachment (A : Basis I K G (Test T avoid)) (frob : ℕ → GalQ) where
  ρ : I → GalQ →* GL (Fin 2) K
  continuous : ∀ i, Continuous fun g => ((ρ i g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  unramified : UnramifiedConstituents T avoid ρ
  cusp : ∀ i a χ hz hr, A.base i = .cusp a χ hz hr → ∀ (q : {q // Test T avoid q}),
    (((ρ i (frob q) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace = a q) ∧
    (((ρ i (frob q) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = (q.val : K) * χ q)
  eis : ∀ i α β, A.base i = .eis α β →
    ∃ χ₁ χ₂ : GalQ →* Kˣ,
      (∀ g, ((ρ i g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        Matrix.diagonal ![(χ₁ g : K), (χ₂ g : K)]) ∧
      ∀ (q : {q // Test T avoid q}), (χ₁ (frob q) : K) = α q ∧ (χ₂ (frob q) : K) = (q.val : K) * β q

variable (ρ₀ : Attachment (frob := frob) A)

theorem Attachment.good (i : I) (q : {q // Test T avoid q}) :
    (((ρ₀.ρ i (frob q) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace = (A.base i).a q) ∧
    (((ρ₀.ρ i (frob q) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det =
      (q.val : K) * (A.χ i (A.atPrime q) : K)) := by
  rw [A.χ_good]
  cases h : A.base i with
  | cusp a χ hz hr => exact ρ₀.cusp i a χ hz hr h q
  | eis α β =>
    obtain ⟨χ₁, χ₂, hdiag, hχ⟩ := ρ₀.eis i α β h
    obtain ⟨h₁, h₂⟩ := hχ q
    rw [hdiag]
    simp [h₁, h₂, EigenSource.a, EigenSource.χ,
      eisenstein_at_prime α β (A.prime q q.2), mul_left_comm]

/-- The good operators are the restrictions of the eigenvalue operators. -/
def Blocks.ops : GoodOperators T avoid frob ρ₀.ρ (A.Λ (O := O) V.seed) where
  hecke q := if h : Test T avoid q then A.latHecke V.seed ⟨q, h⟩ else 0
  diamond q := if h : Test T avoid q then A.latDiamond V.seed (A.atPrime ⟨q, h⟩) else 0
  trace_eq q hq ha v := by
    rw [dite_eq_left (show Test T avoid q from ⟨hq, ha⟩)]
    funext i
    exact congrArg (· * (v : I → K) i) (ρ₀.good i ⟨q, hq, ha⟩).1
  det_eq q hq ha v := by
    rw [dite_eq_left (show Test T avoid q from ⟨hq, ha⟩)]
    funext i
    change _ = (((q : O) • A.diamond (A.atPrime ⟨q, hq, ha⟩) (v : I → K)) i)
    rw [Pi.smul_apply, Algebra.smul_def, map_natCast, Basis.diamond, diagonalOp_apply, ← mul_assoc]
    exact congrArg (· * (v : I → K) i) (ρ₀.good i ⟨q, hq, ha⟩).2

theorem Blocks.hcont [IsTopologicalRing K] : ContinuousOperators ρ₀.ρ (A.Λ (O := O) V.seed) :=
  continuousOperators_of_matrix ρ₀.continuous

/-- Formwise unramifiedness suffices to fix the trace orbit; coordinates of the
common space not occurring in the form impose no condition. -/
theorem Blocks.trace_mul_of_seed_unramified (U : Finset ℕ) (g σ : GalQ)
    (hσ : ∀ i, V.seed U i ≠ 0 → ρ₀.ρ i σ = 1) :
    tV ρ₀.ρ (g * σ) (V.F U) = tV ρ₀.ρ g (V.F U) := by
  funext i
  change _ * V.seed U i = _ * V.seed U i
  by_cases hi : V.seed U i = 0
  · simp only [hi, mul_zero]
  · simp only [map_mul, hσ i hi, mul_one]

variable (hinj : Function.Injective (algebraMap O K))

abbrev Blocks.coeff := A.coeff V.seed hinj (V.integral_seed hinj)

omit [TopologicalSpace K] in
include V in
theorem Blocks.test_ne_two (q : ℕ) (hq : Test T avoid q) : q ≠ 2 := by
  intro e
  subst q
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (V.good_coprime 2 hq)
    (dvd_trans (by decide : 2 ∣ 4) C.four_dvd)

/-- Tex 9719–9727, before taking the good trace. `unary` is the undivided
`θΘ_j` block; its scalar absorbs `B_U[j]` and the integral sign correction. -/
def Blocks.determinant (hm : m.IsPrime) (h2 : (2 : O) ∈ m) (U : Finset ℕ) :
    DeterminantFourierData (V.ops ρ₀) m (V.F U) where
  coeff := V.coeff hinj
  subscripts := if U ⊆ P.pool then subscripts U else ∅
  pos j hj := by
    split_ifs at hj with hU
    · exact ((mem_subscripts (fun p hp => S.good_prime p (P.stage_good p (hU hp))) j).mp hj).1.ne_zero
    · exact (Finset.notMem_empty j hj).elim
  unary := E.FourierUnary
  hecke_eq q hq ha := by
    simpa only [Blocks.ops, dite_eq_left (show Test T avoid q from ⟨hq, ha⟩)] using
      A.heckeFourier V.seed hinj (V.integral_seed hinj) ⟨q, hq, ha⟩
  unary_eq j _ n hn := by
    unfold Lift.FourierUnary timesTheta
    rw [E.unary_off hn, zero_add]
    exact m.mul_mem_right _ h2
  correction r hr ha := by
    by_cases hU : U ⊆ P.pool
    · let u := A.atPrime ⟨r, hr, ha⟩
      refine ⟨fun j => (r : O) * V.c U hU u j, fun n => ?_⟩
      rw [ite_eq_left hU]
      have hd : V.coeff hinj n ((r : O) • (V.ops ρ₀).diamond r (V.F U) - V.F U) =
          ((r : O) * C.ψ U u - 1) * E.FourierF D₀ (P.admissible U hU) n +
          ∑ j ∈ subscripts U, ((r : O) * V.c U hU u j) * E.FourierUnary j n := by
        apply hinj
        rw [A.coeff_spec]
        simp only [Blocks.ops, dite_eq_left (show Test T avoid r from ⟨hr, ha⟩)]
        change A.eval n ((r : O) • A.diamond u (V.seed U) - V.seed U) = _
        rw [Blocks.seed, dite_eq_left hU, map_sub, eval_smul_O, V.diamond_eval hinj, V.vector_eval hinj]
        rw [← map_mul, ← map_sub]
        apply congrArg (algebraMap O K)
        simp only [mul_add, Finset.mul_sum, mul_assoc]
        ring
      rw [hd, add_sub_cancel_right]
      exact m.mul_mem_right _ (C.det_scalar u U r hr.1 (V.test_ne_two r ⟨hr, ha⟩) hm h2)
    · refine ⟨0, fun n => ?_⟩
      have hz : V.F U = 0 := Subtype.ext (dite_eq_right hU)
      simp [hz, hU]

theorem Blocks.hD (hm : m.IsPrime) (h2 : (2 : O) ∈ m) (U : Finset ℕ) :
    (V.determinant ρ₀ hinj hm h2 U).coeff = V.coeff hinj := rfl


end ZInQ.Manuscript.RC.ThetaCoeff
