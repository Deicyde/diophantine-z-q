import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Galois
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Determinant

/-! Integral Hecke and diamond translates of one seed, with the same
positive Fourier coordinates as its input basis (tex 9655–9668). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine PrintsArith TraceLimits O12 ThetaCoeff
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

set_option maxHeartbeats 1000000

variable {I K O G L : Type} [Fintype I] [Field K] [CommRing O] [Algebra O K]
variable [Group G] [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
variable {U : Finset ℕ}
variable (A : Basis I K G (Test T U)) (z : I → K)

def oneSeed (V : Finset ℕ) : I → K := by
  classical
  exact if V = U then z else 0

@[simp] theorem oneSeed_same : oneSeed (U := U) z U = z := by simp [oneSeed]

@[simp] theorem oneSeed_other {V : Finset ℕ} (h : V ≠ U) :
    oneSeed (U := U) z V = 0 := by simp [oneSeed, h]

abbrev oneLattice := A.Λ (O := O) (oneSeed (U := U) z)

def oneLatSeed (V : Finset ℕ) : oneLattice A (O := O) z :=
  ⟨oneSeed z V, A.mem_seed (oneSeed z) V⟩

@[simp] theorem oneLatSeed_val (V : Finset ℕ) :
    (oneLatSeed A (O := O) z V).val = oneSeed (U := U) z V := rfl

theorem oneSeed_integral
    (h : ∀ u n, A.eval n (A.diamond u z) ∈ integralRange (O := O)) :
    ∀ V u n, A.eval n (A.diamond u (oneSeed (U := U) z V)) ∈ integralRange (O := O) := by
  intro V u n
  rcases eq_or_ne V U with rfl | hV
  · simpa only [oneSeed_same] using h u n
  · simp only [oneSeed_other z hV, map_zero, Submodule.zero_mem]

variable [TopologicalSpace K] {frob : ℕ → GalQ} (ρ₀ : Attachment A frob)

/-- At the good tests the Hecke and diamond actions agree with Frobenius
trace and scaled determinant on each column. -/
def oneOps : GoodOperators T U frob ρ₀.ρ (oneLattice A (O := O) z) := by
  classical
  refine ⟨fun q => if h : Test T U q then A.latHecke (oneSeed z) ⟨q, h⟩ else 0,
    fun q => if h : Test T U q then A.latDiamond (oneSeed z) (A.atPrime ⟨q, h⟩) else 0, ?_, ?_⟩
  · intro q hq ha v
    rw [dite_eq_left (show Test T U q from ⟨hq, ha⟩)]
    funext i
    exact congrArg (· * (v : I → K) i) (ρ₀.good i ⟨q, hq, ha⟩).1
  · intro q hq ha v
    rw [dite_eq_left (show Test T U q from ⟨hq, ha⟩)]
    funext i
    change _ = (((q : O) • A.diamond (A.atPrime ⟨q, hq, ha⟩) (v : I → K)) i)
    rw [Pi.smul_apply, Algebra.smul_def, map_natCast, Basis.diamond, diagonalOp_apply, ← mul_assoc]
    exact congrArg (· * (v : I → K) i) (ρ₀.good i ⟨q, hq, ha⟩).2

variable (hinj : Function.Injective (algebraMap O K))
variable (hz : ∀ u n, A.eval n (A.diamond u z) ∈ integralRange (O := O))

abbrev oneCoeff (n : ℕ) :=
  A.coeff (oneSeed z) hinj (oneSeed_integral A z hz) n

theorem oneCoeff_hecke (q : ℕ) (hq : T.Good q) (hqa : q ∉ U) :
    HeckeFourier (oneCoeff A z hinj hz) ((oneOps A z ρ₀ (O := O)).hecke q)
      ((oneOps A z ρ₀ (O := O)).diamond q) q := by
  simpa only [oneOps, dite_eq_left (show Test T U q from ⟨hq, hqa⟩)] using
    A.heckeFourier (oneSeed z) hinj (oneSeed_integral A z hz) ⟨q, hq, hqa⟩

variable [IsTopologicalRing K] [T2Space K] [TopologicalSpace O] [CompactSpace O]
variable [ContinuousSMul O K] [IsNoetherianRing O]

include hinj hz in
/-- The finite integral span is closed. Good-prime density gives stability
under both operations of the attached representations. -/
theorem oneLattice_stable
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q) :
    (∀ g, ∀ x ∈ oneLattice A (O := O) z, tV ρ₀.ρ g x ∈ oneLattice A (O := O) z) ∧
    (∀ g, ∀ x ∈ oneLattice A (O := O) z, dV ρ₀.ρ g x ∈ oneLattice A (O := O) z) :=
  stable_operators T hfrob (lattice_closed _ (A.finite (oneSeed z) hinj (oneSeed_integral A z hz)))
    (continuousOperators_of_matrix ρ₀.continuous) ρ₀.unramified (oneOps A z ρ₀)

/-- The only nonzero seed in this model is the row whose level is being
used. On any orbit of subforms, an inertia prime outside that orbit's set
cannot be a ramified prime of an active seed. -/
theorem oneSeed_trace_inertia {V W : Finset ℕ} (hWV : W ⊆ V)
    {q : ℕ} (hq : T.Good q) (hqV : q ∉ V) {Q : Ideal Zbar}
    (hQ : Q.IsMaximal) (hqQ : ((q : ℤ) : Zbar) ∈ Q) (σ : GalQ)
    (hσ : σ ∈ Q.inertia GalQ) (g : GalQ) :
    tV ρ₀.ρ (g * σ) (oneLatSeed A (O := O) z W) = tV ρ₀.ρ g (oneLatSeed A (O := O) z W) := by
  rcases eq_or_ne W U with rfl | hW
  · have h := ρ₀.unramified q hq (fun h => hqV (hWV h)) Q hQ hqQ σ hσ
    funext i
    simp only [tV, scalarOp_apply, map_mul, h i, mul_one]
  · have hzero : oneLatSeed A (O := O) z W = 0 := Subtype.ext (oneSeed_other z hW)
    simp [hzero]

end ZInQ.Manuscript.RC.EvenJoin
