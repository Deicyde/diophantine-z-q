import ZInQKernel.Contrib.OneProof.RC.ThetaCoeff.Operators
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Model
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Expansions

/-! The model and coefficient-one functional for the actual finite window.
The model's zero extension outside the pool is incidental to this construction;
only the forms on the window are realized by these blocks. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Theta

open AddressGenuine PrintsArith TraceLimits ZInQ.Manuscript.RC.Odd ThetaCoeff O12
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {I K O G L : Type} [Fintype I] [Field K] [CharZero K]
  [CommRing O] [IsDomain O] [CharZero O] [Algebra O K] [Group G]
  [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {avoid : Finset ℕ} {frob : ℕ → GalQ} {m : Ideal O}
variable {M W R : ℕ} {S : AppF.ThetaStage (StageRing O M)} {δ : ℤ} {adm : ℕ → Prop}
variable {P : Window T.Good S W} {A : Basis I K G (Test T avoid)}
variable {E : Lift S} {D : Divisions E δ W R adm} {C : DiamondCharacters O G E.η}
variable (V : Blocks (P := P) A E D C)
variable (hinj : Function.Injective (algebraMap O K))

/-- On the actual seed, the integral coefficient agrees with `H_U` modulo
integer two. This is the `theta_mod_two` comparison on the window. -/
theorem window_theta_mod_two (U : Finset ℕ) (hU : U ⊆ P.pool) (n : ℕ) :
    (2 : O) ∣ V.coeff hinj n (V.F U) - E.HU D (P.admissible U hU) n := by
  rw [V.coeff_F hinj U hU]
  exact fourierF_sub_hu E D (P.admissible U hU) n

/-- A nontrivial budget tests a singleton outside every finite pool. Hence
the window realization hypothesis alone does not cover the full interface. -/
theorem window_misses_test (P : Window T.Good S W) {B : ℕ} (hB : 2 ≤ B)
    {χ : GalQ →* Multiplicative L} (htyp : IsTypeChar T χ)
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q) :
    ∃ U : Finset ℕ, (∀ p ∈ U, T.Good p) ∧ U.card + 1 ≤ B ∧ ¬ U ⊆ P.pool := by
  obtain ⟨q, hq, -, hqpool, -, -⟩ :=
    exists_good_frob T htyp hfrob ∅ P.pool (by simp) 0 (fun _ => 0)
  refine ⟨{q}, ?_, by simpa using hB, fun h => hqpool (h (Finset.mem_singleton_self q))⟩
  intro p hp
  exact (Finset.mem_singleton.mp hp).symm ▸ hq

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
variable [TopologicalSpace O] [CompactSpace O] [IsNoetherianRing O]
variable [ContinuousSMul O K] [Finite (O ⧸ m)]

/-- The particular constituent lattice and positive Fourier coordinates of
the actual theta forms in the finite window, with the coefficient-one reading
built into the model. The formwise ramification input only tests constituents
occurring in the relevant seed. This constructor does not assert that any
of the window's zero extensions is an actual theta form. -/
def windowModel (ρ₀ : Attachment (frob := frob) A)
    (R₀ : Finset ℕ → ZMod 2) (B : ℕ)
    (χ : GalQ →* Multiplicative L) (hχ : OpenTypeKernel χ) (htyp : IsTypeChar T χ)
    (hm : m.IsMaximal) (h2 : (2 : O) ∈ m) (hclosed : IsClosed (m : Set O))
    (he : Topology.IsEmbedding (algebraMap O K))
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (h2fresh : let st := (stable_operators T hfrob
        (lattice_closed _ (A.finite V.seed hinj (V.integral_seed hinj)))
        (V.hcont ρ₀) ρ₀.unramified (V.ops ρ₀)).1
      ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g h,
        ∀ n : ℕ, n ≠ 0 →
          V.coeff hinj n (latT ρ₀.ρ _ st g (latT ρ₀.ρ _ st h (V.F U))) ∈ m)
    (support : Finset ℕ) (hs : TypeDetectsRadicals χ support)
    (hlevel : T.m.primeFactors ⊆ support) (hs2 : 2 ∈ support)
    (hseed : ∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
      ∀ q, T.Good q → q ∉ support → q ∉ U →
      ∀ Q : Ideal Zbar, Q.IsMaximal → ((q : ℤ) : Zbar) ∈ Q →
      ∀ σ ∈ Q.inertia GalQ, ∀ W ⊆ U, ∀ i, V.seed W i ≠ 0 → ρ₀.ρ i σ = 1) :
    Σ X : GaloisConstituentModel T R₀ S.ap B χ, FourierData X :=
  buildWithFormwiseInertia R₀ S.ap B hχ htyp hm h2 hclosed hinj
    (A.finite V.seed hinj (V.integral_seed hinj)) V.F hfrob (V.hcont ρ₀)
    ρ₀.unramified (V.ops ρ₀) (V.coeff hinj) A.coefK
    (A.hspec V.seed hinj (V.integral_seed hinj))
    (V.determinant ρ₀ hinj hm.isPrime h2) (V.hD ρ₀ hinj hm.isPrime h2)
    (A.hcoeff V.seed hinj (V.integral_seed hinj) he) h2fresh support hs hlevel hs2
    (fun U hu hb q hq hqs hqu Q hQ hqQ σ hσ W hW g =>
      V.trace_mul_of_seed_unramified ρ₀ W g σ (hseed U hu hb q hq hqs hqu Q hQ hqQ σ hσ W hW))

#print axioms window_theta_mod_two
#print axioms window_misses_test
#print axioms windowModel

end ZInQ.Manuscript.RC.O12Theta
