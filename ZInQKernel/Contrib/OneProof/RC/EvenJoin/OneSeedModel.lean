import ZInQKernel.Contrib.OneProof.RC.EvenJoin.OneSeedLattice
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Model

/-! The formwise carrier with its one active seed. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine PrintsArith TraceLimits O12 ThetaCoeff
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

set_option maxHeartbeats 1000000

variable {I K O G L : Type} [Fintype I] [Field K] [CommRing O] [Algebra O K]
variable [Group G] [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
variable {U : Finset ℕ}
variable (A : Basis I K G (Test T U)) (z : I → K)
variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
variable [TopologicalSpace O] [CompactSpace O] [ContinuousSMul O K] [IsNoetherianRing O]
variable {frob : ℕ → GalQ} (ρ₀ : Attachment A frob)
variable (hinj : Function.Injective (algebraMap O K))
variable (hz : ∀ u n, A.eval n (A.diamond u z) ∈ integralRange (O := O))
variable {m : Ideal O} [Finite (O ⧸ m)]
variable {χ : GalQ →* Multiplicative L}
variable (hχ : OpenTypeKernel χ) (htyp : IsTypeChar T χ)
variable (hm : m.IsMaximal) (htwo : (2 : O) ∈ m) (hclosed : IsClosed (m : Set O))
variable (he : Topology.IsEmbedding (algebraMap O K))
variable (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
variable (D : DeterminantFourierData (oneOps A z ρ₀ (O := O)) m (oneLatSeed A z U))
variable (hD : D.coeff = oneCoeff A z hinj hz)
variable (hFresh : let st := (oneLattice_stable A z ρ₀ hinj hz hfrob).1
  ∀ g h (n : ℕ), n ≠ 0 → oneCoeff A z hinj hz n
    (latT ρ₀.ρ _ st g (latT ρ₀.ρ _ st h (oneLatSeed A z U))) ∈ m)
variable (support : Finset ℕ) (hs : TypeDetectsRadicals χ support)
variable (hlevel : T.m.primeFactors ⊆ support) (hs2 : 2 ∈ support)

/-- The formwise constructor specializes to one attached seed. Its
Fourier indices and coefficient maps are those of the input basis. -/
def oneSeedModel (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (B : ℕ) :
    Σ X : GaloisConstituentModel T R ap B χ, FourierData X := by
  classical
  let F := oneLatSeed A (O := O) z
  have hzero (V : Finset ℕ) (hV : V ≠ U) : F V = 0 :=
    Subtype.ext (oneSeed_other z hV)
  let Dall (V : Finset ℕ) : DeterminantFourierData (oneOps A z ρ₀ (O := O)) m (F V) :=
    if hV : V = U then hV.symm ▸ D else
      { coeff := oneCoeff A z hinj hz
        subscripts := ∅
        pos := fun _ h => (Finset.notMem_empty _ h).elim
        unary := 0
        hecke_eq := oneCoeff_hecke A z ρ₀ hinj hz
        unary_eq := fun _ h => (Finset.notMem_empty _ h).elim
        correction := fun _ _ _ => ⟨0, fun n => by simp [hzero V hV]⟩ }
  have hDall (V : Finset ℕ) : (Dall V).coeff = oneCoeff A z hinj hz := by
    rcases eq_or_ne V U with rfl | h
    · simpa only [Dall, dite_eq_left rfl] using hD
    · simp [Dall, h]
  exact O12Theta.buildWithFormwiseInertia R ap B hχ htyp hm htwo hclosed hinj
    (A.finite (oneSeed z) hinj (oneSeed_integral A z hz)) F hfrob
    (continuousOperators_of_matrix ρ₀.continuous) ρ₀.unramified (oneOps A z ρ₀)
    (oneCoeff A z hinj hz) A.coefK
    (A.hspec (oneSeed z) hinj (oneSeed_integral A z hz)) Dall hDall
    (A.hcoeff (oneSeed z) hinj (oneSeed_integral A z hz) he)
    (fun V _ _ g h n hn => by
      rcases eq_or_ne V U with rfl | hV
      · exact hFresh g h n hn
      · simp only [hzero V hV, map_zero]; exact m.zero_mem)
    support hs hlevel hs2
    (fun V _ _ q hq _ hqV Q hQ hqQ σ hσ W hWV g =>
      oneSeed_trace_inertia A z ρ₀ hWV hq hqV hQ hqQ σ hσ g)

variable (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (B : ℕ)

local notation "Y" => oneSeedModel A z ρ₀ hinj hz hχ htyp hm htwo hclosed he hfrob
  D hD hFresh support hs hlevel hs2 R ap B

theorem oneSeedModel_column (x : I → K) (n : PosIndex) :
    Y.1.coefK x (Y.2.index n) = A.eval n.val x := rfl

theorem oneSeedModel_seed : (Y.1.F U).val = z := oneSeed_same z

theorem oneSeedModel_hecke (q : ℕ) (hq : T.Good q) (hqa : q ∉ U) :
    ∃ d : Y.1.Λ, ∀ n,
      Y.2.coeff n (Y.1.tΛ (Y.1.frob q) (Y.1.F U)) =
        Y.2.coeff (q * n) (Y.1.F U) +
        if q ∣ n then (q : Y.1.O) * Y.2.coeff (n / q) d else 0 := by
  let ops := oneOps A z ρ₀ (O := O)
  refine ⟨ops.diamond q (Y.1.F U), fun n => ?_⟩
  have ht : Y.1.tΛ (Y.1.frob q) (Y.1.F U) = ops.hecke q (Y.1.F U) := by
    apply Subtype.ext
    change tV ρ₀.ρ (frob q) (oneLatSeed A (O := O) z U) =
      (ops.hecke q (oneLatSeed A (O := O) z U)).val
    exact ops.trace_eq q hq hqa (oneLatSeed A (O := O) z U)
  rw [ht]
  exact oneCoeff_hecke A z ρ₀ hinj hz q hq hqa n (Y.1.F U)

end ZInQ.Manuscript.RC.EvenJoin
