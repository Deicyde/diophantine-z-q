import ZInQKernel.Contrib.OneProof.RC.O12Formwise.Fourier
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Window

/-! Supply the two formwise comparisons to the existing window model.
Actual realizations are asserted only on the finite window. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Formwise

open ThetaCoeff AddressGenuine PrintsArith TraceLimits O12 O12Theta
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {I K O G L : Type} [Fintype I] [Field K] [TopologicalSpace K] [CommRing O] [IsDomain O]
  [CharZero O] [Algebra O K] [Group G] [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {avoid : Finset ℕ} {frob : ℕ → GalQ} {m : Ideal O}
variable {M W R : ℕ} {S : AppF.ThetaStage (Odd.StageRing O M)} {δ : ℤ} {adm : ℕ → Prop}
variable {P : Window T.Good S W} {A : Basis I K G (Test T avoid)}
variable {E : Lift S} {D : Divisions E δ W R adm} {C : DiamondCharacters O G E.η}
variable {V : Blocks (P := P) A E D C} {N : BlockLevels V} {ρ₀ : Attachment (frob := frob) A}
variable [IsTopologicalRing K] [T2Space K] [TopologicalSpace O]
  [CompactSpace O] [IsNoetherianRing O] [ContinuousSMul O K] [Finite (O ⧸ m)]

variable (H : AtLevel N ρ₀) (hinj : Function.Injective (algebraMap O K))
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

/-- The existing window model with `hseed` supplied by the retained levels. -/
def windowModelOfLevels : Σ X : GaloisConstituentModel T R₀ S.ap B χ, FourierData X :=
  windowModel V hinj ρ₀ R₀ B χ hχ htyp hm h2 hclosed he hfrob h2fresh support hs hlevel hs2
    (fun _ _ _ _ hq _ hqU _ hQ hqQ _ hσ _ hU₀ _ hi => seed_unramified H hq hqU hQ hqQ hσ hU₀ hi)

set_option maxHeartbeats 800000 in
/-- The window's `good_hecke` field uses the ambient formula at its tests
and `seed_fourier` on the actual form at the excluded primes. -/
theorem window_good_hecke [IsLocalRing O] :
    (windowModelOfLevels H hinj R₀ B χ hχ htyp hm h2 hclosed he hfrob h2fresh support hs hlevel hs2).2.FormwiseHecke := by
  let Y := windowModelOfLevels H hinj R₀ B χ hχ htyp hm h2 hclosed he hfrob h2fresh support hs hlevel hs2
  refine formwiseHecke_of_ambient Y.2 (V.ops ρ₀)
    (V.determinant ρ₀ hinj hm.isPrime h2) (fun _ => rfl) ?_
  intro U q _ hq hqU _ _
  obtain ⟨diamondF, _, _, hF⟩ := seed_fourier H hinj hm h2 Y.1.stable_t Y.1.stable_d hq hqU (hfrob q hq)
  exact ⟨diamondF, hF⟩

#print axioms windowModelOfLevels
#print axioms window_good_hecke

end ZInQ.Manuscript.RC.O12Formwise
