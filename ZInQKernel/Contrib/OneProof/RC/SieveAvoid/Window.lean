import ZInQKernel.Contrib.OneProof.RC.SieveAvoid.Fourier
import ZInQKernel.Contrib.OneProof.RC.SieveAvoid.Model
import ZInQKernel.Contrib.OneProof.RC.O12Realize.Window

/-! Restricted inertia and Hecke operators on the one common space.
The coarser type quotient is conditional on the extra local sieve test. -/
noncomputable section

namespace ZInQ.Manuscript.RC.SieveAvoid

open O12Realize AddressGenuine PrintsArith TraceLimits ThetaCoeff O12 O12Theta Finset
open ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {I K O G L : Type} [Fintype I] [Field K]
  [CommRing O] [IsDomain O] [CharZero O] [Algebra O K] [Group G] [AddCommGroup L]
variable {ε : L →+ ZMod 2} {T : TypeData L ε} {χ : GalQ →* Multiplicative L}
variable {avoid Scoeff : Finset ℕ} {frob : ℕ → GalQ} {m : Ideal O} {B : ℕ}
variable {M W R : ℕ} {δ : ℤ} {adm : ℕ → Prop} {S : AppF.ThetaStage (StageRing O M)}
variable {P : Window T.Good S W} {A : Basis I K G (Test T avoid)}
variable {E : Lift S} {D : Divisions E δ W R adm} {C : DiamondCharacters O G E.η}
variable (V : Blocks (P := P) A E D C)
variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
  [TopologicalSpace O] [CompactSpace O] [IsNoetherianRing O] [ContinuousSMul O K] [Finite (O ⧸ m)]
variable (ρ₀ : Attachment A frob) (hinj : Function.Injective (algebraMap O K))

/-- Formwise inertia on each actual seed, outside its own added primes and
the actual coefficient support (tex 9745–9750). -/
def InertiaOn' (Scoeff : Finset ℕ) : Prop :=
  ∀ U ⊆ P.pool, U.card + 1 ≤ B →
    ∀ q, T.Good q → q ∉ Scoeff ∪ U →
    ∀ Q : Ideal Zbar, Q.IsMaximal → ((q : ℤ) : Zbar) ∈ Q →
    ∀ σ ∈ Q.inertia GalQ, ∀ i, V.seed U i ≠ 0 → ρ₀.ρ i σ = 1

/-- Test the extra sieve inertia in the elementary quotient of the exact
lattice and coefficient family used below. -/
abbrev WindowSieveInertia (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (support Scoeff : Finset ℕ) : Prop :=
  let st := (stable_operators T hfrob
    (lattice_closed _ (A.finite V.seed hinj (V.integral_seed hinj)))
    (V.hcont ρ₀) ρ₀.unramified (V.ops ρ₀)).1
  let expand : A.Λ (O := O) V.seed →ₗ[O] (PosIndex → O) := LinearMap.pi fun n => V.coeff hinj n
  ∀ U, (∀ p ∈ U, T.Good p) → U.card + 1 ≤ B →
    SieveInertia (T := T) χ (redTrace m expand ρ₀.ρ st V.F) support Scoeff U

/-- Construct the model on the actual common lattice. No operator or
inertia statement on forms outside the pool is needed from the stage. -/
def commonSpace' (R₀ : Finset ℕ → ZMod 2)
    (hχ : OpenTypeKernel χ) (htyp : IsTypeChar T χ)
    (hm : m.IsMaximal) (h2 : (2 : O) ∈ m) (hclosed : IsClosed (m : Set O))
    (he : Topology.IsEmbedding (algebraMap O K))
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (support : Finset ℕ) (hs : TypeDetectsRadicals χ support)
    (hlevel : T.m.primeFactors ⊆ support) (hs2 : 2 ∈ support)
    (h2fresh : TwoFreshOn (m := m) V ρ₀ hinj hfrob B)
    (_havoid : Scoeff ⊆ avoid)
    (hseed : InertiaOn' (B := B) V ρ₀ Scoeff)
    (hsieve : WindowSieveInertia (χ := χ) (m := m) (B := B) V ρ₀ hinj hfrob support Scoeff) :
    Σ X : GaloisConstituentModel T R₀ S.ap B χ, FourierData X :=
  buildWithRestrictedInertia R₀ S.ap B hχ htyp hm h2 hclosed hinj
    (A.finite V.seed hinj (V.integral_seed hinj)) V.F hfrob (V.hcont ρ₀)
    ρ₀.unramified (V.ops ρ₀) (V.coeff hinj) A.coefK
    (A.hspec V.seed hinj (V.integral_seed hinj))
    (V.determinant ρ₀ hinj hm.isPrime h2) (V.hD ρ₀ hinj hm.isPrime h2)
    (A.hcoeff V.seed hinj (V.integral_seed hinj) he)
    (by
      intro st U _ hB g h n hn
      by_cases hU : U ⊆ P.pool
      · exact h2fresh U hU hB g h n hn
      · have hz : V.F U = 0 := Subtype.ext (dite_eq_right hU)
        rw [hz, map_zero, map_zero, map_zero]
        exact m.zero_mem)
    support Scoeff hs hlevel hs2
    (by
      intro U _ hB q hq hqa Q hQ hqQ σ hσ V' hV g
      apply V.trace_mul_of_seed_unramified ρ₀ V' g σ
      intro i hi
      have hVP : V' ⊆ P.pool := by
        by_contra hh
        exact hi (by simp [Blocks.seed, hh])
      exact hseed V' hVP ((Nat.add_le_add_right (card_le_card hV) 1).trans hB) q hq
        (fun e => hqa (Finset.union_subset_union_right (s := Scoeff) hV e)) Q hQ hqQ σ hσ i hi)
    hsieve


variable {N : BlockLevels' Scoeff V}

omit [IsTopologicalRing K] [T2Space K] [TopologicalSpace O]
  [CompactSpace O] [IsNoetherianRing O] [ContinuousSMul O K] in
/-- The restricted inertia input follows from the retained occurrence levels. -/
theorem inertiaOn_of_levels (H : AtLevel' N ρ₀) : InertiaOn' (B := B) V ρ₀ Scoeff := by
  intro U _ _ q hq hf Q hQ hqQ σ hσ i hi
  exact seed_unramified H hq hf hQ hqQ hσ (Finset.Subset.refl U) hi

set_option maxHeartbeats 800000 in
/-- On the same window lattice, the excluded-prime formula is needed only
away from the coefficient support. -/
theorem window_good_hecke [IsLocalRing O] (H : AtLevel' N ρ₀)
    (R₀ : Finset ℕ → ZMod 2) (hχ : OpenTypeKernel χ) (htyp : IsTypeChar T χ)
    (hm : m.IsMaximal) (h2 : (2 : O) ∈ m) (hclosed : IsClosed (m : Set O))
    (he : Topology.IsEmbedding (algebraMap O K))
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (support : Finset ℕ) (hs : TypeDetectsRadicals χ support)
    (hlevel : T.m.primeFactors ⊆ support) (hs2 : 2 ∈ support)
    (h2fresh : TwoFreshOn (m := m) V ρ₀ hinj hfrob B) (havoid : Scoeff ⊆ avoid)
    (hsieve : WindowSieveInertia (χ := χ) (m := m) (B := B) V ρ₀ hinj hfrob support Scoeff) :
    FormwiseHecke' (commonSpace' (B := B) V ρ₀ hinj R₀ hχ htyp hm h2 hclosed he hfrob
      support hs hlevel hs2 h2fresh havoid (inertiaOn_of_levels V ρ₀ H) hsieve).2 Scoeff := by
  let Y := commonSpace' (B := B) V ρ₀ hinj R₀ hχ htyp hm h2 hclosed he hfrob
    support hs hlevel hs2 h2fresh havoid (inertiaOn_of_levels V ρ₀ H) hsieve
  refine formwiseHecke_of_ambient Y.2 (V.ops ρ₀)
    (V.determinant ρ₀ hinj hm.isPrime h2) (fun _ => rfl) ?_
  intro U q _ hq hf _ _
  obtain ⟨diamondF, _, _, hF⟩ :=
    seed_fourier H hinj hm h2 Y.1.stable_t Y.1.stable_d hq hf (hfrob q hq)
  exact ⟨diamondF, hF⟩

#print axioms commonSpace'
#print axioms inertiaOn_of_levels
#print axioms window_good_hecke

end ZInQ.Manuscript.RC.SieveAvoid
