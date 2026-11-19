import ZInQKernel.Contrib.OneProof.RC.ThetaCoeff.Operators
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Model

/-! The genuine theta coefficient data, at one stage and one finite pool of primes.
The analytic input realizes the specified theta blocks in a common constituent
space. No hypothesis of reduced diamond congruence or of two fresh traces is used
in constructing the Fourier data. -/

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

/-- The constructor's stationary support cannot contain a good added prime.
This is the independence of the stationary type and the added vertex bit. -/
theorem no_good_mem_stationary
    {chiType : GalQ →* Multiplicative L₀} (htyp : IsTypeChar T chiType)
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    {support : Finset ℕ} (hs : TypeDetectsRadicals chiType support) {p : ℕ}
    (hp : T.Good p) : p ∉ support := by
  intro hpS
  obtain ⟨q, _, _, _, htype, hbits⟩ := exists_good_frob T htyp hfrob {p} ∅
    (fun s hs => (Finset.mem_singleton.mp hs).symm ▸ hp) 0 (fun _ => 1)
  have hR := hs (frob q) htype
  have hp' : sqrtChar (p : ℤ) (frob q) = 1 :=
    congrFun (MonoidHom.mem_ker.1 hR.2) ⟨p, hpS⟩
  have hneg := MonoidHom.mem_ker.1 hR.1
  have hs : ∀ n : ℕ, sqrtChar ((-1 : ℤ) ^ n) (frob q) = 1 := by
    intro n
    induction n with
    | zero => simpa using DFunLike.congr_fun (sqrtChar_sq 1) (frob q)
    | succ n ih =>
      rw [pow_succ, sqrtChar_mul (pow_ne_zero _ (by decide)) (by decide),
        MonoidHom.mul_apply, ih, hneg, one_mul]
  have hex := hbits p (Finset.mem_singleton_self p)
  rw [bitChar_apply, sstar, sqrtChar_mul (pow_ne_zero _ (by decide)) (by exact_mod_cast hp.1.ne_zero),
    MonoidHom.mul_apply, hs, hp', mul_one] at hex
  exact (by decide : (1 : Multiplicative (ZMod 2)) ≠ Multiplicative.ofAdd 1) hex

variable {P : Window T.Good S W} (A : Basis I K G (Test T avoid))
    (E : Lift S) (D₀ : Divisions E δ W R adm) (C : DiamondCharacters O G E.η)
    (V : Blocks (P := P) A E D₀ C)

variable {A E D₀ C}

include V in
/-- The stationary-coverage hypothesis of the existing constructor cannot
handle a pool with an added good level prime. -/
theorem Blocks.pool_empty_of_stationary_cover
    {chiType : GalQ →* Multiplicative L₀} (htyp : IsTypeChar T chiType)
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q) {support : Finset ℕ}
    (hs : TypeDetectsRadicals chiType support)
    (hlevel : T.m.primeFactors ∪ avoid ⊆ support) : P.pool = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hgood := P.type_good p hp
  have hex : p ∈ avoid := by
    by_contra ha
    exact ((Nat.Prime.coprime_iff_not_dvd hgood.1).mp (V.good_coprime p ⟨hgood, ha⟩))
      (V.level_support p hp)
  exact no_good_mem_stationary htyp hfrob hs hgood
    (hlevel (Finset.mem_union_right _ hex))

variable [TopologicalSpace K]
variable (ρ₀ : Attachment (frob := frob) A)
variable (hinj : Function.Injective (algebraMap O K))

/-- The local ramification interface needed at tex 9745–9750. At a prime
outside the active set, only constituents of its subforms need be unramified. -/
theorem Blocks.inertia_le_consN_of_seed
    {chiType : GalQ →* Multiplicative L₀} (htyp : IsTypeChar T chiType)
    {U : Finset ℕ} (hU : ∀ s ∈ U, T.Good s) {q : ℕ} (hq : T.Good q) (hqU : q ∉ U)
    {Q : Ideal Zbar} (hQ : Q.IsMaximal) (hqQ : ((q : ℤ) : Zbar) ∈ Q)
    (hseed : ∀ σ ∈ Q.inertia GalQ, ∀ W ⊆ U, ∀ i, V.seed W i ≠ 0 → ρ₀.ρ i σ = 1)
    {hst : ∀ g, ∀ v ∈ A.Λ (O := O) V.seed, tV ρ₀.ρ g v ∈ A.Λ (O := O) V.seed} :
    Q.inertia GalQ ≤ consN chiType
      (redTrace m (LinearMap.pi fun n : {n : ℕ // n ≠ 0} => V.coeff hinj n) ρ₀.ρ hst V.F) U := by
  intro σ hσ
  obtain ⟨hc, hb⟩ := chars_eq_one_of_mem_inertia T htyp hU hq hqU hQ hqQ hσ
  refine ⟨hc, hb, fun g W hW => ?_⟩
  unfold redTrace
  congr 1
  exact Subtype.ext (V.trace_mul_of_seed_unramified ρ₀ W g σ (hseed σ hσ W hW))

variable [IsTopologicalRing K] [TopologicalSpace O] [T2Space K] [CompactSpace O] [IsNoetherianRing O]
  [ContinuousSMul O K] [Finite (O ⧸ m)]

/-- The stage-local constituent model. The readings and the two reduced trace
hypotheses are the inputs of the other lanes. (Adapted at the fold: the diamond-congruence
hypothesis is no longer an argument of `buildConstituentModel`, which no longer needs it.) -/
def Blocks.build (R₀ : Finset ℕ → ZMod 2) (B : ℕ)
    (chiType : GalQ →* Multiplicative L₀) (hchi : OpenTypeKernel chiType)
    (htyp : IsTypeChar T chiType)
    (hm : m.IsPrime) (h2 : (2 : O) ∈ m) (hclosed : IsClosed (m : Set O))
    (he : Topology.IsEmbedding (algebraMap O K))
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (read : Finset ℕ → ({n : ℕ // n ≠ 0} → O ⧸ m) →+ ZMod 2)
    (h2fresh : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g h,
      ∀ n : ℕ, n ≠ 0 → V.coeff hinj n
        ⟨tV ρ₀.ρ g (tV ρ₀.ρ h (V.F U)),
          (stable_operators T hfrob (lattice_closed _ (A.finite V.seed hinj (V.integral_seed hinj)))
            (V.hcont ρ₀) ρ₀.unramified (V.ops ρ₀)).1 g _
            ((stable_operators T hfrob (lattice_closed _ (A.finite V.seed hinj (V.integral_seed hinj)))
              (V.hcont ρ₀) ρ₀.unramified (V.ops ρ₀)).1 h _ (V.F U).2)⟩ ∈ m)
    (support : Finset ℕ) (hs : TypeDetectsRadicals chiType support)
    (hlevel : T.m.primeFactors ∪ avoid ⊆ support) (hs2 : 2 ∈ support) :
    GaloisConstituentModel T R₀ S.ap B chiType :=
  buildConstituentModel R₀ S.ap B chiType hchi htyp h2 hclosed
    (A.finite V.seed hinj (V.integral_seed hinj)) V.F hfrob (V.hcont ρ₀) ρ₀.unramified
    (V.ops ρ₀) (V.coeff hinj) A.coefK (A.hspec V.seed hinj (V.integral_seed hinj))
    (V.determinant ρ₀ hinj hm h2) (V.hD ρ₀ hinj hm h2)
    (A.hcoeff V.seed hinj (V.integral_seed hinj) he)
    read h2fresh support hs hlevel hs2 V.hzero


end ZInQ.Manuscript.RC.ThetaCoeff
