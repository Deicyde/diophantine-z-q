import ZInQKernel.Contrib.OneProof.RC.StageJoin.Actual
import ZInQKernel.Contrib.OneProof.RC.TypeCoverage.Consumers

/-! Feed the actual sieved source to the unchanged Appendix F consumer
domains, using the refined coefficient type (tex 2016–2029, 9670–9674). -/

noncomputable section

open scoped BigOperators

namespace ZInQ.Manuscript.RC.StageJoin

open Eichler O12StageVal ThetaCoeff TypeCoverage TraceLimits AddressGenuine Wiring
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {O : Type} [CommRing O] {a b : ℚ} {R : Order a b}
variable {M N ell : ℕ} [Fact ell.Prime]
variable {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K] [IsSepClosed K]
variable {Ebar : WeierstrassCurve (ZMod ell)} [Ebar.IsElliptic] {ap : ℕ → ℤ}
variable (G : PM.Geometry K R N Ebar ap) (d : PM.Evaluation K Ebar M) (L : ℕ)
variable (F : PMLocal O R M N ell) (B : LateSieve)

/-- Identify the abstract support with this lift's support once the local
constructor has supplied the original coefficient places. -/
theorem coefficientSupport_pm
    (hbase : F.support = insert 2 (insert ell (N.primeFactors ∪ F.m.primeFactors))) :
    coefficientSupport (pmSievedStage G d L F B) N B.primes = Scoeff F B := by
  rw [Scoeff, hbase]
  ext p
  change (p ∈ insert 2 (insert ell (N.primeFactors ∪ F.m.primeFactors ∪ B.primes))) ↔ _
  simp only [Finset.mem_union, Finset.mem_insert]
  tauto

variable {m₁ : ℕ} (hm : 0 < m₁) (h8 : 8 ∣ m₁) (hc : ell.Coprime m₁)

/-- Refine the old stationary modulus, preserving the actual stage's moving bit. -/
abbrev refinedType :=
  coveredType (S := pmSievedStage G d L F B) (N := N) hm h8
    (show (pmSievedStage G d L F B).ℓ₀.Prime from Fact.out (p := ell.Prime)) hc B.prime

/-- The refined intrinsic type for the selected label datum. The equality
identifies the moving prime; the old stationary modulus is exactly `D.m₁`. -/
abbrev labelRefinedType {ℓ : ℕ} {W : WData ℓ} (D : LabelData W) (i : ℕ)
    (hi : D.ℓ₀ i = ell) :=
  refinedType G d L F B D.m₁_pos D.eight₁ (hi ▸ D.ℓ₀_cop₁ i)

abbrev refinedChar :=
  coveredChar (S := pmSievedStage G d L F B) (N := N) hm
    (show (pmSievedStage G d L F B).ℓ₀.Prime from Fact.out (p := ell.Prime)) B.prime

theorem refinedType_primeFactors :
    F.support = insert 2 (insert ell (N.primeFactors ∪ F.m.primeFactors)) →
    (refinedType G d L F B hm h8 hc).m.primeFactors = m₁.primeFactors ∪ Scoeff F B := by
  intro hbase
  calc
    _ = m₁.primeFactors ∪ coefficientSupport (pmSievedStage G d L F B) N B.primes :=
      coveredType_primeFactors hm h8 _ hc B.prime
    _ = _ := congrArg (m₁.primeFactors ∪ ·) (coefficientSupport_pm G d L F B hbase)

/-- The character and stationary support inputs of the existing window model. -/
theorem refinedChar_spec :
    IsTypeChar (refinedType G d L F B hm h8 hc) (refinedChar G d L F B hm) ∧
    OpenTypeKernel
      (L := SqClass (fixedModulus (pmSievedStage G d L F B) N B.primes m₁) × ZMod 2)
      (refinedChar G d L F B hm) ∧
    TypeDetectsRadicals
      (L := SqClass (fixedModulus (pmSievedStage G d L F B) N B.primes m₁) × ZMod 2)
      (refinedChar G d L F B hm) (refinedType G d L F B hm h8 hc).m.primeFactors ∧
    2 ∈ (refinedType G d L F B hm h8 hc).m.primeFactors :=
  ⟨isTypeChar_covered hm h8 _ hc B.prime, openTypeKernel_covered hm _ B.prime,
    detects_radicals_covered hm h8 _ hc B.prime, two_mem_type_support hm h8 _ hc B.prime⟩

variable (hbase : F.support = insert 2 (insert ell (N.primeFactors ∪ F.m.primeFactors)))
include hbase

/-- The stage-domain implication in `thetaData`. -/
theorem refinedType_stage_good {p : ℕ} (hp : (refinedType G d L F B hm h8 hc).Good p) :
    (pmSievedStage G d L F B).Good p := by
  apply pmSievedStage_good G d L F B hp.1
  rw [← coefficientSupport_pm G d L F B hbase]
  exact good_not_mem_support hm h8 _ hc B.prime hp

/-- A finite pool of type-good primes in budget gives an actual stage window. -/
def refinedWindow {W : ℕ} (pool : Finset ℕ) (hW : pool.card ≤ W)
    (hpool : ∀ p ∈ pool, (refinedType G d L F B hm h8 hc).Good p) :
    Window (refinedType G d L F B hm h8 hc).Good (pmSievedStage G d L F B) W where
  pool := pool
  card_le := hW
  type_good := hpool
  stage_good p hp := refinedType_stage_good G d L F B hm h8 hc hbase (hpool p hp)

/-- Every fresh type-good prime is outside the stationary support for
`hseed`, and outside the actual coefficient support and active primes for
`hexcl` and `good_hecke`, whether or not it is in the ambient avoidance set. -/
theorem refined_fresh_domains {q : ℕ} {U : Finset ℕ}
    (hq : (refinedType G d L F B hm h8 hc).Good q) (hqU : q ∉ U) :
    q ∉ (refinedType G d L F B hm h8 hc).m.primeFactors ∧
    q ∉ Scoeff F B ∪ U ∧ (pmSievedStage G d L F B).Good q := by
  refine ⟨fun h => (hq.1.coprime_iff_not_dvd.mp hq.2) (Nat.dvd_of_mem_primeFactors h), ?_, ?_⟩
  · rw [← coefficientSupport_pm G d L F B hbase]
    exact fresh_outside_support hm h8 _ hc B.prime hq hqU
  · exact refinedType_stage_good G d L F B hm h8 hc hbase hq

/-- The old modular level's support bound suffices for every refined good prime. -/
theorem refined_old_good {old : ℕ} (hold : old ≠ 0)
    (hs : old.primeFactors ⊆ Scoeff F B) :
    ∀ q, (refinedType G d L F B hm h8 hc).Good q → q.Coprime old :=
  old_good hm h8 _ hc B.prime hold ((coefficientSupport_pm G d L F B hbase).symm ▸ hs)

/-- The same stage window and old level feed `BlocksPerU.realize_of_stage`. -/
def refinedLevelSetup {W common : ℕ} [NeZero common]
    {P : Window (refinedType G d L F B hm h8 hc).Good (pmSievedStage G d L F B) W}
    {avoid : Finset ℕ} (old : ℕ) (hfour : 4 ∣ old) (hs : old.primeFactors ⊆ Scoeff F B)
    (hcommon : common = old * ∏ p ∈ P.pool, p) (havoid : P.pool ⊆ avoid) :
    BlocksPerU.LevelSetup P avoid common :=
  levelSetup hm h8 _ hc B.prime old hfour ((coefficientSupport_pm G d L F B hbase).symm ▸ hs)
    hcommon havoid

theorem refined_test_coprime_common {W common : ℕ} [NeZero common]
    {P : Window (refinedType G d L F B hm h8 hc).Good (pmSievedStage G d L F B) W}
    {avoid : Finset ℕ} {old : ℕ} (hfour : 4 ∣ old) (hs : old.primeFactors ⊆ Scoeff F B)
    (hcommon : common = old * ∏ p ∈ P.pool, p) (havoid : P.pool ⊆ avoid) :
    ∀ q, Test (refinedType G d L F B hm h8 hc) avoid q → q.Coprime common :=
  (refinedLevelSetup G d L F B hm h8 hc hbase old hfour hs hcommon havoid).test_coprime

#print axioms coefficientSupport_pm
#print axioms refinedType
#print axioms labelRefinedType
#print axioms refinedChar
#print axioms refinedType_primeFactors
#print axioms refinedChar_spec
#print axioms refinedType_stage_good
#print axioms refinedWindow
#print axioms refined_fresh_domains
#print axioms refined_old_good
#print axioms refinedLevelSetup
#print axioms refined_test_coprime_common

end ZInQ.Manuscript.RC.StageJoin
