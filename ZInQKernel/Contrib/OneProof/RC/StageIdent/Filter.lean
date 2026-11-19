import ZInQKernel.Contrib.OneProof.RC.O12StageVal.Apply
import ZInQKernel.Contrib.OneProof.RC.Stages.Sequence
import ZInQKernel.Contrib.OneProof.RC.Stages.AnalyticWitness

/-! The actual Fourier support and the stationary address exclusions are kept
separate (tex 2016–2029, 9471–9483). Choosing the label fields from the selected
stages and passing between the finset and modulus descriptions is on-the-spot (c). -/

noncomputable section

open ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.AddressGenuine ZInQ.Manuscript.RC.O12StageVal
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped Classical

namespace ZInQ.Manuscript.RC.StageIdent

variable {At : ℕ → ℕ → Prop} {cw : ℕ} {S : Finset ℕ}

/-- Positive squarefree indices, the prescribed fixed unit classes, the actual
coefficient exclusions, and the moving split test. No later label sieve. -/
def sourceFilter (q : StageSequence At cw S) (unit support : Finset ℕ) (i : ℕ) (D : ℤ) :
    Prop :=
  (positivePrepared unit D ∧ ∀ p ∈ support, ¬ (p : ℤ) ∣ D) ∧ stageTest q i D

/-- The moving split test already excludes divisibility by the moving prime. -/
theorem stageTest_not_dvd (q : StageSequence At cw S) {i : ℕ} {D : ℤ}
    (h : stageTest q i D) : ¬ ((q.stage i).p : ℤ) ∣ D := by
  let : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  intro hd
  have hz := (legendreSym.eq_zero_iff (q.stage i).p D).mpr
    ((ZMod.intCast_zmod_eq_zero_iff_dvd D (q.stage i).p).mpr hd)
  have h1 : legendreSym (q.stage i).p D = 1 := h
  rw [h1] at hz
  exact one_ne_zero hz

variable {ℓ : ℕ} {W : WData ℓ} (Q : LabelData W)
  (q : StageSequence At cw S) (unit : Finset ℕ)

/-- Retain the fixed moduli but pick the moving prime and intrinsic filter
from the construction. The supplied address exclusions may be larger; the
compatibility field holds on indices avoiding them. -/
def labelsAtStages (hs : withStages W q W.prepared = W)
    (havoid : Q.m.primeFactors ⊆ S)
    (hfixed : Q.m₁.primeFactors ⊆ W.S)
    (hprime : ∀ p ∈ W.S, p.Prime)
    (hprep : W.prepared = fun D => positivePrepared unit D ∧ ∀ p ∈ W.S, ¬ (p : ℤ) ∣ D) : LabelData W := { Q with
  ℓ₀ i := (q.stage i).p
  ℓ₀_prime i := (q.stage i).prime
  ℓ₀_cop i := ((q.stage i).prime.coprime_iff_not_dvd).mpr fun hd =>
    q.excluded i (havoid (Nat.mem_primeFactors.mpr ⟨(q.stage i).prime, hd, Q.m_pos.ne'⟩))
  oddAdmissible := sourceFilter q unit Q.m₁.primeFactors
  oddAdmissible_iff i D hav := by
    have had : W.admissible i D = (W.prepared D ∧ stageTest q i D) :=
      congrArg (fun V : WData ℓ => V.admissible i D) hs.symm
    rw [had, hprep]
    change sourceFilter q unit Q.m₁.primeFactors i D ↔
      (positivePrepared unit D ∧ ∀ p ∈ W.S, ¬ (p : ℤ) ∣ D) ∧ stageTest q i D
    constructor
    · rintro ⟨⟨hunit, _⟩, htest⟩
      exact ⟨⟨hunit, fun p hp => hav p hp (hprime p hp)⟩, htest⟩
    · rintro ⟨⟨hunit, hS⟩, htest⟩
      exact ⟨⟨hunit, fun p hp => hS p (hfixed hp)⟩, htest⟩ }

/-- The label's moving prime and the precision in the skeleton are those of
the chosen member of the sequence. -/
theorem labelsAtStages_prime_precision (hs : withStages W q W.prepared = W)
    (havoid : Q.m.primeFactors ⊆ S)
    (hfixed : Q.m₁.primeFactors ⊆ W.S)
    (hprime : ∀ p ∈ W.S, p.Prime)
    (hprep : W.prepared = fun D => positivePrepared unit D ∧ ∀ p ∈ W.S, ¬ (p : ℤ) ∣ D) (i : ℕ) :
    (labelsAtStages Q q unit hs havoid hfixed hprime hprep).ℓ₀ i = (q.stage i).p ∧
      W.Mθ i = cw + 1 + i :=
  ⟨rfl, congrArg (fun V : WData ℓ => V.Mθ i) hs.symm⟩

/-- The source and the valuation use the same full predicate, even before
restricting to squarefree tested products. Here the Fourier support may
include fixed sieve primes in addition to the primes of the original order. -/
theorem sourceFilter_eq (i : ℕ) {support : Finset ℕ}
    (hsupport : support = insert (q.stage i).p Q.m₁.primeFactors) :
    sourceFilter q unit support i = sourceFilter q unit Q.m₁.primeFactors i := by
  subst support
  funext D
  apply propext
  constructor
  · rintro ⟨⟨hunit, hs⟩, ht⟩
    exact ⟨⟨hunit, fun p hp => hs p (Finset.mem_insert_of_mem hp)⟩, ht⟩
  · rintro ⟨⟨hunit, hs⟩, ht⟩
    refine ⟨⟨hunit, fun p hp => ?_⟩, ht⟩
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact stageTest_not_dvd q ht
    · exact hs p hp

/-- The (O.12) mod-four lemma can be used at every prime outside the actual
Fourier support: all the primes over 6ℓ are in the fixed part of that support. -/
theorem bad_mem_support (i : ℕ) {support : Finset ℕ}
    (hsupport : support = insert (q.stage i).p Q.m₁.primeFactors)
    (p : ℕ) (hp : p.Prime) (hd : (p : ℤ) ∣ 6 * (ℓ : ℤ)) : p ∈ support := by
  rw [hsupport]
  apply Finset.mem_insert_of_mem
  exact Nat.mem_primeFactors.mpr ⟨hp, Q.bad₁ p hp (by exact_mod_cast hd), Q.m₁_pos.ne'⟩

/-- Every prime excluded by the Fourier source divides the selected odd type
conductor. Additional exclusions elsewhere in the address are irrelevant. -/
theorem support_dvd_type (i : ℕ) {support : Finset ℕ}
    (hsupport : support = insert (q.stage i).p Q.m₁.primeFactors)
    (p : ℕ) (hp : p ∈ support) : p ∣ Q.m₁ * (q.stage i).p := by
  rw [hsupport, Finset.mem_insert] at hp
  rcases hp with rfl | hp
  · exact dvd_mul_left _ _
  · exact (Nat.dvd_of_mem_primeFactors hp).mul_right _

/-- The local interface itself covers the original primes of the theta
construction, even before comparing with the stationary type modulus. -/
theorem pmLocal_base_support {O : Type} [CommRing O] {a b : ℚ} {R : Eichler.Order a b}
    {M N ell : ℕ} (F : PMLocal O R M N ell) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ 2 * F.m * N * ell) : p ∈ F.support := by
  by_contra hn
  rw [mul_assoc (2 * F.m) N ell] at hd
  rcases hp.dvd_mul.mp hd with h | h
  · rcases hp.dvd_mul.mp h with h2 | hm
    · exact F.neTwo p hp hn ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · exact F.goodM p hp hn hm
  · exact F.away p hp hn h

/-- The address reading, before any later label exclusions, is literally the
valuation reading on the full Fourier source filter. -/
theorem rodd_atStage (hs : withStages W q W.prepared = W)
    (havoid : Q.m.primeFactors ⊆ S)
    (hfixed : Q.m₁.primeFactors ⊆ W.S)
    (hprime : ∀ p ∈ W.S, p.Prime)
    (hprep : W.prepared = fun D => positivePrepared unit D ∧ ∀ p ∈ W.S, ¬ (p : ℤ) ∣ D) (i : ℕ) {support V : Finset ℕ}
    (hsupport : support = insert (q.stage i).p Q.m₁.primeFactors)
    (hV : ∀ p ∈ V, p.Prime) :
    Rodd W (labelsAtStages Q q unit hs havoid hfixed hprime hprep) i V =
      intrinsic (W.aθ i) W.δo (fun n => sourceFilter q unit support i n) V := by
  rw [sourceFilter_eq Q q unit i hsupport]
  exact rodd_eq_intrinsic _ hV

/-- A bound on output cardinalities fixes an operator budget, and two extra
bits suffice for the second division. This holds before choosing the stage. -/
theorem reading_budget (B : ℕ) : B ≤ (B - 1) + 1 ∧ 2 ≤ (2 : ℕ) := by
  omega

#print axioms sourceFilter
#print axioms stageTest_not_dvd
#print axioms labelsAtStages
#print axioms labelsAtStages_prime_precision
#print axioms sourceFilter_eq
#print axioms bad_mem_support
#print axioms support_dvd_type
#print axioms pmLocal_base_support
#print axioms rodd_atStage
#print axioms reading_budget

end ZInQ.Manuscript.RC.StageIdent
