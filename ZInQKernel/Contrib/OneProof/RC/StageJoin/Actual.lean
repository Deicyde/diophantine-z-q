import ZInQKernel.Contrib.OneProof.RC.StageJoin.Sieve
import ZInQKernel.Contrib.OneProof.RC.StageIdent.Apply

/-! The actual theta stage and integral lift, on the same geometry and detector
as (O.4), with the exact late sieve applied. The order carries its existing level. -/

noncomputable section

open scoped Classical WeierstrassCurve

namespace ZInQ.Manuscript.RC.StageJoin

open Eichler O12StageVal ThetaCoeff ZInQ.Manuscript.RC.Odd Wiring WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53

/-- The coefficient support used by the actual sieved stage (tex 9471–9483). -/
def Scoeff {O : Type} [CommRing O] {a b : ℚ} {R : Order a b} {M N ell : ℕ}
    (F : PMLocal O R M N ell) (B : LateSieve) : Finset ℕ :=
  F.support ∪ B.primes

variable {O : Type} [CommRing O] {a b : ℚ} {R : Order a b}
variable {M N ell : ℕ} [Fact ell.Prime]
variable {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K] [IsSepClosed K]
variable {Ebar : WeierstrassCurve (ZMod ell)} [Ebar.IsElliptic] {ap : ℕ → ℤ}
variable (G : PM.Geometry K R N Ebar ap) (d : PM.Evaluation K Ebar M) (L : ℕ)
variable (F : PMLocal O R M N ell) (B : LateSieve)

/-- The stage after exactly the sieves indexed by `B`. -/
def pmSievedStage : AppF.ThetaStage (StageRing O M) :=
  sieveStage (pmStage G d L F) B

/-- Retain the exact operation list with the actual source. -/
def pmSievedSource (u : ClassSet R → ℤ) (hu : PM.IsLift G d L u) :
    SievedSource (pmStage G d L F) :=
  ⟨B, pmLift G d L F u hu⟩

/-- Its integral lift on the very same ideal classes and integral detector lifts. -/
def pmSievedLift (u : ClassSet R → ℤ) (hu : PM.IsLift G d L u) :
    Lift (pmSievedStage G d L F B) :=
  (pmSievedSource G d L F B u hu).lift

/-- The underlying stage is good at every prime outside the enlarged support. -/
theorem pmStage_good_outside {p : ℕ} (hp : p.Prime) (h : p ∉ Scoeff F B) :
    (pmStage G d L F).Good p :=
  ⟨hp, fun hF => h (Finset.mem_union_left _ hF)⟩

/-- The sieved stage has precisely the good-prime domain of the full support. -/
theorem pmSievedStage_good_iff {p : ℕ} :
    (pmSievedStage G d L F B).Good p ↔ p.Prime ∧ p ∉ Scoeff F B := by
  change (p.Prime ∧ p ∉ F.support) ∧ p ∉ B.primes ↔ _
  simp only [Scoeff, Finset.mem_union, not_or, and_assoc]

/-- Primes outside the full support feed the unchanged Brandt and lift interfaces. -/
theorem pmSievedStage_good {p : ℕ} (hp : p.Prime) (h : p ∉ Scoeff F B) :
    (pmSievedStage G d L F B).Good p :=
  (pmSievedStage_good_iff G d L F B).2 ⟨hp, h⟩

omit [Fact ell.Prime] in
private theorem pmLocal_m_ne_zero : F.m ≠ 0 := by
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (F.support.sup id + 1)
  have hout : p ∉ F.support := by
    intro h
    exact Nat.not_succ_le_self _ (hle.trans (Finset.le_sup (f := id) h))
  intro hm
  exact F.goodM p hp hout (hm ▸ dvd_zero p)

/-- The stage coefficients are the actual zero-or-retain Fourier coefficients. -/
theorem pmSievedStage_aθ (n : ℕ) :
    (pmSievedStage G d L F B).aθ n = if B.Keep n then (pmStage G d L F).aθ n else 0 :=
  sieveStage_aθ _ B (pmLocal_m_ne_zero F) n

/-- The same test is imposed integrally, before stage reduction. -/
theorem pmSievedLift_aθ (u : ClassSet R → ℤ) (hu : PM.IsLift G d L u) (n : ℕ) :
    (pmSievedLift G d L F B u hu).aθ n =
      if B.Keep n then (pmLift G d L F u hu).aθ n else 0 :=
  sieveLift_aθ B _ (pmLocal_m_ne_zero F) n

/-- Given the original local vanishing, the new lift supplies the support clause
of `Divisions`, including every actual late sieve. -/
theorem pmSievedLift_support (u : ClassSet R → ℤ) (hu : PM.IsLift G d L u)
    (hlocal : ∀ p ∈ F.support, p.Prime → ∀ n, p ∣ n →
      (pmLift G d L F u hu).aθ n = 0)
    {p : ℕ} (hp : p.Prime) (hbad : ¬ (pmSievedStage G d L F B).Good p)
    {n : ℕ} (hn : p ∣ n) : (pmSievedLift G d L F B u hu).aθ n = 0 := by
  have hmem : p ∈ Scoeff F B := by
    by_contra h
    exact hbad (pmSievedStage_good G d L F B hp h)
  rw [pmSievedLift_aθ]
  rcases Finset.mem_union.mp hmem with hF | hB
  · simp [hlocal p hF hp n hn]
  · exact ite_eq_right fun h => h p hB hn

/-- The stage and lift both use the same class set of the level order.
The Eichler level is certified by the underlying geometry. -/
theorem pmSieved_parameters (u : ClassSet R → ℤ) (hu : PM.IsLift G d L u) :
    IsEichler (pmSievedStage G d L F B).ℓ₀ N R ∧
    (pmSievedStage G d L F B).X = ClassSet R ∧
    (pmSievedLift G d L F B u hu).geom.X = ClassSet R :=
  ⟨G.eichler, rfl, rfl⟩

variable {ℓ : ℕ}
  (G₀ : PM.Geometry K R (CST.newformLevel ((EcurveZ ℓ)⁄ℚ)) Ebar ap)
  (F₀ : PMLocal O R M (CST.newformLevel ((EcurveZ ℓ)⁄ℚ)) ell)

/-- The same order in the selected stage and lift has the newform level of the
skeleton curve, by the existing level identification. No level field is added. -/
theorem pmSieved_newformLevel (u : ClassSet R → ℤ) (hu : PM.IsLift G₀ d L u) :
    IsEichler (pmSievedStage G₀ d L F₀ B).ℓ₀ (CST.newformLevel (Ecurve ℓ)) R ∧
    (pmSievedStage G₀ d L F₀ B).X = ClassSet R ∧
    (pmSievedLift G₀ d L F₀ B u hu).geom.X = ClassSet R := by
  obtain ⟨h, hS, hE⟩ := pmSieved_parameters G₀ d L F₀ B u hu
  exact ⟨StageIdent.level_eq ℓ ▸ h, hS, hE⟩

#print axioms pmSievedStage
#print axioms pmSievedSource
#print axioms pmSievedLift
#print axioms pmStage_good_outside
#print axioms pmSievedStage_good_iff
#print axioms pmSievedStage_good
#print axioms pmLocal_m_ne_zero
#print axioms pmSievedStage_aθ
#print axioms pmSievedLift_aθ
#print axioms pmSievedLift_support
#print axioms pmSieved_parameters
#print axioms pmSieved_newformLevel

end ZInQ.Manuscript.RC.StageJoin
