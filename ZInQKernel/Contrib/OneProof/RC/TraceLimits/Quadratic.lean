import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.GaloisModel
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Elementary
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.RadicalWitness
import Mathlib.Data.Nat.Factorization.Induction

/-!
# The elementary quadratic step

Tex 9745–9750. This file separates the abstract elementary quotient
argument (on-the-spot, provenance (c)) from the arithmetic identification
of its characters with radicals supported on the level.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.TraceLimits

open AddressGenuine
open ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

/-- Triviality on the generators `−1` and the primes in `S` implies
triviality on every square root of a nonzero integer supported on `S`
(tex 9748–9750). Include two in `S` for the manuscript's support. -/
theorem sqrtChar_eq_one_of_support (S : Finset ℕ) (g : GalQ)
    (hneg : sqrtChar (-1) g = 1) (hprime : ∀ p ∈ S, sqrtChar (p : ℤ) g = 1)
    (d : ℤ) (hd : ∀ p, p.Prime → p ∣ d.natAbs → p ∈ S) :
    sqrtChar d g = 1 := by
  have aux (n : ℕ) : (∀ p, p.Prime → p ∣ n → p ∈ S) → sqrtChar (n : ℤ) g = 1 := by
    induction n using Nat.recOnMul with
    | zero => simp [sqrtChar_zero]
    | one => intro _; simpa using DFunLike.congr_fun (sqrtChar_sq 1) g
    | prime p hp => exact fun h => hprime p (h p hp dvd_rfl)
    | mul a b ha hb =>
      intro h
      by_cases ha0 : a = 0
      · simp [ha0, sqrtChar_zero]
      by_cases hb0 : b = 0
      · simp [hb0, sqrtChar_zero]
      rw [Nat.cast_mul, sqrtChar_mul (by exact_mod_cast ha0) (by exact_mod_cast hb0),
        MonoidHom.mul_apply, ha (fun p hp hpa => h p hp (dvd_mul_of_dvd_left hpa _)),
        hb (fun p hp hpb => h p hp (dvd_mul_of_dvd_right hpb _)), mul_one]
  have e := aux d.natAbs hd
  cases d with
  | ofNat n => exact e
  | negSucc n =>
    change sqrtChar ((n + 1 : ℕ) : ℤ) g = 1 at e
    change sqrtChar (-((n + 1 : ℕ) : ℤ)) g = 1
    rw [← neg_one_mul, sqrtChar_mul (by decide) (by exact_mod_cast Nat.succ_ne_zero n),
      MonoidHom.mul_apply, hneg, e, mul_one]

/-- The common kernel of the radical characters for `−1` and the primes in
`S`. Each character has exponent dividing two. -/
def radicalKernel (S : Finset ℕ) : Subgroup GalQ :=
  (sqrtChar (-1)).ker ⊓ (MonoidHom.pi fun p : S => sqrtChar (p.val : ℤ)).ker

/-- The elementary quotient cut out by the listed radicals is finite
(tex 9748–9750); this does not identify it with the maximal elementary
extension with this ramification support. -/
theorem radicalKernel_finiteIndex (S : Finset ℕ) : (radicalKernel S).FiniteIndex := by
  rw [radicalKernel, ← MonoidHom.ker_prod]
  exact Subgroup.finiteIndex_ker _

/-- To identify an elementary quotient of `G_ℚ` it suffices to express the
quadratic characters trivial on `N` as the listed supported radical characters.
This is the exact arithmetic input of the implication; openness or finiteness
of `N` alone would not suffice. -/
theorem radicalKernel_le_squares_sup (N : Subgroup GalQ) (S : Finset ℕ)
    (hclass : ∀ χ : GalQ →* Multiplicative (ZMod 2), N ≤ χ.ker →
      ∃ d : ℤ, χ = sqrtChar d ∧ ∀ p, p.Prime → p ∣ d.natAbs → p ∈ S) :
    radicalKernel S ≤ Subgroup.closure (sqSet GalQ) ⊔ N := by
  intro g hg
  by_contra h
  obtain ⟨χ, hχ, hχg⟩ := exists_quadratic_separating N h
  obtain ⟨d, rfl, hd⟩ := hclass χ hχ
  exact hχg (sqrtChar_eq_one_of_support S g (MonoidHom.mem_ker.1 hg.1)
    (fun p hp => congrFun (MonoidHom.mem_ker.1 hg.2) ⟨p, hp⟩) d hd)

/-- The fixed type detects the sign and all radicals of the stationary support
(tex 2016–2029, 2162–2163; include two in `S`). -/
def TypeDetectsRadicals {L : Type*} [AddCommGroup L]
    (chiType : GalQ →* Multiplicative L) (S : Finset ℕ) : Prop :=
  ∀ g, chiType g = 1 → g ∈ radicalKernel S

/-- The precise supported-character classification needed for the elementary quotient:
a quadratic character trivial on `N` has a radicand with prime factors in `S`.
In applications one must prove this from inertia and the arithmetic of quadratic fields. -/
def SupportedQuadraticCharacters (N : Subgroup GalQ) (S : Finset ℕ) : Prop :=
  ∀ χ : GalQ →* Multiplicative (ZMod 2), N ≤ χ.ker →
    ∃ d : ℤ, χ = sqrtChar d ∧ ∀ p, p.Prime → p ∣ d.natAbs → p ∈ S

/-- When the radicand and two are units modulo a maximal ideal of `ℤ̄`,
inertia fixes its square root. This gives the easy direction of the
ramification check for the listed radical characters (tex 9748–9750). -/
theorem sqrtChar_trivial_on_inertia_of_units {d : ℤ} (hd : d ≠ 0)
    {Q : Ideal Zbar} (hQ : Q.IsMaximal) (h2 : (2 : Zbar) ∉ Q) (hdQ : (d : Zbar) ∉ Q)
    {σ : GalQ} (hσ : σ ∈ Q.inertia GalQ) : sqrtChar d σ = 1 := by
  apply (sqrtChar_eq_one_iff d hd σ).2
  rcases galQ_sqrtQbar σ d with h | h
  · exact h
  · exfalso
    let x : Zbar := ⟨sqrtQbar d, isIntegral_sqrtQbar d⟩
    have ex : -(σ • x - x) = 2 * x := by
      apply Subtype.ext
      change -(σ (sqrtQbar d) - sqrtQbar d) = 2 * sqrtQbar d
      rw [h]
      ring
    have hmul : (2 : Zbar) * x ∈ Q := ex ▸ Q.neg_mem (hσ x)
    have hx : x ∈ Q := (hQ.isPrime.mem_or_mem hmul).resolve_left h2
    have hxsq : x ^ 2 = (d : Zbar) := Subtype.ext (sqrtQbar_sq d)
    exact hdQ (hxsq ▸ Q.pow_mem_of_mem hx 2 (by decide))

/-- Inertia in the absolute integral closure lies in the subgroup away from this support. -/
def UnramifiedOutside (N : Subgroup GalQ) (S : Finset ℕ) : Prop :=
  ∀ q, q.Prime → q ∉ S → ∀ Q : Ideal Zbar, Q.IsMaximal →
    ((q : ℤ) : Zbar) ∈ Q → Q.inertia GalQ ≤ N

/-- The remaining number field comparison: an odd prime dividing a squarefree
radicand has nontrivial inertia action on its square root in `ℚ̄`. -/
def OddRadicalRamification : Prop :=
  ∀ (d : ℤ), Squarefree d → ∀ (s : Qbar), s ^ 2 = (d : Qbar) →
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ d.natAbs →
      ∃ (Q : Ideal Zbar), Q.IsMaximal ∧ ((q : ℤ) : Zbar) ∈ Q ∧
        ∃ σ ∈ Q.inertia GalQ, σ s ≠ s

/-- Absolute inertia reduces the supported classification to the odd-divisor
ramification criterion for squarefree radicands (tex 9748–9750). -/
theorem supportedQuadratic_of_inertia (N : Subgroup GalQ) (S : Finset ℕ)
    (hopen : IsOpen (N : Set GalQ)) (h2 : 2 ∈ S) (hunr : UnramifiedOutside N S)
    (hram : OddRadicalRamification) : SupportedQuadraticCharacters N S := by
  intro χ hN
  obtain ⟨d, s, hd, hs, hχ⟩ :=
    squarefree_radical_of_open_ker χ (Subgroup.isOpen_mono hN hopen)
  refine ⟨d, MonoidHom.ext fun σ => ?_, fun q hq hqd => ?_⟩
  · have e := sq_eq_sq_iff_eq_or_eq_neg.mp ((sqrtQbar_sq d).trans hs.symm)
    have hsame : σ (sqrtQbar d) = sqrtQbar d ↔ σ s = s := by
      rcases e with e | e
      · rw [e]
      · rw [e, map_neg, neg_inj]
    have h := (hχ σ).trans (hsame.symm.trans (sqrtChar_eq_one_iff d hd.ne_zero σ).symm)
    exact (show ∀ a b : Multiplicative (ZMod 2), (a = 1 ↔ b = 1) → a = b by decide) _ _ h
  · by_contra hqS
    obtain ⟨Q, hQ, hqQ, σ, hσ, hmove⟩ :=
      hram d hd s hs q hq (fun e => hqS (e ▸ h2)) hqd
    exact hmove ((hχ σ).1 (MonoidHom.mem_ker.1 (hN (hunr q hq hqS Q hQ hqQ hσ))))

/-- The tracked bit for `p` detects the radical `p` once the sign is detected,
because `sstar p = (−1) ^ (p / 2) * p` (tex 2016–2029, 9748–9750). -/
theorem sqrtChar_prime_of_bit (g : GalQ) {p : ℕ} (hp : p ≠ 0)
    (hneg : sqrtChar (-1) g = 1) (hbit : bitChar p g = 1) : sqrtChar (p : ℤ) g = 1 := by
  have hs (n : ℕ) : sqrtChar ((-1 : ℤ) ^ n) g = 1 := by
    induction n with
    | zero => simpa using DFunLike.congr_fun (sqrtChar_sq 1) g
    | succ n ih => rw [pow_succ, sqrtChar_mul (pow_ne_zero _ (by decide)) (by decide),
        MonoidHom.mul_apply, ih, hneg, mul_one]
  rwa [bitChar_apply, sstar, sqrtChar_mul (pow_ne_zero _ (by decide)) (by exact_mod_cast hp),
    MonoidHom.mul_apply, hs, one_mul] at hbit

/-- Given the supported-character classification, the fixed type and added bits
imply the conclusion of `kummer` for the subgroup in question. -/
theorem kummer_of_support {L : Type*} [AddCommGroup L]
    {chiType : GalQ →* Multiplicative L} {S U : Finset ℕ} {N : Subgroup GalQ}
    (htype : TypeDetectsRadicals chiType S)
    (hclass : SupportedQuadraticCharacters N (S ∪ U))
    (g : GalQ) (hg : chiType g = 1) (hbit : ∀ p ∈ U, bitChar p g = 1) :
    g ∈ Subgroup.closure (sqSet GalQ) ⊔ N := by
  have hS := htype g hg
  refine radicalKernel_le_squares_sup N (S ∪ U) hclass ⟨hS.1, MonoidHom.mem_ker.2 ?_⟩
  funext p
  change sqrtChar (p.val : ℤ) g = 1
  rcases Finset.mem_union.1 p.2 with hp | hp
  · exact congrFun (MonoidHom.mem_ker.1 hS.2) ⟨p, hp⟩
  · by_cases hz : p.val = 0
    · simp [hz, sqrtChar_zero]
    · exact sqrtChar_prime_of_bit _ hz (MonoidHom.mem_ker.1 hS.1) (hbit _ hp)

#print axioms sqrtChar_eq_one_of_support
#print axioms radicalKernel_finiteIndex
#print axioms radicalKernel_le_squares_sup
#print axioms sqrtChar_trivial_on_inertia_of_units
#print axioms supportedQuadratic_of_inertia
#print axioms sqrtChar_prime_of_bit
#print axioms kummer_of_support

end ZInQ.Manuscript.RC.TraceLimits
