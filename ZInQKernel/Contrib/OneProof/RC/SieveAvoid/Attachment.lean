import ZInQKernel.Contrib.OneProof.RC.SieveAvoid.Levels
import ZInQKernel.Contrib.OneProof.RC.O12Formwise.Eisenstein
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! The good attachment on the active coordinates of a form. The new input
only concerns primes omitted by the common-level tests (tex 9647–9654,
9745–9750, 9762–9797). -/

noncomputable section

namespace ZInQ.Manuscript.RC.SieveAvoid

open O12Formwise ThetaCoeff AddressGenuine PrintsArith TraceLimits
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {I K O G L : Type} [Fintype I] [Field K] [TopologicalSpace K] [CommRing O] [IsDomain O]
  [CharZero O] [Algebra O K] [Group G] [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {avoid Scoeff : Finset ℕ} {frob : ℕ → GalQ}
variable {M W R : ℕ} {S : AppF.ThetaStage (Odd.StageRing O M)} {δ : ℤ} {adm : ℕ → Prop}
variable {P : Window T.Good S W} {A : Basis I K G (Test T avoid)}
variable {E : Lift S} {D : Divisions E δ W R adm} {C : DiamondCharacters O G E.η}
variable {V : Blocks (P := P) A E D C} {N : BlockLevels' Scoeff V} {ρ₀ : Attachment (frob := frob) A}

/-- Retain the good-prime data at the level of the individual coordinate.
The ambient `Attachment` already gives them at primes outside `avoid`.
The cusp comparison uses the same good Carayol polynomial; the assertions
that it applies to this lower level on the same representation, and that
the original Eisenstein pair is the indicated cyclotomic pair, are
realization comparisons. No new print is invoked. -/
structure AtLevel' (N : BlockLevels' Scoeff V) (ρ₀ : Attachment (frob := frob) A) : Prop where
  cusp_unramified : ∀ i a χ hz hr, A.base i = .cusp a χ hz hr →
    ∀ q, T.Good q → q ∉ Scoeff → q ∈ avoid → q.Coprime (N.level i) →
      ∀ Q : Ideal Zbar, Q.IsMaximal → ((q : ℤ) : Zbar) ∈ Q →
        ∀ σ ∈ Q.inertia GalQ, ρ₀.ρ i σ = 1
  cusp_polynomial : ∀ i a χ hz hr, A.base i = .cusp a χ hz hr →
    ∀ q, T.Good q → q ∉ Scoeff → q ∈ avoid → q.Coprime (N.level i) →
      (((ρ₀.ρ i (frob q) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace = a q) ∧
      (((ρ₀.ρ i (frob q) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = (q : K) * χ q)
  cusp_recursion : ∀ i a χ hz hr, A.base i = .cusp a χ hz hr →
    ∀ q, T.Good q → q ∉ Scoeff → q ∈ avoid → q.Coprime (N.level i) → GoodRec a (a q) (χ q) q
  eis_pair : ∀ i α β, A.base i = .eis α β →
    ∃ Eχ : EisensteinCharacters α β (N.level i), ∀ g,
      ((ρ₀.ρ i g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        Matrix.diagonal ![(Eχ.first g : K), (Eχ.second g : K)]

variable (H : AtLevel' N ρ₀)
include H

/-- Trace and determinant on a good coordinate, expressed in terms of its
underlying newform or Eisenstein source. The Eisenstein trace uses the
proved divisor sum at a prime. -/
theorem good_values {i : I} {q : ℕ} (hq : T.Good q) (hqs : q ∉ Scoeff) (hc : q.Coprime (N.level i))
    (hf : IsFrobAt (frob q) q) :
    (((ρ₀.ρ i (frob q) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace = (A.base i).a q) ∧
    (((ρ₀.ρ i (frob q) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det =
      (q : K) * (A.base i).χ q) := by
  by_cases ha : q ∈ avoid
  · cases e : A.base i with
    | cusp a χ hz hr => exact H.cusp_polynomial i a χ hz hr e q hq hqs ha hc
    | eis α β =>
      obtain ⟨Eχ, hdiag⟩ := H.eis_pair i α β e
      obtain ⟨h₁, h₂⟩ := Eχ.frob_values hq.1 hq.ne_two hc hf
      rw [hdiag]
      simp [h₁, h₂, EigenSource.a, EigenSource.χ, eisenstein_at_prime α β hq.1, mul_left_comm]
  · have ht := ρ₀.good i ⟨q, hq, ha⟩
    rwa [A.χ_good] at ht

/-- The characteristic polynomial at a good prime of an active coordinate. -/
theorem seed_good_polynomial {U : Finset ℕ} {q : ℕ} (hq : T.Good q) (hqa : q ∉ Scoeff ∪ U)
    {i : I} (hi : V.seed U i ≠ 0) (hf : IsFrobAt (frob q) q) :
    (((ρ₀.ρ i (frob q) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).charpoly =
      Polynomial.X ^ 2 - Polynomial.C ((A.base i).a q) * Polynomial.X +
        Polynomial.C ((q : K) * (A.base i).χ q) := by
  obtain ⟨ht, hd⟩ := good_values H hq (fun h => hqa (Finset.mem_union_left _ h))
    (seed_level_coprime N hq hqa hi) hf
  rw [Matrix.charpoly_fin_two, ht, hd]

/-- The precise inertia comparison used for `windowModel`'s `hseed`.
The prime is outside the coefficient support and the entire root. -/
theorem seed_unramified {U : Finset ℕ} {q : ℕ} (hq : T.Good q) (hqa : q ∉ Scoeff ∪ U)
    {Q : Ideal Zbar} (hQ : Q.IsMaximal) (hqQ : ((q : ℤ) : Zbar) ∈ Q)
    {σ : GalQ} (hσ : σ ∈ Q.inertia GalQ) {U₀ : Finset ℕ} (hU₀ : U₀ ⊆ U)
    {i : I} (hi : V.seed U₀ i ≠ 0) : ρ₀.ρ i σ = 1 := by
  have hqs : q ∉ Scoeff := fun h => hqa (Finset.mem_union_left _ h)
  by_cases ha : q ∈ avoid
  · have hc := seed_level_coprime N hq
      (fun h => hqa (Finset.union_subset_union_right (s := Scoeff) hU₀ h)) hi
    cases e : A.base i with
    | cusp a χ hz hr => exact H.cusp_unramified i a χ hz hr e q hq hqs ha hc Q hQ hqQ σ hσ
    | eis α β =>
      obtain ⟨Eχ, hdiag⟩ := H.eis_pair i α β e
      obtain ⟨h₁, h₂⟩ := Eχ.inertia_values hq.1 hq.ne_two hc hQ hqQ hσ
      apply Units.ext
      rw [hdiag, h₁, h₂, Units.val_one]
      ext a b
      fin_cases a <;> fin_cases b <;> simp
  · exact ρ₀.unramified q hq ha Q hQ hqQ σ hσ i

/-- The good scalar recursion on the basis vector of an active coordinate,
including its old multiplicity label. -/
theorem seed_good_recursion {U : Finset ℕ} {q : ℕ} (hq : T.Good q) (hqa : q ∉ Scoeff ∪ U)
    {i : I} (hi : V.seed U i ≠ 0) :
    GoodRec (Odd.divCoeff (A.base i).a (A.degree i)) ((A.base i).a q) ((A.base i).χ q) q := by
  have hqs : q ∉ Scoeff := fun h => hqa (Finset.mem_union_left _ h)
  have hc := seed_level_coprime N hq hqa hi
  have h : GoodRec (A.base i).a ((A.base i).a q) ((A.base i).χ q) q := by
    by_cases ha : q ∈ avoid
    · cases e : A.base i with
      | cusp a χ hz hr => exact H.cusp_recursion i a χ hz hr e q hq hqs ha hc
      | eis α β =>
        change GoodRec (eisenstein α β) (eisenstein α β q) (α q * β q) q
        rw [eisenstein_at_prime α β hq.1]
        exact eisenstein_rec α β hq.1
    · exact (A.base i).goodRec (Q := Test T avoid) ⟨hq, ha⟩ hq.1
  exact h.degeneracy hq.1.pos (A.degree_pos i) (hc.of_dvd_right (N.degree_dvd i)).symm

#print axioms good_values
#print axioms seed_good_polynomial
#print axioms seed_unramified
#print axioms seed_good_recursion

end ZInQ.Manuscript.RC.SieveAvoid
