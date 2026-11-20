import ZInQKernel.Contrib.OneProof.RC.O12EisConst.Galois
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! The good Euler polynomial and Fourier Hecke recursion of the split
weight-two pair (tex 9660–9668, 9762–9769, 9862–9864 and 10358–10360).
The coefficient and inertia calculations are on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EisForm

open AddressGenuine O12 O12EisConst O12Eisenstein PrintsArith TraceLimits Matrix
open Filter Topology UpperHalfPlane
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime]

private def natChar {m : ℕ} (χ : DirichletCharacter K m) : ℕ →* K :=
  χ.toMonoidHom.comp (Nat.castRingHom (ZMod m)).toMonoidHom

private theorem divisorCoeff_eq_eisenstein {m₁ m₂ : ℕ}
    (a : DirichletCharacter K m₁) (b : DirichletCharacter K m₂) (n : ℕ) :
    divisorCoeff a b n = ThetaCoeff.eisenstein (natChar a) (natChar b) n := by
  unfold divisorCoeff ThetaCoeff.eisenstein
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  have hx₁ := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
  change _ = (if x.1 = 0 then 0 else natChar a x.1) * ((x.2 : K) * natChar b x.2)
  simp only [hx₁.ne', ite_false]
  change a (x.1 : ZMod m₁) * (b (x.2 : ZMod m₂) * (x.2 : K)) =
    a (x.1 : ZMod m₁) * ((x.2 : K) * b (x.2 : ZMod m₂))
  rw [mul_comm (x.2 : K)]

/-- The two scalar entries of the good Hecke recursion are exactly those
of the primitive pair. The sequence is extended by zero at index zero. -/
theorem pair_goodRec (E : CharacterPair K p) {q : ℕ} (hq : q.Prime) :
    ThetaCoeff.GoodRec E.coeff (E.coeff q) (E.unram q * E.ramified q) q := by
  cases h : E.twistUnramified
  · have he : E.coeff = ⇑(ThetaCoeff.eisenstein (natChar E.unram) (natChar E.ramified)) :=
      funext fun n => by
        simpa only [CharacterPair.coeff, h, Bool.false_eq_true, ite_false] using
          divisorCoeff_eq_eisenstein E.unram E.ramified n
    rw [he, ThetaCoeff.eisenstein_at_prime _ _ hq]
    exact ThetaCoeff.eisenstein_rec _ _ hq
  · have he : E.coeff = ⇑(ThetaCoeff.eisenstein (natChar E.ramified) (natChar E.unram)) :=
      funext fun n => by
        simpa only [CharacterPair.coeff, h, ite_true] using
          divisorCoeff_eq_eisenstein E.ramified E.unram n
    rw [he, ThetaCoeff.eisenstein_at_prime _ _ hq, mul_comm (E.unram q)]
    exact ThetaCoeff.eisenstein_rec _ _ hq

/-- At a prime away from the degeneracy degree, the old vector has the
primitive eigensystem regardless of its coefficient at that prime. -/
theorem old_goodRec (E : CharacterPair K p) {q d : ℕ} (hq : q.Prime)
    (hd : 0 < d) (hqd : d.Coprime q) :
    ThetaCoeff.GoodRec (degenerate d E.coeff) (E.coeff q) (E.unram q * E.ramified q) q := by
  exact (pair_goodRec E hq).degeneracy hq.pos hd hqd

private theorem weightTwist_eq_one_of_inertia (j : ℤ_[2] →+* K)
    {q : ℕ} (hq : q.Prime) (hq₂ : q ≠ 2) {Q : Ideal Zbar} (hQ : Q.IsMaximal)
    (hqQ : ((q : ℤ) : Zbar) ∈ Q) {g : GalQ} (hg : g ∈ Q.inertia GalQ) :
    (weightTwist j g : K) = 1 := by
  have hc : q.Coprime 2 :=
    hq.coprime_iff_not_dvd.mpr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).not.mpr hq₂)
  have h : (cyclotomicCharacter Qbar 2 g.toRingEquiv).val = 1 := by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    rw [cyclotomicCharacter.toZModPow, map_one]
    change (cycChar (2 ^ n) g : ZMod (2 ^ n)) = 1
    rw [cycChar_eq_one_of_mem_inertia hq (hc.pow_right n) hQ hqQ hg, Units.val_one]
  change j (cyclotomicCharacter Qbar 2 g.toRingEquiv).val = 1
  rw [h, map_one]

/-- Triviality on all inertia groups at an odd prime away from both conductors. -/
theorem normalizedRep_unramified (E : CharacterPair K p) (j : ℤ_[2] →+* K)
    {q : ℕ} (hq : q.Prime) (hq₂ : q ≠ 2)
    (hu : q.Coprime E.unramLevel) (hr : q.Coprime (p * E.awayLevel))
    {Q : Ideal Zbar} (hQ : Q.IsMaximal) (hqQ : ((q : ℤ) : Zbar) ∈ Q)
    {g : GalQ} (hg : g ∈ Q.inertia GalQ) : normalizedRep E j g = 1 := by
  have huu : dirichletGalois E.unram g = 1 := by
    simp [dirichletGalois, cycChar_eq_one_of_mem_inertia hq hu hQ hqQ hg]
  have hrr : dirichletGalois E.ramified g = 1 := by
    simp [dirichletGalois, cycChar_eq_one_of_mem_inertia hq hr hQ hqQ hg]
  have ht : weightTwist j g = 1 := Units.ext (weightTwist_eq_one_of_inertia j hq hq₂ hQ hqQ hg)
  apply Units.ext
  rw [normalizedRep_matrix]
  change _ = (1 : Matrix (Fin 2) (Fin 2) K)
  rw [← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> cases he : E.twistUnramified <;>
    simp [CharacterPair.ramLine, CharacterPair.unramLine, he, huu, hrr, ht]

/-- At arithmetic Frobenius the characteristic polynomial and the Fourier
recursion use the same primitive eigensystem, before any old degeneracy. -/
theorem normalizedRep_goodAttachment (E : CharacterPair K p) (j : ℤ_[2] →+* K)
    {q : ℕ} {g : GalQ} (hq : q.Prime) (hq₂ : q ≠ 2) (hu : q.Coprime E.unramLevel)
    (hr : q.Coprime (p * E.awayLevel)) (hg : IsFrobAt g q) :
    (↑(normalizedRep E j g) : Matrix (Fin 2) (Fin 2) K).charpoly =
      Polynomial.X ^ 2 - Polynomial.C (E.coeff q) * Polynomial.X +
        Polynomial.C ((q : K) * (E.unram q * E.ramified q)) ∧
    ThetaCoeff.GoodRec E.coeff (↑(normalizedRep E j g) : Matrix (Fin 2) (Fin 2) K).trace
      (E.unram q * E.ramified q) q := by
  obtain ⟨ht, hd⟩ := normalizedRep_good E j hq hq₂ hu hr hg
  exact ⟨by rw [Matrix.charpoly_fin_two, ht, hd], by rw [ht]; exact pair_goodRec E hq⟩

/-- At a good test prime the analytic primitive coefficient and the
Frobenius trace are images of the same algebraic coefficient. -/
theorem baseForm_good_trace {D : Type*} [Field D] {E : CharacterPair D p} {c : D →+* ℂ}
    (F : BaseForm E c) (k : D →+* K) (j : ℤ_[2] →+* K)
    {q : ℕ} {g : GalQ} (hq : q.Prime) (hq₂ : q ≠ 2) (hu : q.Coprime E.unramLevel)
    (hr : q.Coprime (p * E.awayLevel)) (hg : IsFrobAt g q) :
    (qExpansion 1 F.form).coeff q = c (E.coeff q) ∧
      (↑(normalizedRep (mapPair E k) j g) : Matrix (Fin 2) (Fin 2) K).trace =
        k (E.coeff q) := by
  exact ⟨F.positive_expansion ⟨q, hq.ne_zero⟩,
    (normalizedRep_good (mapPair E k) j hq hq₂ hu hr hg).1.trans (mapPair_coeff E k q)⟩

private theorem continuous_finiteChar {m : ℕ} [NeZero m] [TopologicalSpace K]
    [IsTopologicalRing K] (χ : DirichletCharacter K m) :
    Continuous fun g : GalQ => (dirichletGalois χ g : K) := by
  let f := (Units.coeHom K).comp (dirichletGalois χ)
  apply continuous_of_continuousAt_one f
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar m
  let M := IntermediateField.adjoin ℚ ({ζ} : Set Qbar)
  have hf : ∀ᶠ g : GalQ in nhds 1, g ∈ M.fixingSubgroup :=
    (IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _)
  apply tendsto_const_nhds.congr'
  filter_upwards [hf] with g hg
  rw [IntermediateField.mem_fixingSubgroup_iff] at hg
  have he := (cycChar_spec m g ζ hζ.pow_eq_one).symm.trans
    ((hg ζ (IntermediateField.mem_adjoin_simple_self ℚ ζ)).trans
      (cycChar_spec m (1 : GalQ) ζ hζ.pow_eq_one))
  have hc : cycChar m g = cycChar m 1 := Units.ext (ZMod.val_injective m
    (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) he))
  simp [f, dirichletGalois, hc]

theorem continuous_splitTrace [TopologicalSpace K] [IsTopologicalRing K]
    (E : CharacterPair K p) (j : ℤ_[2] →+* K) (hj : Continuous j) :
    Continuous fun g => (↑(normalizedRep E j g) : Matrix (Fin 2) (Fin 2) K).trace := by
  have ht : Continuous fun g : GalQ => (weightTwist j g : K) :=
    hj.comp (Units.continuous_val.comp (cyclotomicCharacter.continuous 2 ℚ Qbar))
  have hu := continuous_finiteChar E.unram
  have hr := continuous_finiteChar E.ramified
  cases he : E.twistUnramified
  · have h : Continuous fun g =>
        (dirichletGalois E.unram g : K) +
          (dirichletGalois E.ramified g : K) * (weightTwist j g : K) := hu.add (hr.mul ht)
    simpa [normalizedRep_matrix, CharacterPair.unramLine, CharacterPair.ramLine, he,
      Fin.sum_univ_two] using h
  · have h : Continuous fun g =>
        (dirichletGalois E.unram g : K) * (weightTwist j g : K) +
          (dirichletGalois E.ramified g : K) := (hu.mul ht).add hr
    simpa [normalizedRep_matrix, CharacterPair.unramLine, CharacterPair.ramLine, he,
      Fin.sum_univ_two] using h

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {chiType : GalQ →* Multiplicative L} {X : GaloisConstituentModel T R ap B chiType}

/-- If the constituent realization chooses the explicit character sum in the
model, its attachment data are automatic for any finite exclusion that
contains the primes of the pair level. This permits a common exclusion set
for a family of labeled columns. -/
theorem repInput_of_split_choice [CharZero X.K] [TopologicalSpace X.K] [IsTopologicalRing X.K]
    (E : CharacterPair X.K p) (j : ℤ_[2] →+* X.K) (hj : Continuous j) (hp₂ : p ≠ 2)
    (P : LocalPair p) (i : X.I) (hρ : X.ρ i = normalizedRep E j)
    (avoid : Finset ℕ) (havoid : (pairLevel E).primeFactors ⊆ avoid) :
    RepInput (X := X) E i avoid := by
  have hn : pairLevel E ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne E.awayLevel))
      (NeZero.ne E.unramLevel)
  have tests (q : ℕ) (hq : T.Good q) (ha : q ∉ avoid) :
      q.Coprime E.unramLevel ∧ q.Coprime (p * E.awayLevel) := by
    have hm : ¬ q ∣ pairLevel E := fun h => ha (havoid (Nat.mem_primeFactors.mpr ⟨hq.1, h, hn⟩))
    exact ⟨hq.1.coprime_iff_not_dvd.mpr (fun h => hm (h.trans (dvd_mul_left _ _))),
      hq.1.coprime_iff_not_dvd.mpr (fun h => hm (h.trans (dvd_mul_right _ _)))⟩
  refine ⟨hρ.symm ▸ normalizedRep_semisimple E j hp₂ P,
    hρ.symm ▸ continuous_splitTrace E j hj, ?_, ?_⟩
  · intro q hq ha Q hQ hqQ σ hσ
    rw [hρ]
    obtain ⟨hu, hr⟩ := tests q hq ha
    exact normalizedRep_unramified E j hq.1 hq.ne_two hu hr hQ hqQ hσ
  · intro q hq ha
    rw [hρ]
    obtain ⟨hu, hr⟩ := tests q hq ha
    exact (normalizedRep_good E j hq.1 hq.ne_two hu hr (X.frob_spec q hq)).1


end ZInQ.Manuscript.RC.EisForm
