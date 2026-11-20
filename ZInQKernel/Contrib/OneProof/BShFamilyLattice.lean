import ZInQKernel.Contrib.OneProof.BShTracesPrimeLattice
import ZInQKernel.Contrib.OneProof.BShTracesTorsion
import ZInQKernel.Contrib.OneProof.BShFamilySections

/-! ON THE SPOT (provenance (c)): the coset enumerations give a finite atlas of
nonzero prime torsion x-coordinates, including the horizontal line. -/

noncomputable section

namespace BShFamily

open UpperHalfPlane PeriodPair T5Glue BShTraces AfTateLam

/-- The prime superlattice specified by a direction. -/
def enlarged {p : ℕ} (hp : 0 < p) (i : Line p) (τ : ℍ) : PeriodPair :=
  i.elim (horizontal p hp τ) (fun j => pp (shiftDiv p j τ))

/-- A finite enumeration of the cosets of the original lattice. -/
def cosets {p : ℕ} (hp : 0 < p) (i : Line p) (τ : ℍ) :
    CosetEnumeration (pp τ) (enlarged hp i τ) (Fin p) :=
  match i with
  | none => horizontalCosets p hp τ
  | some j => triangularCosets p hp j τ

theorem representative_eq {p : ℕ} (hp : 0 < p) (i : Line p) (τ : ℍ) (k : Fin p) :
    (cosets hp i τ).representative k = -(k.val : ℂ) * generator p i τ := by
  cases i with
  | none => simp [cosets, horizontalCosets, generator, div_eq_mul_inv]
  | some j =>
    simp [cosets, triangularCosets, generator, HeckePin.coe_shiftDiv _ _ hp]

/-- The displayed sections represent nonzero classes. -/
theorem multiple_notMem {p : ℕ} (hp : 0 < p) (i : Line p) (τ : ℍ) (k : Multiple p) :
    (k.val.val : ℂ) * generator p i τ ∉ (pp τ).lattice := by
  letI : NeZero p := ⟨hp.ne'⟩
  have h₀ : (cosets hp i τ).representative 0 = 0 := by rw [representative_eq]; simp
  intro h
  apply representative_notMem (cosets hp i τ) 0 h₀
    (fun e => k.property (congrArg Fin.val e))
  simpa only [representative_eq, neg_mul] using (pp τ).lattice.neg_mem h

/-- Multiplying any of the displayed sections by the prime gives an
original period. -/
theorem multiple_killed {p : ℕ} (hp : 0 < p) (i : Line p) (τ : ℍ) (k : Fin p) :
    (p : ℂ) * ((k.val : ℂ) * generator p i τ) ∈ (pp τ).lattice := by
  have hn : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  cases i with
  | none =>
    refine PeriodPair.mem_lattice.mpr ⟨k.val, 0, ?_⟩
    simp [pp, generator]
    field_simp
  | some j =>
    refine PeriodPair.mem_lattice.mpr ⟨(k.val : ℤ) * j.val, k.val, ?_⟩
    simp [pp, generator]
    field_simp
    <;> ring

/-- Every nonzero class killed by the prime has one of the displayed
x-coordinates. -/
theorem exists_normX_of_torsion {p : ℕ} (hp : p.Prime) (τ : ℍ) {z : ℂ}
    (hz : z ∉ (pp τ).lattice) (hn : (p : ℂ) * z ∈ (pp τ).lattice) :
    ∃ (i : Line p) (k : Multiple p), normX τ z =
      normX τ ((k.val.val : ℂ) * generator p i τ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, hi, _⟩ := prime_torsion_lattice_unique hp τ z hz hn
  change z ∈ (enlarged hp.pos i τ).lattice at hi
  let D := cosets hp.pos i τ
  obtain ⟨⟨k,l⟩, e⟩ := D.equiv.surjective ⟨z, hi⟩
  have he : (l : ℂ) - D.representative k = z := by
    rw [← D.coe_equiv]
    exact congrArg Subtype.val e
  rw [representative_eq, neg_mul, sub_neg_eq_add, add_comm] at he
  have hk : k ≠ 0 := by
    rintro rfl
    apply hz
    have he' : (l : ℂ) = z := by simpa using he
    exact he' ▸ l.property
  have hk' : k.val ≠ 0 := fun e => hk (Fin.ext e)
  refine ⟨i, ⟨k, hk'⟩, ?_⟩
  rw [← he]
  exact normX_period τ _ l

open WeierstrassCurve X1Igusa.Weber in
/-- At every generic complex parameter the finite atlas is exactly the root
set of the normalized division polynomial. -/
theorem eval_division_eq_zero_iff {p : ℕ} (hp : p.Prime) (τ : ℍ)
    (h₂ : (pp τ).g₂ ≠ 0) (h₃ : (pp τ).g₃ ≠ 0) (x : ℂ) :
    ((curveG ((pp τ).g₂ ^ 3 / (pp τ).g₃ ^ 2)).ΨSq p).eval x = 0 ↔
      ∃ (i : Line p) (k : Multiple p), x =
        normX τ ((k.val.val : ℂ) * generator p i τ) := by
  have h := normalized_torsion_roots (pp τ) (discNeZero_pp τ) h₂ h₃ p x
  dsimp only at h
  rw [h]
  constructor
  · rintro ⟨z, hz, hn, rfl⟩
    exact exists_normX_of_torsion hp τ hz hn
  · rintro ⟨i, k, rfl⟩
    exact ⟨_, multiple_notMem hp.pos i τ k, multiple_killed hp.pos i τ k.val, rfl⟩

#print axioms representative_eq
#print axioms multiple_notMem
#print axioms multiple_killed
#print axioms exists_normX_of_torsion
#print axioms eval_division_eq_zero_iff

end BShFamily
