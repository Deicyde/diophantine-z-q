import ZInQKernel.Contrib.OneProof.RC.O12EisConst.Galois

/-! Supply the coordinate inputs to the Eisenstein branch of (O.12).
The comparison with the complementary Fourier contribution is on-the-spot
(c), before any reduction (tex 9885–9902). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12EisConst

open AddressGenuine O12 O12Eisenstein PrintsArith Matrix
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {chiType : GalQ →* Multiplicative L} {X : GaloisConstituentModel T R ap B chiType}
variable {p : ℕ} [Fact p.Prime] {A : FourierData X}

/-- A degeneracy of a pair ramified at `p` cannot use `p` again in a
block whose level has exponent at most one at `p` (tex 9754–9759). -/
theorem degree_coprime_of_level {D : Type} [Field D] (E : CharacterPair D p)
    {d M : ℕ} (hd : d * pairLevel E ∣ M) (hM : ¬ p * p ∣ M) : d.Coprime p := by
  refine ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr fun h => hM ?_).symm
  have hE : p ∣ pairLevel E :=
    (dvd_mul_right p E.awayLevel).trans (dvd_mul_right _ E.unramLevel)
  exact (mul_dvd_mul h hE).trans hd

section Realization

variable [TopologicalSpace X.K]

/-- Data for one actual ramified Eisenstein coordinate, at a fixed target
level `N` (tex 9649–9654, 9754–9771, 9862–9864). The old copy is built
using the analytic degeneracy of the primitive series, at an index prime
to the operator prime. Its Galois input consists of test-prime data and
semisimplicity. -/
structure RealizedCoordinate (D : Type) [Field D] (c : D →+* ℂ) (k : D →+* X.K)
    (N : ℕ) (avoid : Finset ℕ) (i : X.I) where
  pair : CharacterPair D p
  primitiveForm : BaseForm pair c
  degree : ℕ
  degree_pos : 0 < degree
  blockLevel : ℕ
  divides_block : degree * pairLevel pair ∣ blockLevel
  block_exponent_le_one : ¬ p * p ∣ blockLevel
  block_dvd : blockLevel ∣ N
  scale : D
  scale_ne_zero : scale ≠ 0
  column : letI : NeZero degree := ⟨degree_pos.ne'⟩
    ColumnRealization primitiveForm k (divides_block.trans block_dvd) scale A i
  attachment : RepInput (X := X) (mapPair pair k) i avoid

variable [CharZero X.K] [IsTopologicalRing X.K] [T2Space X.K]
variable {D : Type} [Field D] {c : D →+* ℂ} {k : D →+* X.K} {N : ℕ} {avoid : Finset ℕ}
variable (j : ℤ_[2] →+* X.K) (hj : Continuous j) (hp₂ : p ≠ 2) (P : LocalPair p)

/-- The two identifications required in `O12Eisenstein.Coordinate` follow
from the analytic column realization and the good-prime attachment. -/
def RealizedCoordinate.toCoordinate {i : X.I}
    (C : RealizedCoordinate (p := p) (A := A) D c k N avoid i) : Coordinate X j A (p := p) i := by
  letI : NeZero C.degree := ⟨C.degree_pos.ne'⟩
  let h := C.attachment.split j hj hp₂ P
  exact {
    pair := mapPair C.pair k
    degeneracy := C.degree
    degeneracy_coprime := degree_coprime_of_level C.pair C.divides_block C.block_exponent_le_one
    scale := k C.scale
    basis := Classical.choose h
    split := Classical.choose_spec h
    expansion := C.column.expansion C.primitiveForm k (C.divides_block.trans C.block_dvd) C.scale }

/-- The identification family for the intersection in `eisenstein_branch`. -/
def coordinates (active ramified eisenstein : Set X.I)
    (C : ∀ i : ((active ∩ ramified) ∩ eisenstein : Set X.I),
      RealizedCoordinate (p := p) (A := A) D c k N avoid i.val) :
    ∀ i : ((active ∩ ramified) ∩ eisenstein : Set X.I), Coordinate X j A (p := p) i.val :=
  fun i => (C i).toCoordinate j hj hp₂ P

/-- Feed the actual coordinate identifications to the existing branch. The
result is the local matrix and scalar clause and the projected Fourier
identity on active inputs, for any complementary action. -/
theorem realized_branch (active ramified eisenstein : Set X.I)
    [Finite X.I]
    (C : ∀ i : ((active ∩ ramified) ∩ eisenstein : Set X.I),
      RealizedCoordinate (p := p) (A := A) D c k N avoid i.val)
    (other : (X.I → X.K) →ₗ[X.K] (X.I → X.K)) :
    let S := (active ∩ ramified) ∩ eisenstein
    let Up := withEisensteinUp (coordinates j hj hp₂ P active ramified eisenstein C) other
    (∀ i ∈ active ∩ ramified, i ∈ eisenstein → ∃ (b : GL (Fin 2) X.K) (lam mu : X.K),
      (↑(b * X.ρ i P.τ * b⁻¹) : Matrix (Fin 2) (Fin 2) X.K) = diagonal ![1, -1] ∧
      (↑(b * X.ρ i P.φ * b⁻¹) : Matrix (Fin 2) (Fin 2) X.K) = diagonal ![lam, mu] ∧
      ∀ v : X.I → X.K, (∀ k ∉ active, v k = 0) → Up v i = lam * v i) ∧
    (∀ v : X.I → X.K, (∀ k ∉ active, v k = 0) →
      X.coefK (project X S (Up v)) (A.index ⟨1, one_ne_zero⟩) =
      X.coefK (project X S v) (A.index ⟨p, (Fact.out : p.Prime).ne_zero⟩)) := by
  classical
  let : Fintype ((active ∩ ramified) ∩ eisenstein : Set X.I) := Fintype.ofFinite _
  exact eisenstein_branch active ramified eisenstein
    (coordinates j hj hp₂ P active ramified eisenstein C) other hp₂ P

end Realization

section Complement

variable {j : ℤ_[2] →+* X.K} {S active : Set X.I}
variable (C : ∀ i : S, Coordinate X j A (p := p) i.val)
variable (other : (X.I → X.K) →ₗ[X.K] (X.I → X.K))

/-- The complementary coordinates of the assembled operator see precisely the
complementary input and output. In particular they retain the whole chosen
operator on that space, including any non-scalar old multiplicity action. -/
theorem withEisensteinUp_complement (v : X.I → X.K) :
    project X Sᶜ (withEisensteinUp C other v) = project X Sᶜ (other (project X Sᶜ v)) := by
  classical
  funext i
  by_cases hi : i ∈ S <;> simp [withEisensteinUp, project, eisensteinUp, hi]

private theorem project_add_complement (v : X.I → X.K) :
    project X S v + project X Sᶜ v = v := by
  classical
  funext i
  by_cases hi : i ∈ S <;> simp [project, hi]

/-- An already assembled ambient operator agrees on active inputs if it
separates the Eisenstein summand and acts there by the defining shift.
This uses positive coefficient injectivity only on that summand. -/
theorem withEisensteinUp_eq_ambient [Fintype S]
    (hproj : ∀ (v : X.I → X.K), (∀ i ∉ active, v i = 0) →
      project X S (other v) = other (project X S v))
    (hshift : ∀ (v : X.I → X.K), (∀ i ∉ S, v i = 0) → ∀ n : PosIndex,
      X.coefK (other v) (A.index n) =
        X.coefK v (A.index ⟨p * n.val, mul_ne_zero (Fact.out : p.Prime).ne_zero n.property⟩))
    (hinj : ∀ (v : X.I → X.K), (∀ i ∉ S, v i = 0) →
      (∀ n : PosIndex, X.coefK v (A.index n) = 0) → v = 0)
    (v : X.I → X.K) (hv : ∀ i ∉ active, v i = 0) :
    withEisensteinUp C other v = other v := by
  have hE := project_up_eq C other hproj hshift hinj v hv
  rw [← project_add_complement (S := S) (withEisensteinUp C other v),
    withEisensteinUp_project, withEisensteinUp_complement, ← hE]
  have hC : project X Sᶜ (other (project X Sᶜ v)) = project X Sᶜ (other v) := by
    conv_rhs => rw [← project_add_complement (S := S) v, map_add, map_add, ← hproj v hv]
    classical
    suffices hzero : project X Sᶜ (project X S (other v)) = 0 by rw [hzero, zero_add]
    funext i
    by_cases hi : i ∈ S <;> simp [project, hi]
  rw [hC, project_add_complement]

/-- The full Fourier comparison at one is equivalent to the complementary
comparison once the Eisenstein action is assembled. -/
theorem withEisensteinUp_atOne_iff [Fintype S] (v : X.I → X.K) :
    (X.coefK (withEisensteinUp C other v) (A.index ⟨1, one_ne_zero⟩) =
      X.coefK v (A.index ⟨p, (Fact.out : p.Prime).ne_zero⟩)) ↔
    (X.coefK (project X Sᶜ (other (project X Sᶜ v))) (A.index ⟨1, one_ne_zero⟩) =
      X.coefK (project X Sᶜ v) (A.index ⟨p, (Fact.out : p.Prime).ne_zero⟩)) := by
  have h := upAtOne_projected (active := Set.univ) C (withEisensteinUp C other)
    (fun w _ => withEisensteinUp_project C other w) v (by simp)
  conv_lhs =>
    lhs
    rw [← project_add_complement (S := S) (withEisensteinUp C other v),
      withEisensteinUp_complement, map_add, Pi.add_apply, h]
  conv_lhs =>
    rhs
    rw [← project_add_complement (S := S) v, map_add, Pi.add_apply]
  exact add_left_cancel_iff

end Complement

#print axioms degree_coprime_of_level
#print axioms realized_branch
#print axioms withEisensteinUp_complement
#print axioms project_add_complement
#print axioms withEisensteinUp_eq_ambient
#print axioms withEisensteinUp_atOne_iff

end ZInQ.Manuscript.RC.O12EisConst
