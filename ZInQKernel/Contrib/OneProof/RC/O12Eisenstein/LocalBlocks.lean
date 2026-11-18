import ZInQKernel.Contrib.OneProof.RC.O12Eisenstein.Characters
import ZInQKernel.Contrib.OneProof.RC.O12.Fourier

/-!
# The Eisenstein part of the (O.12) local comparison

Tex 9754–9771 and 9858–9873. The actual coordinate column is identified by
its divisor-sum expansion (with its degeneracy and scaling) and its
normalized character pair. Within the selected summand the positive
coefficient shift gives the operator. The passage between a separated
summand and ambient coordinates is on-the-spot (provenance (c)).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Eisenstein

open AddressGenuine O12 PrintsArith Matrix
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {chiType : GalQ →* Multiplicative L}
variable (X : GaloisConstituentModel T R ap B chiType)
variable {p : ℕ} [hp : Fact p.Prime] (j : ℤ_[2] →+* X.K) (A : FourierData X)

/-- A single vector in the constituent coordinates. -/
def column (i : X.I) (a : X.K) : X.I → X.K := by
  classical exact Pi.single i a

/-- Identify one basis vector of the actual ramified Eisenstein space.
`split` identifies the model's abstract representation with the normalized
character sum; it places the unramified line first in the Galois basis.
`expansion` identifies the Fourier column of the same constituent. -/
structure Coordinate (i : X.I) where
  pair : CharacterPair X.K p
  degeneracy : ℕ
  degeneracy_coprime : degeneracy.Coprime p
  scale : X.K
  basis : GL (Fin 2) X.K
  split : ∀ g : GalQ, (↑(basis * X.ρ i g * basis⁻¹) : Matrix (Fin 2) (Fin 2) X.K) =
    diagonal ![(pair.unramLine j g : X.K), (pair.ramLine j g : X.K)]
  expansion : ∀ n : PosIndex, X.coefK (column X i 1) (A.index n) =
    scale * degenerate degeneracy pair.coeff n.val

variable {X j A}

/-- The common basis in the two matrix clauses of `LocalBlocks.newLine`,
with the unramified Frobenius entry equal to the divisor-sum scalar. -/
theorem Coordinate.local_matrices {i : X.I} (E : Coordinate X j A (p := p) i)
    (hp₂ : p ≠ 2) (P : LocalPair p) :
    (↑(E.basis * X.ρ i P.τ * E.basis⁻¹) : Matrix (Fin 2) (Fin 2) X.K) = diagonal ![1, -1] ∧
    (↑(E.basis * X.ρ i P.φ * E.basis⁻¹) : Matrix (Fin 2) (Fin 2) X.K) =
      diagonal ![E.pair.scalar, (E.pair.ramLine j P.φ : X.K)] := by
  have ⟨hu, hr⟩ := E.pair.inertia_lines j hp₂ P
  exact ⟨by simpa only [hu, hr] using E.split P.τ,
    by simpa only [E.pair.unramLine_frob j hp₂ P] using E.split P.φ⟩

/-- Shift identity on a column, including its degeneracy, scaling and any
choice of coordinate value. -/
theorem Coordinate.column_shift {i : X.I} (E : Coordinate X j A (p := p) i)
    (a : X.K) (n : PosIndex) :
    X.coefK (column X i (E.pair.scalar * a)) (A.index n) =
      X.coefK (column X i a) (A.index ⟨p * n.val, mul_ne_zero hp.out.ne_zero n.property⟩) := by
  classical
  have hcol (b : X.K) : column X i b = b • column X i 1 := by
    ext k
    by_cases h : k = i <;> simp [column, h, Pi.single_eq_of_ne]
  have hread (b : X.K) (m : PosIndex) :
      X.coefK (column X i b) (A.index m) =
        b * (E.scale * degenerate E.degeneracy E.pair.coeff m.val) := by
    rw [hcol b]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, E.expansion]
  simp only [hread, degenerate_mul E.degeneracy_coprime
    (fun _ hk => E.pair.coeff_mul hk) n.property]
  ring

variable (X)

/-- The coordinate projection onto the selected summand. -/
def project (S : Set X.I) : (X.I → X.K) →ₗ[X.K] (X.I → X.K) := by
  classical
  exact
    { toFun := fun v i => if i ∈ S then v i else 0
      map_add' := fun _ _ => by
        funext i
        by_cases hi : i ∈ S <;> simp [hi]
      map_smul' := fun _ _ => by
        funext i
        by_cases hi : i ∈ S <;> simp [hi] }

variable {X} {S : Set X.I} (E : ∀ i : S, Coordinate X j A (p := p) i.val)

/-- The Eisenstein contribution to the weight-two operator, extended by zero
on other coordinates. Each old degeneracy column receives the same scalar as
its underlying pair. -/
def eisensteinUp : (X.I → X.K) →ₗ[X.K] (X.I → X.K) := by
  classical
  exact
    { toFun := fun v i => if hi : i ∈ S then (E ⟨i, hi⟩).pair.scalar * v i else 0
      map_add' := fun v w => by
        funext i
        by_cases hi : i ∈ S <;> simp [hi, mul_add]
      map_smul' := fun c v => by
        funext i
        by_cases hi : i ∈ S <;> simp [hi, mul_left_comm] }

private theorem sum_columns [Fintype S] (v : X.I → X.K) (hv : ∀ i ∉ S, v i = 0) :
    (∑ i : S, column X i.val (v i.val)) = v := by
  classical
  funext k
  rw [Finset.sum_apply]
  by_cases hk : k ∈ S
  · rw [Finset.sum_eq_single (⟨k, hk⟩ : S)]
    · simp [column]
    · intro i _ hi
      exact Pi.single_eq_of_ne (fun h => hi (Subtype.ext h.symm)) _
    · simp
  · rw [hv k hk]
    apply Finset.sum_eq_zero
    intro i _
    unfold column
    apply Pi.single_eq_of_ne
    intro h
    exact hk (h.symm ▸ i.property)

/-- The explicitly assembled Eisenstein operator is the positive Fourier
shift on the entire selected summand. -/
theorem eisensteinUp_shift [Fintype S] (v : X.I → X.K) (hv : ∀ i ∉ S, v i = 0)
    (n : PosIndex) :
    X.coefK (eisensteinUp E v) (A.index n) =
      X.coefK v (A.index ⟨p * n.val, mul_ne_zero hp.out.ne_zero n.property⟩) := by
  classical
  have hw : ∀ k ∉ S, eisensteinUp E v k = 0 := fun k hk => by
    simp [eisensteinUp, hk]
  have hs (i : S) : eisensteinUp E v i.val = (E i).pair.scalar * v i.val := by
    simp [eisensteinUp, i.property]
  rw [← sum_columns (eisensteinUp E v) hw]
  conv_rhs => rw [← sum_columns v hv]
  simp only [map_sum, Finset.sum_apply, hs]
  exact Finset.sum_congr rfl fun i _ => (E i).column_shift (v i.val) n

/-- The Eisenstein part of `FourierData.UpAtOne`, for vectors supported on
the selected summand. -/
theorem eisensteinUp_atOne [Fintype S] (v : X.I → X.K) (hv : ∀ i ∉ S, v i = 0) :
    X.coefK (eisensteinUp E v) (A.index ⟨1, one_ne_zero⟩) =
      X.coefK v (A.index ⟨p, hp.out.ne_zero⟩) := by
  simpa only [mul_one] using eisensteinUp_shift E v hv ⟨1, one_ne_zero⟩

/-- Compare with the ambient operator without using `LocalBlocks.newLine`.
The projection commutes with that operator on active inputs (separation of
summands). On the selected summand the defining Fourier shift characterizes
the operator, because its positive Fourier expansion is injective there. -/
theorem project_up_eq [Fintype S] {active : Set X.I}
    (Up : (X.I → X.K) →ₗ[X.K] (X.I → X.K))
    (hproj : ∀ (v : X.I → X.K), (∀ i ∉ active, v i = 0) →
      project X S (Up v) = Up (project X S v))
    (hshift : ∀ (v : X.I → X.K), (∀ i ∉ S, v i = 0) → ∀ n : PosIndex,
      X.coefK (Up v) (A.index n) =
        X.coefK v (A.index ⟨p * n.val, mul_ne_zero hp.out.ne_zero n.property⟩))
    (hinj : ∀ (v : X.I → X.K), (∀ i ∉ S, v i = 0) →
      (∀ n : PosIndex, X.coefK v (A.index n) = 0) → v = 0)
    (v : X.I → X.K) (hv : ∀ i ∉ active, v i = 0) :
    project X S (Up v) = eisensteinUp E v := by
  classical
  have hsp : ∀ k ∉ S, project X S v k = 0 := fun k hk => by simp [project, hk]
  have he : eisensteinUp E (project X S v) = eisensteinUp E v := by
    funext k
    by_cases hk : k ∈ S <;> simp [eisensteinUp, project, hk]
  apply sub_eq_zero.mp
  apply hinj
  · intro k hk
    simp [project, eisensteinUp, hk]
  · intro n
    simp only [map_sub, Pi.sub_apply, hproj v hv, ← he,
      hshift _ hsp n, eisensteinUp_shift E _ hsp n, sub_self]


/-- Assemble the Eisenstein action with an operator on the complementary
coordinates. This constructs the required action without assuming an
ambient Fourier comparison. -/
def withEisensteinUp (other : (X.I → X.K) →ₗ[X.K] (X.I → X.K)) :
    (X.I → X.K) →ₗ[X.K] (X.I → X.K) :=
  (project X Sᶜ).comp (other.comp (project X Sᶜ)) + eisensteinUp E

theorem withEisensteinUp_project (other : (X.I → X.K) →ₗ[X.K] (X.I → X.K))
    (v : X.I → X.K) :
    project X S (withEisensteinUp E other v) = eisensteinUp E v := by
  classical
  funext k
  by_cases hk : k ∈ S <;> simp [withEisensteinUp, project, eisensteinUp, hk]

/-- The exact `LocalBlocks.newLine` conclusion on each of the selected
active ramified Eisenstein coordinates. For the assembled operator use
`withEisensteinUp_project`; for a supplied ambient operator use
`project_up_eq` to verify the projection. -/
theorem newLine {active : Set X.I}
    (Up : (X.I → X.K) →ₗ[X.K] (X.I → X.K))
    (hUp : ∀ (v : X.I → X.K), (∀ i ∉ active, v i = 0) →
      project X S (Up v) = eisensteinUp E v)
    (hp₂ : p ≠ 2) (P : LocalPair p) (i : X.I) (hi : i ∈ S) :
    ∃ (b : GL (Fin 2) X.K) (lam mu : X.K),
      (↑(b * X.ρ i P.τ * b⁻¹) : Matrix (Fin 2) (Fin 2) X.K) = diagonal ![1, -1] ∧
      (↑(b * X.ρ i P.φ * b⁻¹) : Matrix (Fin 2) (Fin 2) X.K) = diagonal ![lam, mu] ∧
      ∀ v : X.I → X.K, (∀ k ∉ active, v k = 0) → Up v i = lam * v i := by
  let e := E ⟨i, hi⟩
  obtain ⟨ht, hf⟩ := e.local_matrices hp₂ P
  refine ⟨e.basis, e.pair.scalar, (e.pair.ramLine j P.φ : X.K), ht, hf, ?_⟩
  intro v hv
  classical
  simpa [project, eisensteinUp, hi, e] using congrFun (hUp v hv) i

/-- In the `UpAtOne` equality, the projections of input and output onto this
summand give matching contributions for every active input. -/
theorem upAtOne_projected [Fintype S] {active : Set X.I}
    (Up : (X.I → X.K) →ₗ[X.K] (X.I → X.K))
    (hUp : ∀ (v : X.I → X.K), (∀ i ∉ active, v i = 0) →
      project X S (Up v) = eisensteinUp E v)
    (v : X.I → X.K) (hv : ∀ i ∉ active, v i = 0) :
    X.coefK (project X S (Up v)) (A.index ⟨1, one_ne_zero⟩) =
      X.coefK (project X S v) (A.index ⟨p, hp.out.ne_zero⟩) := by
  classical
  have he : eisensteinUp E (project X S v) = eisensteinUp E v := by
    funext k
    by_cases hk : k ∈ S <;> simp [eisensteinUp, project, hk]
  rw [hUp v hv, ← he]
  exact eisensteinUp_atOne E _ (fun k hk => by simp [project, hk])

/-- Assemble both Eisenstein comparisons for precisely the active ramified
Eisenstein coordinates. The complementary operator can be supplied
independently. -/
theorem eisenstein_branch (active ramified eisenstein : Set X.I)
    [Fintype ((active ∩ ramified) ∩ eisenstein : Set X.I)]
    (C : ∀ i : ((active ∩ ramified) ∩ eisenstein : Set X.I),
      Coordinate X j A (p := p) i.val)
    (other : (X.I → X.K) →ₗ[X.K] (X.I → X.K)) (hp₂ : p ≠ 2) (P : LocalPair p) :
    (∀ i ∈ active ∩ ramified, i ∈ eisenstein → ∃ (b : GL (Fin 2) X.K) (lam mu : X.K),
      (↑(b * X.ρ i P.τ * b⁻¹) : Matrix (Fin 2) (Fin 2) X.K) = diagonal ![1, -1] ∧
      (↑(b * X.ρ i P.φ * b⁻¹) : Matrix (Fin 2) (Fin 2) X.K) = diagonal ![lam, mu] ∧
      ∀ v : X.I → X.K, (∀ k ∉ active, v k = 0) → withEisensteinUp C other v i = lam * v i) ∧
    (∀ v : X.I → X.K, (∀ k ∉ active, v k = 0) →
      X.coefK (project X ((active ∩ ramified) ∩ eisenstein) (withEisensteinUp C other v))
        (A.index ⟨1, one_ne_zero⟩) =
      X.coefK (project X ((active ∩ ramified) ∩ eisenstein) v) (A.index ⟨p, hp.out.ne_zero⟩)) := by
  exact ⟨fun i hi hE => newLine C (withEisensteinUp C other)
      (fun v _ => withEisensteinUp_project C other v) hp₂ P i ⟨hi, hE⟩,
    upAtOne_projected C (withEisensteinUp C other)
      (fun v _ => withEisensteinUp_project C other v)⟩

#print axioms Coordinate.local_matrices
#print axioms Coordinate.column_shift
#print axioms sum_columns
#print axioms eisensteinUp_shift
#print axioms eisensteinUp_atOne
#print axioms project_up_eq
#print axioms withEisensteinUp_project
#print axioms newLine
#print axioms upAtOne_projected
#print axioms eisenstein_branch

end ZInQ.Manuscript.RC.O12Eisenstein
