import ZInQKernel.Contrib.OneProof.RC.ModelLevels.UniversalDivisibility
import ZInQKernel.Contrib.OneProof.RC.ModelLevels.Clopen
import Mathlib.NumberTheory.Divisors

/-! # The exact-order locus in the affine torsion -/

namespace WeierstrassCurve.ModelLevels

open ModelTorsion

variable {A : Type*} [CommRing A] (W : WeierstrassCurve A) [W.IsElliptic]
variable {N : ℕ} (hN : IsUnit (N : A))

private theorem divisor_kernel_idempotent {d : ℕ} (hdN : d ∣ N) :
    ∃ e : AffineTorsionAlgebra W N, IsIdempotentElem e ∧
      RingHom.ker (restrictAffineTorsion W hN hdN) = Ideal.span {e} := by
  have hd : IsUnit (d : A) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hdN) hN
  haveI := (affineTorsionAlgebra_finite_etale W hN).2.2
  haveI := (affineTorsionAlgebra_finite_etale W hd).2.2
  exact exists_idempotent_ker _ (restrictAffineTorsion_surjective W hN hdN)

/-- The idempotent that is zero on the divisor-level closed subscheme and one
on its complement. -/
noncomputable def divisorIdempotent {d : ℕ} (hdN : d ∣ N) : AffineTorsionAlgebra W N :=
  Classical.choose (divisor_kernel_idempotent W hN hdN)

theorem divisorIdempotent_spec {d : ℕ} (hdN : d ∣ N) :
    IsIdempotentElem (divisorIdempotent W hN hdN) ∧
      RingHom.ker (restrictAffineTorsion W hN hdN) = Ideal.span {divisorIdempotent W hN hdN} :=
  Classical.choose_spec (divisor_kernel_idempotent W hN hdN)

/-- The product of the complement idempotents cuts out the intersection of
all complements of the proper divisor levels. -/
noncomputable def exactOrderIdempotent : AffineTorsionAlgebra W N :=
  ∏ d ∈ N.properDivisors.attach, divisorIdempotent W hN (Nat.mem_properDivisors.mp d.2).1

theorem exactOrderIdempotent_idempotent : IsIdempotentElem (exactOrderIdempotent W hN) := by
  classical
  unfold exactOrderIdempotent
  let D := {d // d ∈ N.properDivisors}
  let e : D → AffineTorsionAlgebra W N :=
    fun d => divisorIdempotent W hN (Nat.mem_properDivisors.mp d.2).1
  change IsIdempotentElem (∏ d ∈ N.properDivisors.attach, e d)
  have h (s : Finset D) : IsIdempotentElem (∏ d ∈ s, e d) := by
    induction s using Finset.induction_on with
    | empty => simpa using (IsIdempotentElem.one : IsIdempotentElem (1 : AffineTorsionAlgebra W N))
    | insert d s hd ih =>
      rw [Finset.prod_insert hd]
      exact (divisorIdempotent_spec W hN (Nat.mem_properDivisors.mp d.2).1).1.mul ih
  exact h _

/-- For level one the identity section is the exact-order locus. For all other
invertible levels the locus is the complement of the proper divisor levels
inside the affine torsion. -/
noncomputable def ExactOrderAlgebra : Type _ :=
  if N = 1 then A else ClopenFactor (exactOrderIdempotent W hN)

noncomputable instance : CommRing (ExactOrderAlgebra W hN) := by
  obtain _ | _ | N := N
  · exact inferInstanceAs (CommRing (ClopenFactor (exactOrderIdempotent W hN)))
  · exact inferInstanceAs (CommRing A)
  · exact inferInstanceAs (CommRing (ClopenFactor (exactOrderIdempotent W hN)))

noncomputable instance : Algebra A (ExactOrderAlgebra W hN) := by
  obtain _ | _ | N := N
  · exact inferInstanceAs (Algebra A (ClopenFactor (exactOrderIdempotent W hN)))
  · exact inferInstanceAs (Algebra A A)
  · exact inferInstanceAs (Algebra A (ClopenFactor (exactOrderIdempotent W hN)))

/-- The exact-order cover is finite étale over the elliptic coefficient ring
for every invertible level, including level one. -/
theorem exactOrderAlgebra_finite_etale :
    Module.Finite A (ExactOrderAlgebra W hN) ∧ Algebra.Etale A (ExactOrderAlgebra W hN) := by
  have hComplement : Module.Finite A (ClopenFactor (exactOrderIdempotent W hN)) ∧
      Algebra.Etale A (ClopenFactor (exactOrderIdempotent W hN)) := by
    haveI := (affineTorsionAlgebra_finite_etale W hN).1
    haveI := (affineTorsionAlgebra_finite_etale W hN).2.2
    exact ⟨(clopenFactor_finite_etale (A := A) (exactOrderIdempotent_idempotent W hN)).1,
      (clopenFactor_finite_etale (A := A) (exactOrderIdempotent_idempotent W hN)).2.1⟩
  obtain _ | _ | N := N
  · exact hComplement
  · exact (show Module.Finite A A ∧ Algebra.Etale A A from ⟨inferInstance, inferInstance⟩)
  · exact hComplement

/-- A field point of nonidentity torsion lies in the product idempotent's
support precisely when it factors through none of the proper divisor levels. -/
theorem exactOrderIdempotent_eval_ne_zero_iff {k : Type*} [Field k] [Algebra A k]
    (x : AffineTorsionAlgebra W N →ₐ[A] k) :
    x (exactOrderIdempotent W hN) ≠ 0 ↔
      ∀ (d : ℕ) (hd : d ∣ N), d < N →
        ¬ ∃ y : AffineTorsionAlgebra W d →ₐ[A] k, y.comp (restrictAffineTorsion W hN hd) = x := by
  classical
  rw [exactOrderIdempotent, map_prod, Finset.prod_ne_zero_iff]
  constructor
  · intro hx d hd hlt
    let i : {d // d ∈ N.properDivisors} := ⟨d, Nat.mem_properDivisors.mpr ⟨hd, hlt⟩⟩
    rw [factorsThrough_iff_idempotent_vanishes _ (restrictAffineTorsion_surjective W hN hd)
      x (divisorIdempotent_spec W hN hd).2]
    exact hx i (Finset.mem_attach _ _)
  · intro hx d _
    have h := Nat.mem_properDivisors.mp d.2
    specialize hx d h.1 h.2
    rwa [factorsThrough_iff_idempotent_vanishes _ (restrictAffineTorsion_surjective W hN h.1)
      x (divisorIdempotent_spec W hN h.1).2] at hx

#print axioms divisor_kernel_idempotent
#print axioms divisorIdempotent_spec
#print axioms exactOrderIdempotent_idempotent
#print axioms exactOrderAlgebra_finite_etale
#print axioms exactOrderIdempotent_eval_ne_zero_iff

end WeierstrassCurve.ModelLevels
