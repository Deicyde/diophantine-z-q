import ZInQKernel.Contrib.OneProof.RC.ModelLevels.ExactOrder
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Smooth.Flat

/-! # Field tests for the exact-order coordinate construction -/

namespace WeierstrassCurve.ModelLevels

open scoped TensorProduct

universe u

variable {A : Type*} {S : Type u} [CommRing A] [CommRing S] [Algebra A S]

/-- To establish that a scalar-multiplication denominator is a unit, it
suffices to check that it is nonzero under all field-valued algebra maps. -/
theorem isUnit_of_nonzero_at_fields {s : S}
    (h : ∀ (k : Type u) [Field k] [Algebra A k], ∀ f : S →ₐ[A] k, f s ≠ 0) :
    IsUnit s := by
  by_contra hs
  obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal (Ideal.span {s})
    (Ideal.span_singleton_eq_top.not.mpr hs)
  let : m.IsMaximal := hm
  let : Field (S ⧸ m) := Ideal.Quotient.field m
  exact h (S ⧸ m) (Ideal.Quotient.mkₐ A m)
    (Ideal.Quotient.eq_zero_iff_mem.mpr (hsm (Ideal.subset_span (Set.mem_singleton s))))

/-- Over a reduced ring, polynomial identities can be verified at
field-valued points. Prime residues suffice for this test. -/
theorem eq_of_eq_at_fields [IsReduced S] {s t : S}
    (h : ∀ (k : Type u) [Field k] [Algebra A k], ∀ f : S →ₐ[A] k, f s = f t) :
    s = t := by
  rw [← sub_eq_zero]
  have hn : s - t ∈ nilradical S := by
    rw [nilradical_eq_sInf, Ideal.mem_sInf]
    intro p hp
    let : p.IsPrime := hp
    let k := FractionRing (S ⧸ p)
    let f : S →ₐ[A] k := (IsScalarTower.toAlgHom A (S ⧸ p) k).comp (Ideal.Quotient.mkₐ A p)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (IsFractionRing.injective (S ⧸ p) k)
    change f (s - t) = algebraMap (S ⧸ p) k 0
    rw [map_zero, map_sub, h k f, sub_self]
  simpa only [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot] using hn

/-- Over a domain the exact-order algebra embeds into its generic fibre.
That fibre is étale over a field and therefore reduced. -/
theorem exactOrderAlgebra_isReduced [IsDomain A] (W : WeierstrassCurve A) [W.IsElliptic]
    {N : ℕ} (hN : IsUnit (N : A)) : IsReduced (ExactOrderAlgebra W hN) := by
  let S := ExactOrderAlgebra W hN
  let k := FractionRing A
  let : Algebra.Etale A S := (exactOrderAlgebra_finite_etale W hN).2
  let : Algebra.Etale k (k ⊗[A] S) := inferInstance
  let : IsReduced (k ⊗[A] S) := Algebra.FormallyUnramified.isReduced_of_field k _
  exact isReduced_of_injective (Algebra.TensorProduct.includeRight (R := A) (A := k) (B := S))
    (Module.Flat.tensorProduct_mk_injective (R := A) (M := S) (S := k))

#print axioms isUnit_of_nonzero_at_fields
#print axioms eq_of_eq_at_fields
#print axioms exactOrderAlgebra_isReduced

end WeierstrassCurve.ModelLevels
