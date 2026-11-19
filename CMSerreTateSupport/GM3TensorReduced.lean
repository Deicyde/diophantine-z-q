/-
Lane5 GM3 commutative-algebra proof for the exact algebraically-closed field
interface, universe u, SOURCE ONLY / UNCOMPILED.

Truth pre-check: reduced finite-type k-algebras remain reduced after EVERY
field extension when k is algebraically closed (EGA IV 4.6.1). We do not
use the weaker Algebra.IsGeometricallyReduced definition which Mathlib's
Nilpotent/GeometricallyReduced file explicitly says lacks the all-field
bridge. Instead actual k-algebra maps to k separate elements by Jacobson
and the Nullstellensatz. A basis of the extension field detects each tensor
coefficient after those actual scalar evaluations; nilpotence makes every
such evaluation zero in a field. No finite-extension or characteristic case
is dropped, and no finite-dimensionality of the extension is assumed.
-/
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option autoImplicit false
noncomputable section
universe u

open scoped TensorProduct

namespace H5OriginalDVR.Lane5.GM3Algebra

/-- Jacobson/Nullstellensatz separation by ACTUAL algebra maps to k. -/
theorem eq_zero_of_all_algHom_zero
    {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [_root_.IsReduced A]
    (a : A) (ha : ∀ phi : A →ₐ[k] k, phi a = 0) : a = 0 := by
  letI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  have hrad : a ∈ (⊥ : Ideal A).radical := by
    rw [Ideal.radical_eq_jacobson, Ideal.jacobson, Ideal.mem_sInf]
    intro m hm
    letI : m.IsMaximal := hm.2
    letI : Field (A ⧸ m) := Ideal.Quotient.field m
    letI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
    have hIntegral : (algebraMap k (A ⧸ m)).IsIntegral :=
      Algebra.isIntegral_def.mp (inferInstance : Algebra.IsIntegral k (A ⧸ m))
    let e : k ≃ₐ[k] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m))
      (IsAlgClosed.ringHom_bijective_of_isIntegral _ hIntegral)
    let phi : A →ₐ[k] k := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m)
    have hq : Ideal.Quotient.mk m a = 0 := by
      apply e.symm.injective
      simpa [phi] using ha phi
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  obtain ⟨n, hn⟩ := hrad
  exact (show IsNilpotent a from ⟨n, Ideal.mem_bot.mp hn⟩).eq_zero

/-- Actual scalar evaluation of a tensor using an original k-algebra point. -/
def tensorEvaluation
    {k L A : Type u} [Field k] [Field L] [CommRing A] [Algebra k L] [Algebra k A]
    (phi : A →ₐ[k] k) : L ⊗[k] A →ₐ[k] L :=
  Algebra.TensorProduct.lift (AlgHom.id k L) ((Algebra.ofId k L).comp phi)
    (fun _ _ => Commute.all _ _)

@[simp]
theorem tensorEvaluation_tmul
    {k L A : Type u} [Field k] [Field L] [CommRing A] [Algebra k L] [Algebra k A]
    (phi : A →ₐ[k] k) (l : L) (a : A) :
    tensorEvaluation phi (l ⊗ₜ[k] a) = phi a • l := by
  simp [tensorEvaluation, Algebra.smul_def, mul_comm]

/-- The coordinate of the evaluated tensor is the evaluation of its actual
A-valued coefficient. Only a vector-space basis, not a dimension invariant. -/
theorem evaluate_coefficient
    {k L A : Type u} [Field k] [Field L] [CommRing A] [Algebra k L] [Algebra k A]
    {I : Type u} [DecidableEq I] (b : Module.Basis I k L) (phi : A →ₐ[k] k)
    (x : L ⊗[k] A) (i : I) :
    phi (TensorProduct.equivFinsuppOfBasisLeft b x i) =
      b.repr (tensorEvaluation phi x) i := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
      simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
        tensorEvaluation_tmul, mul_comm]
  | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply]
      rw [hx, hy]

/-- EVERY field base change of this reduced finite-type algebra is reduced.
No algebraicity/finite-dimensionality/noetherianity of L is an extra premise. -/
theorem isReduced_field_tensor
    {k L A : Type u} [Field k] [IsAlgClosed k] [Field L]
    [CommRing A] [Algebra k L] [Algebra k A]
    [Algebra.FiniteType k A] [_root_.IsReduced A] : _root_.IsReduced (L ⊗[k] A) := by
  classical
  let b := Module.Basis.ofVectorSpace k L
  let c := TensorProduct.equivFinsuppOfBasisLeft b (N := A)
  constructor
  intro x hx
  apply c.injective
  apply Finsupp.ext
  intro i
  have hi : c x i = 0 := by
    apply eq_zero_of_all_algHom_zero (k := k)
    intro phi
    have hEval : tensorEvaluation phi x = 0 :=
      (hx.map (tensorEvaluation phi).toRingHom).eq_zero
    rw [evaluate_coefficient b phi x i, hEval]
    simp
  simpa only [map_zero, Finsupp.zero_apply] using hi

/-- The opposite tensor ordering is carried by the actual algebra symmetry. -/
theorem isReduced_tensor_field
    {k L A : Type u} [Field k] [IsAlgClosed k] [Field L]
    [CommRing A] [Algebra k L] [Algebra k A]
    [Algebra.FiniteType k A] [_root_.IsReduced A] : _root_.IsReduced (A ⊗[k] L) := by
  letI : _root_.IsReduced (L ⊗[k] A) := isReduced_field_tensor
  exact isReduced_of_injective (Algebra.TensorProduct.comm k A L).toRingHom
    (Algebra.TensorProduct.comm k A L).injective

end H5OriginalDVR.Lane5.GM3Algebra
