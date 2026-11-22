import ZInQKernel.Contrib.CloudR2CM.SerreTate.FiniteInertiaStatements
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.GroupTheory.Index

/-!
# Rationalization of the actual CM order

The finite additive index and integer denominator clearing show that the
original order spans its number field. Its rational tensor algebra is
identified with the whole field, without excluding conductor primes.
The original base-field endomorphism ring is not replaced or given a new
ring structure.
-/

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj TensorProduct

namespace HDec.CMSerreTate.P1

/-- The actual order inclusion respects the canonical integer algebra. -/
def orderIntAlgHom {k : Type} [Field k] [NumberField k] (R : Subring k) : R →ₐ[ℤ] k :=
  { R.subtype with
    commutes' := fun n => by
      change R.subtype (n : R) = (n : k)
      exact map_intCast R.subtype n }

/-- The rational order map is scalar extension of its actual inclusion. -/
def rationalOrderMap {k : Type} [Field k] [NumberField k] (R : Subring k) :
    ℚ ⊗[ℤ] R →ₐ[ℚ] k :=
  (AlgHom.liftEquiv ℤ ℚ R k) (orderIntAlgHom R)

theorem rationalOrderMap_tmul {k : Type} [Field k] [NumberField k]
    (R : Subring k) (q : ℚ) (r : R) :
    rationalOrderMap R (q ⊗ₜ[ℤ] r) = q • (r : k) := rfl

/-- The rational map retains every order element: its injectivity follows
on the whole localization, not only on pure tensors. -/
theorem rationalOrderMap_injective {k : Type} [Field k] [NumberField k]
    (R : Subring k) : Function.Injective (rationalOrderMap R) := by
  let j : R →ₗ[ℤ] ℚ ⊗[ℤ] R := TensorProduct.mk ℤ ℚ R 1
  haveI : IsLocalizedModule (nonZeroDivisors ℤ) j := by
    change IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ R 1)
    infer_instance
  apply IsLocalizedModule.injective_of_map_zero (S := nonZeroDivisors ℤ) j
    (g := (rationalOrderMap R).toLinearMap.restrictScalars ℤ)
  intro r hr
  have hr' : (r : k) = 0 := by
    change rationalOrderMap R (TensorProduct.mk ℤ ℚ R 1 r) = 0 at hr
    rw [TensorProduct.mk_apply, rationalOrderMap_tmul, one_smul] at hr
    exact hr
  have hr0 : r = 0 := Subtype.ext hr'
  simp only [hr0, map_zero]

/-- Finite additive index gives surjectivity after integer denominator
clearing. No inverse of the conductor in the integral order is assumed. -/
theorem rationalOrderMap_surjective {k : Type} [Field k] [NumberField k]
    (R : Subring k) (hR : HDec.CMBranch.IsImagQuadOrder k R) :
    Function.Surjective (rationalOrderMap R) := by
  intro x
  have hxQ : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have hxZ : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ k).mpr hxQ
  obtain ⟨d, hd, hInt⟩ := hxZ.exists_integral_multiple
  have hy : d • x ∈ (integralClosure ℤ k).toSubring :=
    (mem_integralClosure_iff ℤ k).mpr hInt
  have hIndex : R.toAddSubgroup.relIndex
      (integralClosure ℤ k).toSubring.toAddSubgroup ≠ 0 := hR.2.2.2
  obtain ⟨n, hn, _, hnr⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero
    (H := R.toAddSubgroup) (K := (integralClosure ℤ k).toSubring.toAddSubgroup) hIndex hy
  let m : ℤ := (n : ℤ) * d
  have hm : m ≠ 0 := mul_ne_zero (by exact_mod_cast hn.ne') hd
  have hnr' := hnr.1
  change n • (d • x) ∈ R at hnr'
  have hmx : m • x ∈ R := by
    simpa only [m, mul_smul, natCast_zsmul] using hnr'
  let r : R := ⟨m • x, hmx⟩
  have hmk : (m : k) ≠ 0 := Int.cast_ne_zero.mpr hm
  refine ⟨(m : ℚ)⁻¹ ⊗ₜ[ℤ] r, ?_⟩
  rw [rationalOrderMap_tmul]
  change (m : ℚ)⁻¹ • (m • x) = x
  rw [Algebra.smul_def, zsmul_eq_mul, map_inv₀, map_intCast, inv_mul_cancel_left₀ hmk]

/-- The full rationalization of the actual order is its number field. -/
def rationalOrderEquiv {k : Type} [Field k] [NumberField k]
    (R : Subring k) (hR : HDec.CMBranch.IsImagQuadOrder k R) : ℚ ⊗[ℤ] R ≃ₐ[ℚ] k :=
  AlgEquiv.ofBijective (rationalOrderMap R)
    ⟨rationalOrderMap_injective R, rationalOrderMap_surjective R hR⟩

/-- The actual base-field End-ring identification is an integer-algebra
identification with the same order. -/
def endOrderIntAlgEquiv {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    {k : Type} [Field k] [NumberField k] (R : Subring k)
    (e : _root_.PkgI3.AbVar.End A ≃+* R) : _root_.PkgI3.AbVar.End A ≃ₐ[ℤ] R :=
  { e with
    commutes' := fun n => by
      change e (n : _root_.PkgI3.AbVar.End A) = (n : R)
      exact map_intCast e n }

/-- The original rational End ring is identified with the whole CM field
through the actual base-End/order equivalence and order rationalization. -/
def end0OrderEquiv {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    {k : Type} [Field k] [NumberField k] (R : Subring k)
    (e : _root_.PkgI3.AbVar.End A ≃+* R) (hR : HDec.CMBranch.IsImagQuadOrder k R) :
    A.End0 ≃ₐ[ℚ] k :=
  (_root_.Algebra.TensorProduct.congr (AlgEquiv.refl : ℚ ≃ₐ[ℚ] ℚ) (endOrderIntAlgEquiv A R e)).trans
    (rationalOrderEquiv R hR)

end HDec.CMSerreTate.P1
