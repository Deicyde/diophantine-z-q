import ZInQKernel.Contrib.OneProof.CMBranch
import TauCeti.NumberTheory.NumberField.Global.Orders.Discriminant
import Mathlib.LinearAlgebra.Unimodular
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.PicardGroup

/-!
# Discriminants of imaginary quadratic orders

The order construction adapts `GR512Bridge.toOrder` without importing that module. The basis
and trace arguments adapt commit `a7a10d135` and use the vendored discriminant/index theorem.
-/

namespace HDec.CMBranch.FowlerBridges

open NumberField Module TauCeti.GlobalNumberFields
open scoped nonZeroDivisors

private def intSubalgebra {k : Type} [Field k] (R : Subring k) : Subalgebra ℤ k :=
  { R.toSubsemiring with algebraMap_mem' := fun n => by simpa using intCast_mem R n }

/-- View the kernel's finite-index subring as an order. The additive index kills the quotient
of the maximal order by the subring, so the subring spans the field over ℚ. -/
def toOrder {k : Type} [Field k] [NumberField k] (R : Subring k)
    (hR : IsImagQuadOrder k R) : NumberFieldOrder k where
  toSubalgebra := intSubalgebra R
  finite := by
    have h : intSubalgebra R ≤ integralClosure ℤ k := fun x hx => hR.2.2.1 hx
    have : Module.Finite ℤ (integralClosure ℤ k) := inferInstanceAs (Module.Finite ℤ (𝓞 k))
    exact Module.Finite.of_injective (Subalgebra.inclusion h).toLinearMap
      (Subalgebra.inclusion_injective h)
  spans := by
    apply top_unique
    rw [← (maximalNumberFieldOrder k).spans]
    apply Submodule.span_le.mpr
    intro y hy
    let f := LeafQM.AV.conductor R
    have hf : (f : k) ≠ 0 := by exact_mod_cast hR.2.2.2
    have hy' : y ∈ (integralClosure ℤ k).toSubring.toAddSubgroup := hy
    have hm : f • y ∈ intSubalgebra R := R.toAddSubgroup.nsmul_relIndex_mem hy'
    have he : y = (f : ℚ)⁻¹ • (f • y) := by
      rw [Algebra.smul_def, nsmul_eq_mul, ← mul_assoc, map_inv₀, map_natCast,
        inv_mul_cancel₀ hf, one_mul]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

/-- A finite-index imaginary quadratic order has a two-element integral basis.
The existing order construction gives a finite free integer module; localizing its basis
in the ambient field shows that its rank is two. -/
theorem exists_intBasis_of_isImagQuadOrder {k : Type} [Field k] [NumberField k]
    (R : Subring k) (hR : IsImagQuadOrder k R) : Nonempty (Basis (Fin 2) ℤ R) := by
  classical
  let O := toOrder R hR
  let b := Module.Free.chooseBasis ℤ O.toSubalgebra
  let bQ := b.localizationLocalization ℚ ℤ⁰ k
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ O.toSubalgebra) =
      Fintype.card (Fin 2) := by
    rw [← Module.finrank_eq_card_basis bQ, hR.2.1, Fintype.card_fin]
  exact ⟨b.reindex (Fintype.equivOfCardEq hcard)⟩

/-- The index used by the existing order construction is exactly the relative additive
index defining `LeafQM.AV.conductor`, not the conductor ideal. -/
theorem toOrder_index_eq_conductor {k : Type} [Field k] [NumberField k]
    (R : Subring k) (hR : IsImagQuadOrder k R) :
    (toOrder R hR).index = LeafQM.AV.conductor R := by
  rw [NumberFieldOrder.index_eq_addSubgroup_index]
  change (R.toAddSubgroup.comap (algebraMap (𝓞 k) k).toAddMonoidHom).index =
    R.toAddSubgroup.relIndex (integralClosure ℤ k).toSubring.toAddSubgroup
  rw [AddSubgroup.index_comap]
  congr 1
  ext x
  change (∃ y : 𝓞 k, (y : k) = x) ↔ x ∈ integralClosure ℤ k
  exact ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

/-- The formula `orderDisc R` is the actual trace discriminant of every integral basis of `R`.
This uses the existing discriminant/index theorem: the determinant of the basis-change
matrix has absolute value equal to the lattice index, and its square multiplies the
maximal-order discriminant. -/
theorem orderDisc_eq_discr {k : Type} [Field k] [NumberField k]
    (R : Subring k) (hR : IsImagQuadOrder k R)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ R) :
    orderDisc R = Algebra.discr ℤ b := by
  let O := toOrder R hR
  have hb : Algebra.discr ℤ b = O.discr := O.discr_eq_discr b
  rw [hb, O.discr_eq_index_sq_mul, toOrder_index_eq_conductor R hR]
  rfl

/-- The discriminant of an imaginary quadratic order is negative. -/
theorem orderDisc_neg {k : Type} [Field k] [NumberField k]
    (R : Subring k) (hR : IsImagQuadOrder k R) : orderDisc R < 0 := by
  let : NumberField.IsTotallyComplex k := hR.1
  have hdim := NumberField.IsTotallyComplex.finrank (K := k)
  have hc : NumberField.InfinitePlace.nrComplexPlaces k = 1 := by
    rw [hR.2.1] at hdim
    omega
  have hs := NumberField.sign_discr k
  rw [hc] at hs
  norm_num at hs
  rw [orderDisc]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (by exact_mod_cast hR.2.2.2)) hs

/-- A two-dimensional integral order has discriminant congruent to zero or one modulo four.
Complete its primitive unit element to a basis `(1, θ)` and write `θ² = a + dθ`;
the trace determinant is `d² + 4a`, whose residue modulo four is zero or one. -/
theorem discr_intBasis_mod_four {k : Type} [Field k] (R : Subring k)
    (b : Basis (Fin 2) ℤ R) :
    Algebra.discr ℤ b % 4 = 0 ∨ Algebra.discr ℤ b % 4 = 1 := by
  classical
  let : Module.Free ℤ R := Module.Free.of_basis b
  have hdim : Module.finrank ℤ R = 2 := by
    simpa using Module.finrank_eq_card_basis b
  obtain ⟨c, hc⟩ := Module.IsUnimodular.exists_basis_zero_eq hdim
    (Module.Free.isUnimodular_one (R := ℤ) (A := R))
  let a : ℤ := c.repr (c 1 * c 1) 0
  let d : ℤ := c.repr (c 1 * c 1) 1
  have hm : c 1 * c 1 = a • c 0 + d • c 1 := by
    simpa [Fin.sum_univ_two, a, d] using (c.sum_repr (c 1 * c 1)).symm
  have htr : ∀ x : R, Algebra.trace ℤ R x = (Algebra.leftMulMatrix c x).trace :=
    fun x => Algebra.trace_eq_matrix_trace c x
  have hrep : ∀ x : R, ∀ i j, Algebra.leftMulMatrix c x i j = c.repr (x * c j) i :=
    fun x i j => Algebra.leftMulMatrix_eq_repr_mul c x i j
  have t1 : Algebra.trace ℤ R 1 = 2 := by
    rw [htr, Matrix.trace_fin_two, hrep, hrep, one_mul, one_mul, c.repr_self, c.repr_self]
    simp
  have td : Algebra.trace ℤ R (c 1) = d := by
    rw [htr, Matrix.trace_fin_two, hrep, hrep, hc, mul_one, c.repr_self, hm,
      map_add, map_smul, map_smul]
    simp
  have tdd : Algebra.trace ℤ R (c 1 * c 1) = 2 * a + d ^ 2 := by
    rw [hm, map_add, map_smul, map_smul, hc, t1, td]
    simp
    ring
  have hd : Algebra.discr ℤ c = d ^ 2 + 4 * a := by
    rw [Algebra.discr_def, Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hc, one_mul, mul_one]
    rw [t1, td, tdd]
    ring
  rw [Algebra.discr_eq_discr R b c, hd]
  simp only [Int.add_emod, Int.mul_emod_right, add_zero, Int.sq_emod_four]
  omega

/-- The order discriminant satisfies the two residue classes in Fowler's proposition. -/
theorem orderDisc_mod_four {k : Type} [Field k] [NumberField k] (R : Subring k)
    (hR : IsImagQuadOrder k R) : orderDisc R % 4 = 0 ∨ orderDisc R % 4 = 1 := by
  obtain ⟨b⟩ := exists_intBasis_of_isImagQuadOrder R hR
  rw [orderDisc_eq_discr R hR b]
  exact discr_intBasis_mod_four R b

end HDec.CMBranch.FowlerBridges
