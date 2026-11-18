import ZInQKernel.Contrib.OneProof.CMBranch
import ZInQKernel.Contrib.OneProof.GR512Bridge
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Orders.Discriminant
import Mathlib.LinearAlgebra.Unimodular
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.PicardGroup

/-! # Fowler's Proposition 2·7 and the order-discriminant bridge -/

namespace HDec.CMBranch

open NumberField Module TauCeti.GlobalNumberFields
open scoped nonZeroDivisors

/-- A finite-index imaginary quadratic order has a two-element integral basis.
The existing order construction gives a finite free integer module; localizing its basis
in the ambient field shows that its rank is two. -/
theorem exists_intBasis_of_isImagQuadOrder {k : Type} [Field k] [NumberField k]
    (R : Subring k) (hR : IsImagQuadOrder k R) : Nonempty (Basis (Fin 2) ℤ R) := by
  classical
  let O := GR512Bridge.toOrder R hR.2.2.1 hR.2.2.2
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
    (GR512Bridge.toOrder R hR.2.2.1 hR.2.2.2).index = LeafQM.AV.conductor R := by
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
    (R : Subring k) (hR : IsImagQuadOrder k R) (b : Basis (Fin 2) ℤ R) :
    orderDisc R = Algebra.discr ℤ b := by
  let O := GR512Bridge.toOrder R hR.2.2.1 hR.2.2.2
  have hb : Algebra.discr ℤ b = O.discr := O.discr_eq_discr b
  rw [hb, O.discr_eq_index_sq_mul, toOrder_index_eq_conductor R hR]
  rfl

/-- The Picard cardinal is the class number: for every domain, the class group of
invertible fractional ideals modulo principal ideals is isomorphic to the Picard group.
No maximality or Dedekind-domain hypothesis is needed. -/
theorem card_pic_eq_card_classGroup {k : Type} [Field k] (R : Subring k) :
    Nat.card (CommRing.Pic R) = Nat.card (ClassGroup R) :=
  (Nat.card_congr (ClassGroup.equivPic R).toEquiv).symm

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

/-- Every integral basis of an imaginary quadratic order has negative discriminant. -/
theorem discr_intBasis_neg {k : Type} [Field k] [NumberField k]
    (R : Subring k) (hR : IsImagQuadOrder k R) (b : Basis (Fin 2) ℤ R) :
    Algebra.discr ℤ b < 0 := by
  rw [← orderDisc_eq_discr R hR b]
  exact orderDisc_neg R hR

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

/-- G. Fowler, *Some uniform effective results on André–Oort for sums of powers in ℂⁿ*,
Math. Proc. Cambridge Philos. Soc. **180** (2026), 607–641, Proposition 2·7, p. 615;
the definition of `h(Δ)` as the class number of the imaginary quadratic order of
discriminant `Δ` is on p. 613.

The printed statement is re-indexed by imaginary quadratic orders: the order of a given
negative discriminant congruent to zero or one modulo four is unique up to isomorphism.
`IsImagQuadOrder k R` encodes a totally complex degree-two number field and an order of
finite index in its ring of integers. The order discriminant is the lattice trace
discriminant `Algebra.discr ℤ b`, quantified over every integral basis `b`; it is basis
independent. Negativity and the congruence condition are automatic for these orders,
so neither is added as an extra hypothesis. The printed `h(Δ)` is
`Nat.card (ClassGroup R)`, where `ClassGroup` uses invertible fractional ideals modulo
principal ideals. The positive integer in the print is `k' : ℕ` with `1 ≤ k'`, the
class-number premise is `hΔ ≤ k'`, and the conclusion is exactly
`√|Δ| ≤ 2 k'² exp(21000 k'²)`. -/
def FowlerProp27Printed : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (R : Subring k), IsImagQuadOrder k R →
    ∀ b : Basis (Fin 2) ℤ R,
      let Δ : ℤ := Algebra.discr ℤ b
      let hΔ : ℕ := Nat.card (ClassGroup R)
      ∀ k' : ℕ, 1 ≤ k' → hΔ ≤ k' →
        Real.sqrt |(Δ : ℝ)| ≤
          2 * (k' : ℝ) ^ 2 * Real.exp (21000 * (k' : ℝ) ^ 2)

/-- Fowler's printed proposition implies the existing CM-branch leaf, with no additional
hypothesis: identify the lattice discriminant and the class-number cardinal, then apply
the printed inequality. -/
theorem fowlerProp27_of_printed (h : FowlerProp27Printed) : FowlerProp27 := by
  intro k _ _ R hR n hn hh
  obtain ⟨b⟩ := exists_intBasis_of_isImagQuadOrder R hR
  have hc : Nat.card (ClassGroup R) ≤ n := by
    rw [← card_pic_eq_card_classGroup R]
    exact hh
  have hp := h k R hR b n hn hc
  change Real.sqrt |(Algebra.discr ℤ b : ℝ)| ≤
    2 * (n : ℝ) ^ 2 * Real.exp (21000 * (n : ℝ) ^ 2) at hp
  rwa [← orderDisc_eq_discr R hR b] at hp

end HDec.CMBranch
