import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Models
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The division prime (tex 8551–8561)
The completed division algebra and its maximal order are supplied by the local
order interface; the residue field used here is Mathlib's `GaloisField p 2`.
-/

namespace ZInQ.Manuscript.RC.LocalWeights

open scoped Topology

variable (p : ℕ) [Fact p.Prime]

/-- Coordinates to be supplied at the division prime. The topology and reduction
are those of the maximal order. The two trace fields describe its trace-zero
residue line and the action of a chosen division uniformizer on that line. -/
structure DivisionCoordinates (D : Type*) [DivisionRing D] [Algebra ℚ_[p] D]
    [Algebra ℤ_[p] D] [TopologicalSpace D] where
  order : Subalgebra ℤ_[p] D
  tr : D →ₗ[ℚ_[p]] ℚ_[p]
  nrd : D →* ℚ_[p]
  red : order →+* GaloisField p 2
  red_surj : Function.Surjective red
  red_scalar : ∀ a : ℤ_[p], red (algebraMap ℤ_[p] order a) =
    algebraMap (ZMod p) (GaloisField p 2) (PadicInt.toZMod a)
  red_locallyConstant : IsLocallyConstant red
  order_open : IsOpen (order : Set D)
  order_compact : IsCompact (order : Set D)
  beta : GaloisField p 2
  beta_ne_zero : beta ≠ 0
  trace_line : ∀ x : order, tr x.val = 0 →
    ∃ t : ZMod p, red x = algebraMap (ZMod p) (GaloisField p 2) t * beta
  uniformizer : Dˣ
  uniformizer_order : order ≃+* order
  uniformizer_conj : ∀ x : order, (uniformizer_order x).val =
    (↑uniformizer⁻¹ : D) * x.val * (↑uniformizer : D)
  uniformizer_frobenius : ∀ x : order, red (uniformizer_order x) = (red x) ^ p
  beta_frobenius : beta ^ p = -beta

variable {p} {D : Type*} [DivisionRing D] [Algebra ℚ_[p] D] [Algebra ℤ_[p] D]
  [TopologicalSpace D]

namespace DivisionCoordinates
variable (C : DivisionCoordinates p D)

private theorem coordinate_injective :
    Function.Injective (fun t : ZMod p =>
      algebraMap (ZMod p) (GaloisField p 2) t * C.beta) :=
  fun _ _ h => (algebraMap (ZMod p) (GaloisField p 2)).injective
    (mul_right_cancel₀ C.beta_ne_zero h)

/-- The Legendre weight on the residue line, zero away from its nonzero points. -/
noncomputable def residueWeight {O : Type*} [Ring O] (a : GaloisField p 2) : O :=
  open Classical in
  if h : ∃ t : ZMod p, a = algebraMap (ZMod p) (GaloisField p 2) t * C.beta then
    (quadraticChar (ZMod p) h.choose : O)
  else 0

theorem residueWeight_eq {O : Type*} [Ring O] (t : ZMod p) :
    C.residueWeight (algebraMap (ZMod p) (GaloisField p 2) t * C.beta) =
      (quadraticChar (ZMod p) t : O) := by
  classical
  have h : ∃ z, algebraMap (ZMod p) (GaloisField p 2) t * C.beta =
      algebraMap (ZMod p) (GaloisField p 2) z * C.beta := ⟨t, rfl⟩
  rw [residueWeight, dite_eq_left h, C.coordinate_injective h.choose_spec.symm]

/-- The integral trace-zero weight; for an ambient input use zero outside the order. -/
noncomputable def divisionWeight {O : Type*} [Ring O] (x : C.order) : O :=
  C.residueWeight (C.red x)

theorem divisionWeight_nonzero_iff {O : Type*} [Ring O] [Nontrivial O]
    (x : C.order) (hx : C.tr x.val = 0) : (C.divisionWeight x : O) ≠ 0 ↔ C.red x ≠ 0 := by
  obtain ⟨t, ht⟩ := C.trace_line x hx
  unfold divisionWeight
  rw [ht, C.residueWeight_eq]
  by_cases hz : t = 0
  · simp [hz]
  · have ht' : algebraMap (ZMod p) (GaloisField p 2) t ≠ 0 := by
      intro h
      apply hz
      apply (algebraMap (ZMod p) (GaloisField p 2)).injective
      simpa only [map_zero] using h
    have hn := mul_ne_zero ht' C.beta_ne_zero
    rcases quadraticChar_dichotomy hz with h | h <;> simp [hn, h]

/-- Reducing the scalar `-x²` gives the norm residue used in tex 8559.
Here `a` is the integral representative of the reduced norm. -/
theorem norm_residue_of_trace_zero (x : C.order) (hx : C.tr x.val = 0) (a : ℤ_[p])
    (ha : algebraMap ℤ_[p] D a = -(x.val ^ 2)) :
    ∃ t : ZMod p, C.red x = algebraMap (ZMod p) (GaloisField p 2) t * C.beta ∧
      algebraMap (ZMod p) (GaloisField p 2) (PadicInt.toZMod a) =
        -(algebraMap (ZMod p) (GaloisField p 2) t * C.beta) ^ 2 := by
  obtain ⟨t, ht⟩ := C.trace_line x hx
  have ha' : algebraMap ℤ_[p] C.order a = -(x ^ 2) := Subtype.ext ha
  refine ⟨t, ht, ?_⟩
  rw [← C.red_scalar, ha', map_neg, map_pow, ht]

theorem divisionWeight_locallyConstant {O : Type*} [Ring O] :
    IsLocallyConstant (C.divisionWeight : C.order → O) :=
  C.red_locallyConstant.comp C.residueWeight

theorem divisionWeight_conj {O : Type*} [Ring O] (u : C.orderˣ) (x : C.order) :
    C.divisionWeight ((↑u⁻¹ : C.order) * x * ↑u) = (C.divisionWeight x : O) := by
  unfold divisionWeight
  have h := congrArg C.red (Units.inv_mul u)
  simp only [map_mul, map_one] at h
  rw [map_mul, map_mul, mul_right_comm, h, one_mul]

theorem divisionWeight_scale {O : Type*} [Ring O] (x : C.order) (hx : C.tr x.val = 0)
    (v : ℤ_[p]ˣ) :
    C.divisionWeight (algebraMap ℤ_[p] C.order v.val * x) =
      (quadraticChar (ZMod p) (PadicInt.toZMod v.val) : O) * C.divisionWeight x := by
  obtain ⟨t, ht⟩ := C.trace_line x hx
  unfold divisionWeight
  rw [map_mul, C.red_scalar, ht, ← mul_assoc, ← map_mul, C.residueWeight_eq,
    C.residueWeight_eq, map_mul, Int.cast_mul]

theorem divisionWeight_uniformizer {O : Type*} [Ring O] (x : C.order)
    (hx : C.tr x.val = 0) (hp : p % 4 = 3) :
    C.divisionWeight (C.uniformizer_order x) = -(C.divisionWeight x : O) := by
  have hchar : quadraticChar (ZMod p) (-1) = -1 := by
    rw [quadraticChar_neg_one ((ringChar.eq (ZMod p) p).substr (by omega : p ≠ 2)),
      ZMod.card, ZMod.χ₄_nat_three_mod_four hp]
  obtain ⟨t, ht⟩ := C.trace_line x hx
  unfold divisionWeight
  rw [C.uniformizer_frobenius, ht, mul_pow, ← map_pow, ZMod.pow_card, C.beta_frobenius,
    mul_neg, ← neg_mul, ← map_neg, C.residueWeight_eq, C.residueWeight_eq,
    neg_eq_neg_one_mul, map_mul, hchar, Int.cast_mul, Int.cast_neg, Int.cast_one, neg_one_mul]

end DivisionCoordinates
end ZInQ.Manuscript.RC.LocalWeights

open ZInQ.Manuscript.RC.LocalWeights in
#print axioms DivisionCoordinates.coordinate_injective
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms DivisionCoordinates.residueWeight_eq
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms DivisionCoordinates.divisionWeight_nonzero_iff
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms DivisionCoordinates.norm_residue_of_trace_zero
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms DivisionCoordinates.divisionWeight_locallyConstant
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms DivisionCoordinates.divisionWeight_conj
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms DivisionCoordinates.divisionWeight_scale
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms DivisionCoordinates.divisionWeight_uniformizer
