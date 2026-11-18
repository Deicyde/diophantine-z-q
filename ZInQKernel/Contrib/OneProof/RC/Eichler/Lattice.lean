import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Visibility.Theta

/-!
# Lattices in the definite quaternion algebra

Tex 8464–8468, 8563–8564 and 8605–8611. The algebra below is on-the-spot (c).
We use finitely generated full integer lattices in the rational vector space; a common
denominator reduces boundedness to a finite box of integer coordinates.
-/

open scoped Quaternion
open Module

namespace ZInQ.Manuscript.RC.Eichler

abbrev B (a b : ℚ) := ℍ[ℚ,a,0,b]

/-- A full integer lattice in a rational vector space. -/
abbrev FullLattice {V : Type*} [AddCommGroup V] [Module ℚ V]
    (L : Submodule ℤ V) := Submodule.IsLattice ℚ L

namespace FullLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : Submodule ℤ V}

omit [Module ℚ V] in
theorem span_basis (c : Basis ι ℤ L) :
    Submodule.span ℤ (Set.range fun i => (c i : V)) = L := by
  change Submodule.span ℤ (Set.range (L.subtype ∘ c)) = L
  rw [Set.range_comp, ← Submodule.map_span, c.span_eq, Submodule.map_subtype_top]

/-- The integer basis of a full lattice has the same indexing type as an ambient basis. -/
noncomputable def basis {ι : Type*} [Fintype ι] (h : FullLattice L) (e : Basis ι ℚ V) :
    Basis ι ℤ L := by
  classical
  letI := h
  let c := Module.Free.chooseBasis ℤ L
  let d := c.extendOfIsLattice ℚ
  exact c.reindex (Fintype.equivOfCardEq ((Module.finrank_eq_card_basis d).symm.trans
    (Module.finrank_eq_card_basis e)))

/-- The integer basis of a full lattice also gives a rational basis of the ambient space. -/
noncomputable def ratBasis {ι : Type*} [Fintype ι] (h : FullLattice L) (e : Basis ι ℚ V) :
    Basis ι ℚ V := by
  letI := h
  exact (h.basis e).extendOfIsLattice ℚ

theorem span_ratBasis {ι : Type*} [Fintype ι] (h : FullLattice L) (e : Basis ι ℚ V) :
    Submodule.span ℤ (Set.range (h.ratBasis e)) = L := by
  have he : (h.ratBasis e : ι → V) = fun i => (h.basis e i : V) := by
    funext i
    exact Basis.extendOfIsLattice_apply ℚ (h.basis e) i
  rw [he, span_basis]

end FullLattice

section Coordinates

variable {a b : ℚ}

abbrev coord (x : B a b) : Fin 4 → ℚ := QuaternionAlgebra.linearEquivTuple a 0 b x

def weight (a b : ℚ) : Fin 4 → ℚ := ![1, -a, -b, a * b]

theorem weight_pos (ha : a < 0) (hb : b < 0) (i : Fin 4) : 0 < weight a b i := by
  fin_cases i <;> simp [weight, ha, hb, mul_pos_of_neg_of_neg ha hb]

theorem nrd_sum (x : B a b) :
    Visibility.nrd x = ∑ i, weight a b i * coord x i ^ 2 := by
  rw [Visibility.nrd_apply, Fin.sum_univ_four]
  change _ = 1 * x.re ^ 2 + -a * x.imI ^ 2 + -b * x.imJ ^ 2 + a * b * x.imK ^ 2
  ring

theorem nrd_pos (ha : a < 0) (hb : b < 0) {x : B a b} (hx : x ≠ 0) :
    0 < Visibility.nrd x := by
  have hx' : ∃ i, coord x i ≠ 0 := by
    by_contra! he
    apply hx
    apply (QuaternionAlgebra.linearEquivTuple a 0 b).injective
    funext i
    change coord x i = (QuaternionAlgebra.linearEquivTuple a 0 b 0) i
    rw [map_zero]
    exact he i
  obtain ⟨i, hi⟩ := hx'
  rw [nrd_sum]
  exact lt_of_lt_of_le (mul_pos (weight_pos ha hb i) (sq_pos_of_ne_zero hi))
    (Finset.single_le_sum (fun j _ => mul_nonneg (weight_pos ha hb j).le (sq_nonneg _))
      (Finset.mem_univ i))

/-- Every nonzero quaternion in the definite algebra is a unit. -/
def unitOfNeZero (ha : a < 0) (hb : b < 0) (x : B a b) (hx : x ≠ 0) : (B a b)ˣ where
  val := x
  inv := (Visibility.nrd x)⁻¹ • star x
  val_inv := by
    rw [mul_smul_comm, ← Visibility.algebraMap_nrd, Algebra.smul_def, ← map_mul,
      inv_mul_cancel₀ (nrd_pos ha hb hx).ne', map_one]
  inv_val := by
    rw [smul_mul_assoc, QuaternionAlgebra.star_mul_eq_coe]
    rw [Visibility.quat_re_mul_comm (star x) x]
    change (Visibility.nrd x)⁻¹ • algebraMap ℚ (B a b) (Visibility.nrd x) = 1
    rw [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ (nrd_pos ha hb hx).ne', map_one]

/-- A finitely generated lattice has a single denominator for all its ambient coordinates. -/
theorem commonDenom {V : Type*} [AddCommGroup V] [Module ℚ V]
    {ι : Type*} [Fintype ι] (e : Basis ι ℚ V) {L : Submodule ℤ V} (h : L.FG) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ L, ∀ i, ∃ z : ℤ, (z : ℚ) = (d : ℚ) * e.repr x i := by
  classical
  obtain ⟨s, hs, rfl⟩ := Submodule.fg_def.mp h
  let := hs.to_subtype
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun t : s × ι => e.repr t.1 t.2)
  refine ⟨d, nonZeroDivisors.ne_zero d.prop, fun x hx i => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz⟩ := hd (⟨y, hy⟩, i)
    exact ⟨z, hz⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by simp [hu, hv, mul_add]⟩
  | smul c x _ hx =>
    obtain ⟨u, hu⟩ := hx
    refine ⟨c * u, ?_⟩
    simp only [Int.cast_mul, hu, ← Int.cast_smul_eq_zsmul ℚ, map_smul, Finsupp.smul_apply, smul_eq_mul]
    ring

/-- A positive definite norm bound cuts a finite set out of an integer lattice. -/
theorem finite_norm_le (ha : a < 0) (hb : b < 0)
    (L : Submodule ℤ (B a b)) (hL : L.FG) (q : ℚ) :
    {x : B a b | x ∈ L ∧ Visibility.nrd x ≤ q}.Finite := by
  classical
  obtain ⟨d, hd, hdL⟩ := commonDenom (QuaternionAlgebra.basisOneIJK a 0 b) hL
  let f (x : B a b) (i : Fin 4) : ℤ := ⌊(d : ℚ) * coord x i⌋
  have hf (x : B a b) (hx : x ∈ L) (i : Fin 4) : (f x i : ℚ) = (d : ℚ) * coord x i := by
    obtain ⟨v, hv⟩ := hdL x hx i
    change (v : ℚ) = (d : ℚ) * coord x i at hv
    simp [f, ← hv]
  let r (i : Fin 4) : ℚ := max 1 (q / weight a b i)
  let M (i : Fin 4) : ℤ := ⌈|(d : ℚ)| * r i⌉
  apply Set.Finite.of_finite_image (f := f)
  · refine (Set.finite_Icc (-M) M).subset ?_
    rintro _ ⟨x, ⟨hx, hq⟩, rfl⟩
    have hcoord (i : Fin 4) : |coord x i| ≤ r i := by
      have hterm := (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
        mul_nonneg (weight_pos ha hb j).le (sq_nonneg (coord x j))) (Finset.mem_univ i))
      rw [← nrd_sum] at hterm
      have hs : coord x i ^ 2 ≤ q / weight a b i :=
        (le_div_iff₀ (weight_pos ha hb i)).2 (by rw [mul_comm]; exact hterm.trans hq)
      by_contra! hn
      have hr : 1 ≤ r i := le_max_left _ _
      have hm : q / weight a b i ≤ r i := le_max_right _ _
      have hv : |coord x i| < |coord x i| ^ 2 := by
        nlinarith [mul_pos (show 0 < |coord x i| by linarith)
          (show 0 < |coord x i| - 1 by linarith)]
      rw [sq_abs] at hv
      linarith
    constructor <;> intro i
    · have hfi : |(f x i : ℚ)| ≤ (M i : ℚ) := by
        rw [hf x hx i, abs_mul]
        exact (mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _)).trans (Int.le_ceil _)
      exact_mod_cast (abs_le.mp hfi).1
    · have hfi : |(f x i : ℚ)| ≤ (M i : ℚ) := by
        rw [hf x hx i, abs_mul]
        exact (mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _)).trans (Int.le_ceil _)
      exact_mod_cast (abs_le.mp hfi).2
  · intro x hx y hy hxy
    apply (QuaternionAlgebra.linearEquivTuple a 0 b).injective
    funext i
    apply mul_left_cancel₀ (Int.cast_ne_zero.mpr hd : (d : ℚ) ≠ 0)
    rw [← hf x hx.1, ← hf y hy.1, hxy]

end Coordinates

end ZInQ.Manuscript.RC.Eichler
