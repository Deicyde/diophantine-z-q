import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! Two algebraic steps of the integral-closure construction of the integral
Atkin–Lehner operator (Atiyah–Macdonald, *Introduction to Commutative Algebra*, 1969,
Ch. 5, UNVERIFIED, for integral closure).

* `isIntegral_of_finite`: if `B` is finite over a ring `D` along `θ`, and a ring map
  `φ : B → C` sends the image of `D` to elements integral over `A`, then it sends all of
  `B` to elements integral over `A`.
* `mem_range_of_isIntegral`: let `κ : A → B` be injective, `π ∈ A` with `κ π` a unit, and
  `πA` a radical ideal. If `b ∈ B` is integral over `A` and `κ(π)ⁿ b` lies in the image
  of `κ`, then so does `b`. (For `A` flat over a DVR with uniformizer `π`, `B = A[1/π]`
  and `A/πA` reduced, this says `A` is integrally closed in `A[1/π]`.) -/

set_option autoImplicit false

noncomputable section

open Polynomial
open scoped TensorProduct

namespace ZInQ.Manuscript.RC.ModelGeneric5

section Finite

variable {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D] [Algebra A C]

theorem isIntegral_of_finite (θ : D →+* B) (hθ : θ.Finite) (φ : B →+* C)
    (hD : ∀ d, IsIntegral A (φ (θ d))) (b : B) : IsIntegral A (φ b) := by
  let T := integralClosure A C
  have hb : θ.IsIntegralElem b := hθ.to_isIntegral b
  obtain ⟨p, hp, hpb⟩ := hb
  -- the coefficients of `p`, pushed by `φ ∘ θ`, lie in `T`
  let ψ : D →+* T := ((φ.comp θ).codRestrict T.toSubring fun d => hD d)
  letI : Algebra T C := T.toAlgebra
  have hT : IsIntegral T (φ b) := by
    refine ⟨p.map ψ, hp.map ψ, ?_⟩
    rw [eval₂_map]
    have : (algebraMap T C).comp ψ = φ.comp θ := by
      ext d
      rfl
    rw [this, ← hom_eval₂, hpb, map_zero]
  exact isIntegral_trans (R := A) (A := T) (φ b) hT

end Finite

section Radical

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- One division by `π`: if `π y` is in the image and `y` is integral, so is `y`. -/
theorem mem_range_of_isIntegral_of_mul (hκ : Function.Injective (algebraMap A B)) (π : A)
    (hπ : IsUnit (algebraMap A B π)) (hrad : (Ideal.span {π}).IsRadical) {y : B}
    (hy : IsIntegral A y) {a : A} (ha : algebraMap A B a = algebraMap A B π * y) :
    ∃ c, algebraMap A B c = y := by
  let κ := algebraMap A B
  obtain ⟨p, hp, hpy⟩ := hy
  let m := p.natDegree
  have hscale : eval₂ κ (κ π * y) (scaleRoots p π) = κ π ^ m * eval₂ κ y p :=
    scaleRoots_eval₂_mul κ y π
  rw [hpy, mul_zero, ← ha, eval₂_hom] at hscale
  have h0 : (scaleRoots p π).eval a = 0 := hκ (hscale.trans κ.map_zero.symm)
  have hdeg : (scaleRoots p π).natDegree < m + 1 := by
    rw [natDegree_scaleRoots]; omega
  rw [eval_eq_sum_range' hdeg, Finset.sum_range_succ, coeff_scaleRoots,
    show p.coeff m = 1 from hp, Nat.sub_self, pow_zero, one_mul, one_mul] at h0
  have hmem : a ^ m ∈ Ideal.span {π} := by
    rw [show a ^ m = -∑ i ∈ Finset.range m, (scaleRoots p π).coeff i * a ^ i by
      linear_combination h0]
    refine neg_mem ?_
    refine sum_mem fun i hi => ?_
    rw [coeff_scaleRoots]
    have hi' : 0 < m - i := Nat.sub_pos_of_lt (Finset.mem_range.mp hi)
    obtain ⟨k, hk⟩ : ∃ k, m - i = k + 1 := ⟨m - i - 1, by omega⟩
    rw [hk, pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _
      (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self π)))
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hrad ⟨m, hmem⟩)
  refine ⟨c, ?_⟩
  apply hπ.mul_left_cancel
  rw [← ha, ← hc, map_mul, mul_comm]

/-- **Integral closedness in the localization at `π`**: an element integral over `A` with
`πⁿ b` in the image of `A` is itself in the image. -/
theorem mem_range_of_isIntegral (hκ : Function.Injective (algebraMap A B)) (π : A)
    (hπ : IsUnit (algebraMap A B π)) (hrad : (Ideal.span {π}).IsRadical) (n : ℕ) :
    ∀ {b : B}, IsIntegral A b → (∃ a, algebraMap A B a = algebraMap A B π ^ n * b) →
      ∃ c, algebraMap A B c = b := by
  induction n with
  | zero =>
    intro b _ ⟨a, ha⟩
    exact ⟨a, by rw [ha, pow_zero, one_mul]⟩
  | succ n ih =>
    intro b hb ⟨a, ha⟩
    have hy : IsIntegral A (algebraMap A B π ^ n * b) :=
      ((isIntegral_algebraMap (x := π)).pow n).mul hb
    obtain ⟨c, hc⟩ := mem_range_of_isIntegral_of_mul hκ π hπ hrad hy
      (a := a) (by rw [ha, pow_succ]; ring)
    exact ih hb ⟨c, hc⟩

/-- The same, for a ring map `κ` instead of an algebra structure. -/
theorem exists_eq_of_isIntegralElem {A B : Type*} [CommRing A] [CommRing B] (κ : A →+* B)
    (hκ : Function.Injective κ) (π : A) (hπ : IsUnit (κ π)) (hrad : (Ideal.span {π}).IsRadical)
    {b : B} (hb : κ.IsIntegralElem b) (n : ℕ) (a : A) (ha : κ a = κ π ^ n * b) :
    ∃ c, κ c = b := by
  letI := κ.toAlgebra
  exact mem_range_of_isIntegral hκ π hπ hrad n hb ⟨a, ha⟩

end Radical

section Residue

variable {R A : Type*} [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]

/-- If the special fibre `k ⊗_R A` is reduced and `𝔪_R = (π)`, then `πA` is radical. -/
theorem isRadical_span_of_residue_reduced {π : R}
    (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    [IsReduced (IsLocalRing.ResidueField R ⊗[R] A)] :
    (Ideal.span {algebraMap R A π}).IsRadical := by
  have hm : (IsLocalRing.maximalIdeal R).map (algebraMap R A) = Ideal.span {algebraMap R A π} := by
    rw [hπ, Ideal.map_span, Set.image_singleton]
  let eq := Algebra.TensorProduct.quotIdealMapEquivQuotTensor A (IsLocalRing.maximalIdeal R)
  have : IsReduced ((R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] A) :=
    inferInstanceAs (IsReduced (IsLocalRing.ResidueField R ⊗[R] A))
  have : IsReduced (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
    isReduced_of_injective eq.toRingHom eq.injective
  rw [← hm]
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr inferInstance

end Residue

section Restrict

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The restriction of a ring endomorphism `σ` of `B` to a subring `κ(A)` it preserves. -/
def restrictRange (κ : A →+* B) (hκ : Function.Injective κ) (σ : B →+* B)
    (h : ∀ a, ∃ c, κ c = σ (κ a)) : A →+* A :=
  ((RingEquiv.ofBijective κ.rangeRestrict
      ⟨fun _ _ hxy => hκ (congrArg Subtype.val hxy), κ.rangeRestrict_surjective⟩).symm.toRingHom).comp
    ((σ.comp κ).codRestrict κ.range fun a => (RingHom.mem_range (f := κ)).mpr (h a))

theorem restrictRange_spec (κ : A →+* B) (hκ : Function.Injective κ) (σ : B →+* B)
    (h : ∀ a, ∃ c, κ c = σ (κ a)) (a : A) :
    κ (restrictRange κ hκ σ h a) = σ (κ a) := by
  let e := RingEquiv.ofBijective κ.rangeRestrict
    ⟨fun _ _ hxy => hκ (congrArg Subtype.val hxy), κ.rangeRestrict_surjective⟩
  let y : κ.range := ⟨σ (κ a), (RingHom.mem_range (f := κ)).mpr (h a)⟩
  change κ (e.symm y) = y.val
  exact congrArg Subtype.val (e.apply_symm_apply y)

end Restrict

#print axioms isIntegral_of_finite
#print axioms mem_range_of_isIntegral
#print axioms exists_eq_of_isIntegralElem
#print axioms isRadical_span_of_residue_reduced
#print axioms restrictRange
#print axioms restrictRange_spec

end ZInQ.Manuscript.RC.ModelGeneric5
