import ZInQKernel.Contrib.TYZChain.Lcal

/-!
# tyz-genus: `ℚ(i) = QNeg 1`: cyclotomic of order 4, class number 1, four roots of unity
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenusFold

open ZInQ.RouteK.Rank5b NumberField

/-- `i = √−1` in `QNeg 1`. -/
def iQ : QNeg 1 := ⟨0, 1⟩

theorem iQ_sq : iQ ^ 2 = -1 := by
  ext <;> simp [iQ, pow_two]

theorem iQ_pow_four : iQ ^ (2 ^ 2) = 1 := by
  rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, iQ_sq]; norm_num

theorem iQ_isPrimitiveRoot : IsPrimitiveRoot iQ (2 ^ 2) := by
  refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) iQ_pow_four fun l hl hl4 => ?_
  norm_num at hl4
  interval_cases l
  · intro h
    have := congrArg QuadraticAlgebra.im h
    simp [iQ, QuadraticAlgebra.im_one] at this
  · rw [iQ_sq]; intro h
    have := congrArg QuadraticAlgebra.re h
    simp [QuadraticAlgebra.re_one] at this
    norm_num at this
  · intro h
    have := congrArg QuadraticAlgebra.im h
    simp [iQ, pow_succ, QuadraticAlgebra.im_one] at this

instance isCyclotomicExtension_four : IsCyclotomicExtension {2 ^ 2} ℚ (QNeg 1) := by
  rw [IsCyclotomicExtension.iff_singleton]
  refine ⟨⟨iQ, iQ_isPrimitiveRoot⟩, fun x => ?_⟩
  have hz : iQ ∈ Algebra.adjoin ℚ {b : QNeg 1 | b ^ (2 ^ 2) = 1} :=
    Algebra.subset_adjoin iQ_pow_four
  have hx : x = algebraMap ℚ (QNeg 1) x.re + x.im • iQ := by
    ext <;> simp [iQ]
  rw [hx]
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.smul_mem _ hz _)

/-- `#μ(ℚ(i)) = 4`. -/
theorem torsionOrder_one : NumberField.Units.torsionOrder (QNeg 1) = 4 := by
  rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := 2 ^ 2)]
  norm_num

/-- `𝓞_{ℚ(i)}` is a principal ideal ring (Minkowski: `|d| = 4 < π²`). -/
theorem pid_one : IsPrincipalIdealRing (𝓞 (QNeg 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [IsCyclotomicExtension.Rat.discr_prime_pow (p := 2) (k := 2) (K := QNeg 1),
    IsCyclotomicExtension.finrank (n := 2 ^ 2) (QNeg 1) (Polynomial.cyclotomic.irreducible_rat (by norm_num)),
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := 2 ^ 2) (K := QNeg 1)]
  have ht : (2 ^ 2 : ℕ).totient = 2 := by decide
  rw [ht]
  norm_num
  nlinarith [Real.pi_gt_three]

theorem classGroup_one_subsingleton : Subsingleton (ClassGroup (𝓞 (QNeg 1))) := by
  have h1 : Fintype.card (ClassGroup (𝓞 (QNeg 1))) = 1 := card_classGroup_eq_one_iff.mpr pid_one
  exact Fintype.card_le_one_iff_subsingleton.mp h1.le

end ZInQ.Contrib.TYZGenusFold
