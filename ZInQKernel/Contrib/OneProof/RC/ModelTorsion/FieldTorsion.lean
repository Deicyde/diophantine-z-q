import Mathlib.SetTheory.Cardinal.NatCard
import ZInQKernel.Contrib.OneProof.RC.ModelTorsion.DivisionPolynomial
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_card_torsion_of_isAlgClosed

/-! # Geometric torsion in Weierstrass coordinates -/

namespace WeierstrassCurve.ModelTorsion

open Polynomial
open WeierstrassCurve.Affine

variable {K : Type*} [Field K] [DecidableEq K]

/-- An affine point is killed by the level exactly when its abscissa satisfies
the division equation. -/
theorem nsmul_some_eq_zero_iff (W : WeierstrassCurve K) (n : ℕ) {x y : K}
    (h : W.toAffine.Nonsingular x y) :
    n • (Point.some x y h : W.toAffine.Point) = 0 ↔ (xPolynomial W n).eval x = 0 := by
  have hsns := (W.toAffine.nonsingular_iff' x y).mp h
  have hsq := W.evalEval_ψ_sq hsns.1 (n : ℤ)
  rw [← natCast_zsmul, W.smul_eq_zero_iff_evalEval_ψ h, ← sq_eq_zero_iff, hsq, ΨSq_ofNat]
  by_cases he : Even n <;> simp [xPolynomial, he, eval_mul, mul_eq_zero]

omit [DecidableEq K] in
/-- A point on the Weierstrass equation lies above a root of the two-torsion
factor exactly when it equals its negative. -/
theorem eval_Ψ₂Sq_eq_zero_iff (W : WeierstrassCurve K) {x y : K}
    (hy : W.toAffine.Equation x y) :
    W.Ψ₂Sq.eval x = 0 ↔ y = W.toAffine.negY x y := by
  rw [← P2MW.S_WeierstrassCurve_card_torsion_of_isAlgClosed.Deep.sub_negY_sq_eq_Ψ₂Sq_eval
    W.toAffine hy, sq_eq_zero_iff, sub_eq_zero]

omit [DecidableEq K] in
/-- The nonidentity torsion coordinates over a field. -/
def affineCoordinates (W : WeierstrassCurve K) (n : ℕ) :=
  {xy : K × K // W.toAffine.Equation xy.1 xy.2 ∧ (xPolynomial W n).eval xy.1 = 0}

/-- The geometric torsion count in affine coordinates, with one point removed
for the identity section. -/
theorem card_affineCoordinates [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) :
    Nat.card (affineCoordinates W n) = n ^ 2 - 1 := by
  let toTorsion : Option (affineCoordinates W n) → Submodule.torsionBy ℤ W.toAffine.Point n
    | none => 0
    | some ⟨(x, y), he, hx⟩ =>
      let h := W.toAffine.equation_iff_nonsingular.mp he
      ⟨Point.some x y h, by
        change (n : ℤ) • (Point.some x y h : W.toAffine.Point) = 0
        rw [natCast_zsmul]
        exact (nsmul_some_eq_zero_iff W n h).2 hx⟩
  have hinj : Function.Injective toTorsion := by
    rintro (_ | ⟨⟨x, y⟩, h⟩) (_ | ⟨⟨x', y'⟩, h'⟩) e
    · rfl
    · exact False.elim (Point.some_ne_zero _ (congrArg Subtype.val e).symm)
    · exact False.elim (Point.some_ne_zero _ (congrArg Subtype.val e))
    · have he := congrArg Subtype.val e
      change Point.some x y _ = Point.some x' y' _ at he
      rcases Point.some.inj he with ⟨rfl, rfl⟩
      rfl
  have hsurj : Function.Surjective toTorsion := by
    rintro ⟨P, htor⟩
    cases P with
    | zero => exact ⟨none, rfl⟩
    | some x y h =>
      change (n : ℤ) • (Point.some x y h : W.toAffine.Point) = 0 at htor
      rw [natCast_zsmul] at htor
      exact ⟨some ⟨(x, y), h.1, (nsmul_some_eq_zero_iff W n h).1 htor⟩, rfl⟩
  let : Algebra K K := Algebra.id K
  have hcount := P2MW.S_WeierstrassCurve_card_torsion_of_isAlgClosed.solution
    (K := K) W hn
  change Nat.card (Submodule.torsionBy ℤ W.toAffine.Point n) = n ^ 2 at hcount
  have hc := Nat.card_congr (Equiv.ofBijective toTorsion ⟨hinj, hsurj⟩)
  rw [hcount] at hc
  have : Finite (Submodule.torsionBy ℤ W.toAffine.Point n) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcount]
    exact pow_ne_zero _ (by rintro rfl; simp at hn)
  let : Finite (affineCoordinates W n) :=
    Finite.of_injective _ (hinj.comp (Option.some_injective _))
  rw [Finite.card_option] at hc
  omega

#print axioms nsmul_some_eq_zero_iff
#print axioms eval_Ψ₂Sq_eq_zero_iff
#print axioms card_affineCoordinates

end WeierstrassCurve.ModelTorsion
