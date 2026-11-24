import TauCeti.FieldTheory.FunctionField.Consequences.HighDegree
import TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! A rational place on a genus-zero function field determines a rational
coordinate with its only pole at that place. -/

noncomputable section

open IntermediateField

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- A genus-zero function field with exact constant field and a rational place
is rational over the constants. The selected generator has just one simple pole. -/
theorem exists_ratFunc_equiv_of_genus_zero (hF : IsFunctionField k F)
    (hc : IsIntegrallyClosedIn k F) (hg : genus k F = 0) (P : Place k F)
    (hP : P.degree = 1) :
    ∃ e : RatFunc k ≃ₐ[k] F, P.ord (e RatFunc.X) = -1 ∧
      ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord (e RatFunc.X) := by
  obtain ⟨x, _, hx, hreg⟩ := P.exists_ord_eq_neg_and_forall_ne_ord_nonneg
    hF hc (n := 1) (by simp [hg])
  have ht : Transcendental k x := P.transcendental_of_ord_ne_zero (by rw [hx]; norm_num)
  have htop : k⟮x⟯ = ⊤ := IntermediateField.finrank_eq_one_iff_eq_top.mp (by
    rw [finrank_adjoin_eq_mul_degree_of_ord_eq_neg hF (n := 1) one_ne_zero hx hreg, hP, mul_one])
  let e := (RatFunc.algEquivOfTranscendental x ht).trans
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)
  have hX : e RatFunc.X = x := RatFunc.algEquivOfTranscendental_X x ht
  exact ⟨e, hX ▸ hx, hX ▸ hreg⟩

end TauCeti.Place
