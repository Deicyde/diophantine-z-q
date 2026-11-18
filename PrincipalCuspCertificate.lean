import PrincipalCuspExpansion

/-!
# An actual principal-to-square-level cusp certificate

The existence statement includes equality to the normalized positive-rational
slash, all-cusp vanishing, nonvanishing when the input is nonzero, and the
period-matched q-expansion. It asserts no eigenform or newform extraction.
-/

noncomputable section
set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.PrincipalCuspTransport

/-- A nonzero principal cusp form has the genuine square-level cusp carrier and exact expansion. -/
theorem exists_nonzero_square_level_cusp (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (hf : f ≠ 0) :
    ∃ g : CuspForm ((Gamma1 (N ^ 2)).map (mapGL ℝ)) k,
      g ≠ 0 ∧
      (∀ τ : ℍ, g τ = f (TauCeti.scaleGL N • τ)) ∧
      (∀ c : OnePoint ℝ, IsCusp c ((Gamma1 (N ^ 2)).map (mapGL ℝ)) → c.IsZeroAt ⇑g k) ∧
      qExpansion 1 g = qExpansion (N : ℝ) f ∧
      ⇑g = (N : ℂ) ^ (1 - k) •
        (⇑f ∣[k] GeneralLinearGroup.map (algebraMap ℚ ℝ) (TauCeti.scaleGLRat N)) ∧
      0 < (TauCeti.scaleGLRat N : Matrix (Fin 2) (Fin 2) ℚ).det := by
  refine ⟨transport N k f, transport_ne_zero N k hf, transport_apply N k f,
    ?_, qExpansion_transport N k f, rational_dilation_relation N k f,
    rational_dilation_det_pos N⟩
  intro c hc
  exact (transport N k f).zero_at_cusps' hc

end ZInQ.Contrib.HeckePrimeRationality.PrincipalCuspTransport
