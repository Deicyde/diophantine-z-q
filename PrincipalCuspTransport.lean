import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Degeneracy

/-!
# Principal cusp forms at square level

Dilation by a positive level transports an actual principal cusp form to the
square-level Gamma-one cusp space. The determinant factor uses integer powers.
All cusp conditions are inherited through actual translation and restriction.
-/

noncomputable section
set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.PrincipalCuspTransport

/-- The dilation-conjugate of a square-level Gamma-one matrix is principal. -/
theorem square_level_conjugation (N : ℕ) [NeZero N] {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma1 (N ^ 2)) :
    TauCeti.scaleGL N * mapGL ℝ γ * (TauCeti.scaleGL N)⁻¹ ∈
      (Gamma N).map (mapGL ℝ) := by
  obtain ⟨t, ht⟩ := mem_Gamma0_iff_dvd.mp (Gamma1_in_Gamma0 (N ^ 2) hγ)
  have hc : γ 1 0 = (N : ℤ) * ((N : ℤ) * t) := by
    rw [ht]
    push_cast
    ring
  have hNN : N ∣ N ^ 2 := by rw [pow_two]; exact dvd_mul_right N N
  have hd := (Gamma1_mem N γ).mp (Gamma1_le_Gamma1_of_dvd hNN hγ)
  refine Subgroup.mem_map.mpr ⟨TauCeti.conjScale N γ ((N : ℤ) * t) hc, ?_,
    (TauCeti.mapGL_conjScale γ ((N : ℤ) * t) hc).symm⟩
  rw [Gamma_mem]
  simpa [TauCeti.coe_conjScale] using
    (show ((γ 0 0 : ℤ) : ZMod N) = 1 ∧
      (((N : ℤ) * γ 0 1 : ℤ) : ZMod N) = 0 ∧
      (((N : ℤ) * t : ℤ) : ZMod N) = 0 ∧
      ((γ 1 1 : ℤ) : ZMod N) = 1 from ⟨hd.1, by simp, by simp, hd.2.1⟩)

/-- The actual subgroup inclusion needed by cusp-form translation. -/
theorem square_level_group_le (N : ℕ) [NeZero N] :
    (Gamma1 (N ^ 2)).map (mapGL ℝ) ≤
      ConjAct.toConjAct (TauCeti.scaleGL N)⁻¹ • (Gamma N).map (mapGL ℝ) := by
  rintro _ ⟨γ, hγ, rfl⟩
  rw [TauCeti.mem_conjAct_inv_scaleGL_iff]
  exact square_level_conjugation N hγ

/-- The actual square-level cusp carrier, with the raw slash normalized by N^(1-k). -/
def transport (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    CuspForm ((Gamma1 (N ^ 2)).map (mapGL ℝ)) k :=
  TauCeti.CuspForm.levelRaise N (square_level_group_le N) f

/-- Dilation preserves the weight and has no residual factor on pointwise values. -/
theorem transport_apply (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (τ : ℍ) :
    transport N k f τ = f (TauCeti.scaleGL N • τ) :=
  TauCeti.CuspForm.levelRaise_apply (square_level_group_le N) f τ

/-- Dilation by N is multiplication of the actual upper-half-plane coordinate by N. -/
theorem dilation_coe (N : ℕ) [NeZero N] (τ : ℍ) :
    ((TauCeti.scaleGL N • τ : ℍ) : ℂ) = (N : ℂ) * τ :=
  TauCeti.coe_scaleGL_smul τ

/-- The cusp carrier retains the exact determinant normalization for all integer weights. -/
theorem transport_coe (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    ⇑(transport N k f) = (N : ℂ) ^ (1 - k) • (⇑f ∣[k] TauCeti.scaleGL N) :=
  TauCeti.CuspForm.coe_levelRaise (square_level_group_le N) f

/-- The unnormalized slash introduces precisely N^(k-1). -/
theorem raw_slash_eq_transport (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    ⇑f ∣[k] TauCeti.scaleGL N = (N : ℂ) ^ (k - 1) • ⇑(transport N k f) := by
  funext τ
  rw [TauCeti.slash_scaleGL_apply, Pi.smul_apply, smul_eq_mul, transport_apply]

/-- The normalizing power cannot vanish, even at negative integer weights. -/
theorem normalization_ne_zero (N : ℕ) [NeZero N] (k : ℤ) :
    (N : ℂ) ^ (1 - k) ≠ 0 :=
  zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne N))

/-- Dilation is injective on actual cusp forms, by evaluating at the inverse dilation. -/
theorem transport_injective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Injective (transport N k) :=
  TauCeti.CuspForm.levelRaise_injective (square_level_group_le N)

/-- The zero form is preserved. -/
theorem transport_zero (N : ℕ) [NeZero N] (k : ℤ) : transport N k 0 = 0 := by
  ext τ
  simp [transport_apply]

/-- Nonvanishing of an actual principal cusp form survives in the square-level carrier. -/
theorem transport_ne_zero (N : ℕ) [NeZero N] (k : ℤ)
    {f : CuspForm ((Gamma N).map (mapGL ℝ)) k} (hf : f ≠ 0) :
    transport N k f ≠ 0 := by
  intro h
  exact hf (transport_injective N k (h.trans (transport_zero N k).symm))

/-- The actual complex-linear cusp transport. -/
def transportLinear (N : ℕ) [NeZero N] (k : ℤ) :
    CuspForm ((Gamma N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma1 (N ^ 2)).map (mapGL ℝ)) k :=
  TauCeti.CuspForm.levelRaiseₗ N (square_level_group_le N)

/-- The positive rational dilation matrix, read in the real slash-action group. -/
theorem rational_dilation_relation (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    ⇑(transport N k f) = (N : ℂ) ^ (1 - k) •
      (⇑f ∣[k] GeneralLinearGroup.map (algebraMap ℚ ℝ) (TauCeti.scaleGLRat N)) := by
  rw [TauCeti.map_ratCast_scaleGLRat]
  exact transport_coe N k f

/-- The rational matrix has strictly positive determinant. -/
theorem rational_dilation_det_pos (N : ℕ) [NeZero N] :
    0 < ((TauCeti.scaleGLRat N : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  simp only [TauCeti.scaleGLRat, TauCeti.diagGL_coe, Matrix.diagonal_fin_two]
  simpa using (show (0 : ℚ) < N from by exact_mod_cast NeZero.pos N)

end ZInQ.Contrib.HeckePrimeRationality.PrincipalCuspTransport
