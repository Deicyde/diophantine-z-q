import BridgeDenominatorV002
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionData

/-!
# Actual raw torsion forms, diamonds, and coefficient conjugation

The weight-one form is the unchanged torsion logarithmic derivative at
(0,1), not a derivative-scale multiple. Every unit translate is the actual
Gamma-one diamond. The cyclotomic automorphism unit is produced from the
proved torsion dictionary, with the lower-right representative convention.
All product transport below uses determinant-one integral slashing.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm BigOperators

namespace BridgeLambda

open ZInQ.Contrib.HeckePrimeRationality
open DirectTorsionOrbit

/-- Admissibility of the raw primitive axis label. -/
theorem base_admissible (N : ℕ) [NeZero N] (hN : 3 ≤ N) : ¬ (N : ℤ) ∣ 1 :=
  fun h => base_good N hN ⟨dvd_zero _, h⟩

/-- The genuine unscaled weight-one Gamma-one form. -/
def baseLambda (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) 1 :=
  AllLevelForms.torsionForm N (NeZero.pos N) 1 (base_admissible N hN)

/-- Its analytic function is exactly the raw torsion logarithmic derivative used in localization. -/
theorem baseLambda_coe (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    ⇑(baseLambda N hN) = Torsion.torsionLogDerivative N 0 1 := rfl

/-- The actual unit-indexed raw torsion orbit on Gamma-one. -/
def lambdaForm (N : ℕ) [NeZero N] (hN : 3 ≤ N) (u : (ZMod N)ˣ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) 1 :=
  diamondOp 1 u (baseLambda N hN)

/-- The identity unit recovers the original form. -/
theorem lambdaForm_one (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    lambdaForm N hN 1 = baseLambda N hN := by
  simp [lambdaForm]

/-- Diamonds compose according to the actual unit multiplication. -/
theorem diamond_lambdaForm (N : ℕ) [NeZero N] (hN : 3 ≤ N) (u v : (ZMod N)ˣ) :
    diamondOp 1 u (lambdaForm N hN v) = lambdaForm N hN (u * v) := by
  simp only [lambdaForm, diamondOp_mul, LinearMap.comp_apply]

/-- The exact scalar-ring maps defining the two actual slash notations agree. -/
theorem real_slash_eq_integral (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) :
    f ∣[k] mapGL ℝ γ = f ∣[k] γ := by
  rw [ModularForm.SL_slash]
  rfl

/-- A restricted actual level-one form is fixed by every actual Gamma-one diamond. -/
theorem diamond_restrictLevelOne (N : ℕ) (k : ℤ) (u : (ZMod N)ˣ)
    (f : ModularForm 𝒮ℒ k) :
    diamondOp k u (BridgeDenominator.restrictLevelOne N k f) =
      BridgeDenominator.restrictLevelOne N k f := by
  obtain ⟨γ, hγ⟩ := Gamma0Map_toHomUnits_surjective (N := N) u
  apply DFunLike.coe_injective
  rw [coe_diamondOp k u γ hγ]
  exact SlashInvariantFormClass.slash_action_eq f _ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)

/-- Multiplication transport is the determinant-one SL product law, not a general GL identity. -/
theorem diamond_mul {N : ℕ} {a b : ℤ} (u : (ZMod N)ˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) a)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) b) :
    diamondOp (a + b) u (f.mul g) = (diamondOp a u f).mul (diamondOp b u g) := by
  obtain ⟨γ, hγ⟩ := Gamma0Map_toHomUnits_surjective (N := N) u
  apply DFunLike.coe_injective
  rw [coe_diamondOp (a + b) u γ hγ, ModularForm.coe_mul,
    ModularForm.coe_mul, coe_diamondOp a u γ hγ, coe_diamondOp b u γ hγ,
    real_slash_eq_integral, real_slash_eq_integral, real_slash_eq_integral]
  exact ModularForm.mul_slash_SL2 a b (γ : SL(2, ℤ)) f g

/-- Powers of the actual weight-one unit form with the exact natural weight cast. -/
def unitPower (N : ℕ) [NeZero N] (hN : 3 ≤ N) (u : (ZMod N)ˣ) (j : ℕ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) (j : ℤ) :=
  ModularForm.mcast (by ring) ((lambdaForm N hN u).pow j)

/-- The actual Fourier series of the power is the formal power of the actual unit-form series. -/
theorem unitPower_qExpansion (N : ℕ) [NeZero N] (hN : 3 ≤ N) (u : (ZMod N)ˣ) (j : ℕ) :
    qExpansion 1 (unitPower N hN u j) = (qExpansion 1 (lambdaForm N hN u)) ^ j := by
  simp only [unitPower, ModularForm.coe_mcast]
  exact ModularForm.qExpansion_pow one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N) _ j

/-- The actual unit power is transported to the product unit, at the same fixed weight. -/
theorem diamond_unitPower (N : ℕ) [NeZero N] (hN : 3 ≤ N) (u v : (ZMod N)ˣ) (j : ℕ) :
    diamondOp (j : ℤ) u (unitPower N hN v j) = unitPower N hN (u * v) j := by
  obtain ⟨γ, hγ⟩ := Gamma0Map_toHomUnits_surjective (N := N) u
  apply ModularForm.ext
  intro τ
  rw [coe_diamondOp (j : ℤ) u γ hγ, real_slash_eq_integral]
  simp only [unitPower, ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply,
    ModularForm.SL_slash_apply]
  have he : lambdaForm N hN (u * v) τ =
      (lambdaForm N hN v) ((γ : SL(2, ℤ)) • τ) * denom (γ : SL(2, ℤ)) τ ^ (-1 : ℤ) := by
    rw [← diamond_lambdaForm, coe_diamondOp 1 u γ hγ, real_slash_eq_integral,
      ModularForm.SL_slash_apply]
  rw [he, mul_pow]
  have hd : (denom (γ : SL(2, ℤ)) τ ^ (-1 : ℤ)) ^ j =
      denom (γ : SL(2, ℤ)) τ ^ (-(j : ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [hd]

/-- Every actual unit translate has cyclotomic period-one coefficients. -/
theorem lambdaForm_coefficients_mem (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (u : (ZMod N)ˣ) (n : ℕ) :
    (qExpansion 1 (lambdaForm N hN u)).coeff n ∈ Torsion.coefficientField N := by
  obtain ⟨γ, hγ⟩ := Gamma0Map_toHomUnits_surjective (N := N) u
  rw [lambdaForm, baseLambda, AllLevelTorsionData.diamond_torsionForm N u γ hγ]
  exact AllLevelTorsionData.torsionForm_coeff_mem N _ _ n

/-- Every coefficient-field automorphism produces one genuine cyclotomic unit,
realizing coefficient conjugation simultaneously on every actual unit translate. -/
theorem exists_galois_unit (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (σ : Torsion.coefficientField N ≃ₐ[ℚ] Torsion.coefficientField N) :
    ∃ s : (ZMod N)ˣ, ∀ (u : (ZMod N)ˣ) (n : ℕ),
      (σ (⟨(qExpansion 1 (lambdaForm N hN u)).coeff n,
        lambdaForm_coefficients_mem N hN u n⟩ : Torsion.coefficientField N) : ℂ) =
          (qExpansion 1 (lambdaForm N hN (s * u))).coeff n := by
  obtain ⟨s, hs⟩ := AllLevelTorsionData.galois_diamond_dictionary N σ
  refine ⟨s, ?_⟩
  intro u n
  obtain ⟨γ, hγ⟩ := Gamma0Map_toHomUnits_surjective (N := N) u
  let b : ℤ := (γ : SL(2, ℤ)) 1 1 * 1
  have hb : ¬ (N : ℤ) ∣ b :=
    AllLevelTorsionData.representative_admissible N γ 1 (base_admissible N hN)
  have hform : lambdaForm N hN u = AllLevelForms.torsionForm N (NeZero.pos N) b hb := by
    rw [lambdaForm, baseLambda]
    exact AllLevelTorsionData.diamond_torsionForm N u γ hγ 1 (base_admissible N hN)
  have hlift : (⟨(qExpansion 1 (lambdaForm N hN u)).coeff n,
      lambdaForm_coefficients_mem N hN u n⟩ : Torsion.coefficientField N) =
      ⟨(qExpansion 1 (AllLevelForms.torsionForm N (NeZero.pos N) b hb)).coeff n,
        AllLevelTorsionData.torsionForm_coeff_mem N b hb n⟩ := by
    apply Subtype.ext
    change (qExpansion 1 (lambdaForm N hN u)).coeff n =
      (qExpansion 1 (AllLevelForms.torsionForm N (NeZero.pos N) b hb)).coeff n
    exact congrArg (fun f : ModularForm ((Gamma1 N).map (mapGL ℝ)) 1 =>
      (qExpansion 1 f).coeff n) hform
  calc
    (σ (⟨(qExpansion 1 (lambdaForm N hN u)).coeff n,
        lambdaForm_coefficients_mem N hN u n⟩ : Torsion.coefficientField N) : ℂ) =
        (σ (⟨(qExpansion 1 (AllLevelForms.torsionForm N (NeZero.pos N) b hb)).coeff n,
          AllLevelTorsionData.torsionForm_coeff_mem N b hb n⟩ : Torsion.coefficientField N) : ℂ) := by rw [hlift]
    _ = (qExpansion 1 (diamondOp 1 s (AllLevelForms.torsionForm N (NeZero.pos N) b hb))).coeff n := hs b hb n
    _ = (qExpansion 1 (diamondOp 1 s (lambdaForm N hN u))).coeff n := by rw [hform]
    _ = (qExpansion 1 (lambdaForm N hN (s * u))).coeff n := by rw [diamond_lambdaForm]

end BridgeLambda
