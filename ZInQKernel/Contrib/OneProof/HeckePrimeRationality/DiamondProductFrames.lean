import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelPrincipalForms
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCoefficients
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.DiamondOperators

/-!
# Analytic and field frames for diamond descent

Finite special-linear slash covariance preserves complex coordinates. Corrected
representatives with the same diamond label act identically on a Gamma-one form.
An element of the actual cyclotomic coefficient field fixed by all its rational
automorphisms is rational.
-/

set_option autoImplicit false
noncomputable section
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace DiamondProductFrames

/-- Termwise special-linear covariance extends to an actual finite combination. -/
theorem finite_sum_slash_of_termwise
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {J : Type*} [Fintype J]
    (k : ℤ) (F G : J → _root_.ModularForm Γ k) (c : J → ℂ) (γ : SL(2, ℤ))
    (hFG : ∀ j, ⇑(F j) ∣[k] γ = ⇑(G j)) :
    ⇑(∑ j, c j • F j : _root_.ModularForm Γ k) ∣[k] γ =
      ⇑(∑ j, c j • G j : _root_.ModularForm Γ k) := by
  classical
  rw [FunLike.coe_sum, FunLike.coe_sum, SlashAction.sum_slash]
  apply Finset.sum_congr rfl
  intro j _
  rw [FunLike.coe_smul, FunLike.coe_smul, _root_.ModularForm.SL_smul_slash, hFG j]

/-- The corrected representative has the same action on an actual Gamma-one form. -/
theorem gammaT_slash_eq
    (N : ℕ) (k : ℤ) (g : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (t : ℤ) (γ : Gamma0 N) :
    ⇑g ∣[k] ZInQ.Contrib.HeckePrimeRationality.AllLevelPrincipal.gammaT t (γ : SL(2, ℤ)) =
      ⇑g ∣[k] (γ : SL(2, ℤ)) := by
  change ⇑g ∣[k] mapGL ℝ
    (ZInQ.Contrib.HeckePrimeRationality.AllLevelPrincipal.gammaT t (γ : SL(2, ℤ))) =
      ⇑g ∣[k] mapGL ℝ (γ : SL(2, ℤ))
  exact slash_eq_of_Gamma0Map_eq
    (fun a ha => SlashInvariantFormClass.slash_action_eq g a ha)
    ⟨_, ZInQ.Contrib.HeckePrimeRationality.AllLevelPrincipal.gammaT_mem_Gamma0 t γ.property⟩ γ
    (ZInQ.Contrib.HeckePrimeRationality.AllLevelPrincipal.gammaT_label t γ.property)

/-- Fixedness in the specified finite cyclotomic field gives an actual rational complex value. -/
theorem rational_of_fixed
    (N : ℕ) [NeZero N] (a : ℂ)
    (ha : a ∈ ZInQ.Contrib.HeckePrimeRationality.Torsion.coefficientField N)
    (hfixed : ∀ σ : ZInQ.Contrib.HeckePrimeRationality.Torsion.coefficientField N ≃ₐ[ℚ]
      ZInQ.Contrib.HeckePrimeRationality.Torsion.coefficientField N,
      σ (⟨a, ha⟩ : ZInQ.Contrib.HeckePrimeRationality.Torsion.coefficientField N) =
        (⟨a, ha⟩ : ZInQ.Contrib.HeckePrimeRationality.Torsion.coefficientField N)) :
    ∃ q : ℚ, a = (q : ℂ) := by
  let K : IntermediateField ℚ ℂ := ZInQ.Contrib.HeckePrimeRationality.Torsion.coefficientField N
  let x : K := ⟨a, ha⟩
  have hx : x ∈ Set.range (algebraMap ℚ K) :=
    (IsGalois.mem_range_algebraMap_iff_fixed x).mpr hfixed
  obtain ⟨q, hq⟩ := hx
  refine ⟨q, ?_⟩
  have hqC := congrArg (fun z : K => (z : ℂ)) hq
  have hqmap := (Rat.castHom ℂ).map_rat_algebraMap q
  change (q : ℂ) = algebraMap ℚ ℂ q at hqmap
  have he : algebraMap ℚ ℂ q = a := by
    simpa only [IntermediateField.coe_algebraMap_apply] using hqC
  exact (hqmap.trans he).symm

end DiamondProductFrames
