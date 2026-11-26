import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.ConductorResidueUnits
import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.LocalEulerFactor
import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.FromCox

/-! The conductor product on the same order from the remaining residue identifications. -/

namespace HDec.CMBranch.FowlerArithmetic

open NumberField TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The global quotient and computed maximal-order residue count give Cox's product.
The remaining inputs identify the conductor kernel and count the order residue subgroup. -/
theorem coxConductorProduct_of_residue_identifications
    (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2)
    (hker : (conductorUnitsToPic O).ker =
      (maximalUnitsModConductor O).range ⊔ orderResidueUnitSubgroup O)
    (hOrder : Nat.card (orderResidueUnitSubgroup O) = O.index.totient) :
    CoxConductorProduct O := by
  have hCard : Nat.card (ClassGroup (𝓞 K)) = classNumber K := by
    rw [classNumber, Nat.card_eq_fintype_card]
  have h := card_pic_mul_orderResidueUnits_and_unit_index O hker
  rw [hOrder, hCard] at h
  change Nat.card (Pic O) * O.index.totient * quadraticOrderUnitIndex O = _ at h
  have hR : (Nat.card (Pic O) : ℝ) * (O.index.totient : ℝ) *
      (quadraticOrderUnitIndex O : ℝ) =
        (classNumber K : ℝ) * (Nat.card (𝓞 K ⧸ O.conductor)ˣ : ℝ) := by exact_mod_cast h
  rw [card_units_quotient_order_conductor_real O hK] at hR
  have ht : (O.index.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero O.index_ne_zero)).ne'
  refine ⟨quadraticSplittingSymbol K, fun p _ => quadraticSplittingSymbol_le_one (K := K) p, ?_⟩
  apply mul_right_cancel₀ ht
  calc
    (Nat.card (Pic O) : ℝ) * (quadraticOrderUnitIndex O : ℝ) * (O.index.totient : ℝ) =
        (Nat.card (Pic O) : ℝ) * (O.index.totient : ℝ) * (quadraticOrderUnitIndex O : ℝ) := by ring
    _ = (classNumber K : ℝ) * (O.index : ℝ) *
        (∏ p ∈ O.index.primeFactors, (1 - (quadraticSplittingSymbol K p : ℝ) / (p : ℝ))) *
        (O.index.totient : ℝ) := by rw [hR]; ring

end HDec.CMBranch.FowlerArithmetic
