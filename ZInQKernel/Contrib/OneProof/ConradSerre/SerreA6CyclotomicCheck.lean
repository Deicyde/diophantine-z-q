import Mathlib.RingTheory.Norm.Transitivity
import ZInQKernel.Contrib.OneProof.ConradSerre.LocalArtin
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Norm.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The cyclotomic character in Serre III-A6 (iv)

For constant weight one, the conjugate product is the norm and the cyclotomic value of the
arithmetic Artin symbol is its inverse. The identity holds on all integer units.
-/

noncomputable section
namespace HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin

open _root_.ZInQ.Contrib.G9.PkgI4 (GQp)
open scoped BigOperators

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

private def padicIntUnitsToK : ℤ_[p]ˣ →* Kˣ :=
  (Units.map (algebraMap ℚ_[p] K).toMonoidHom).comp
    (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom)

/-- Tau Ceti's local cyclotomic character, viewed in the coefficient field. -/
def cyclotomicCharacterToK : GQp p →* Kˣ :=
  (padicIntUnitsToK p K).comp (TauCeti.localCyclotomicCharacter p ℚ_[p])

theorem cyclotomicCharacterToK_continuous :
    Continuous (fun g => (((cyclotomicCharacterToK p K g : Kˣ) : K) : PadicAlgCl p)) := by
  change Continuous (fun g : GQp p => algebraMap ℚ_[p] (PadicAlgCl p)
    ((TauCeti.localCyclotomicCharacter p ℚ_[p] g : ℤ_[p]) : ℚ_[p]))
  have hcoe : Continuous (fun z : ℤ_[p] => (z : ℚ_[p])) := continuous_subtype_val
  have hval : Continuous (fun w : ℤ_[p]ˣ => (w : ℤ_[p])) := Units.continuous_val
  exact (continuous_algebraMap ℚ_[p] (PadicAlgCl p)).comp
    (hcoe.comp (hval.comp (TauCeti.localCyclotomicCharacter_continuous p ℚ_[p])))

private theorem norm_serreUnits_valuation [FiniteDimensional ℚ_[p] K]
    (u : serreUnits p K) : (TauCeti.Algebra.normUnits ℚ_[p] u.val : ℚ_[p]).valuation = 0 := by
  let _ := TauCeti.finiteIntermediateFieldValuativeRel ℚ_[p] (PadicAlgCl p) K
  let _ := TauCeti.finiteIntermediateFieldTopology ℚ_[p] (PadicAlgCl p) K
  let _ := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField ℚ_[p] (PadicAlgCl p) K
  have := TauCeti.finiteIntermediateField_valuativeExtension ℚ_[p] (PadicAlgCl p) K
  have hu : u.val ∈ TauCeti.unitFiltration K 0 := u.property
  rw [← Padic.toAdd_normalizedValuation_eq_valuation,
    TauCeti.normalizedValuation_norm_eq_one_of_eq_one u.val
      ((TauCeti.normalizedValuation_eq_one_iff u.val).2
        ((TauCeti.mem_unitFiltration_zero u.val).1 hu)), toAdd_one]

/-- Serre III-A6 (iv) for the cyclotomic character at constant weight one. -/
theorem serreA6_integerUnits_cyclotomic [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K] :
    serreConditionIVUnits p K (cyclotomicCharacterToK p K)
      (cyclotomicCharacterToK_continuous p K) (fun _ => 1) := by
  let _ : T1Space Kˣ :=
    (show Topology.IsEmbedding ((↑) : Kˣ → K) from Units.isEmbedding_val₀).t1Space
  unfold serreConditionIVUnits
  refine ⟨⊤, by simp, fun u _ => ?_⟩
  simp only [restrictCharacter, character_norm, zpow_one]
  let x := TauCeti.Algebra.normUnits ℚ_[p] u.val
  obtain ⟨w, hw⟩ := Padic.exists_eq_zpow_valuation_mul (Units.ne_zero x)
  rw [norm_serreUnits_valuation p K u, zpow_zero, one_mul] at hw
  have hlift (a : Field.absoluteGaloisGroupAbelianization ℚ_[p]) :
      TopologicalAbelianization.lift (continuousCharacter p K (cyclotomicCharacterToK p K)
          (cyclotomicCharacterToK_continuous p K)) a =
        padicIntUnitsToK p K (TauCeti.abelianizedLocalCyclotomicCharacter p ℚ_[p] a) := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    rw [TopologicalAbelianization.lift_mk, TauCeti.abelianizedLocalCyclotomicCharacter_mk]
    rfl
  have hχ := TauCeti.ClassFieldTheory.abelianizedLocalCyclotomicCharacter_artinMap_padic p
    (x := x) (k := 0) (u := w) (by simpa only [zpow_zero, one_mul] using hw)
  have hprod :
      (∏ σ : K ≃ₐ[ℚ_[p]] K, σ.symm (u.val : K)) = algebraMap ℚ_[p] K (x : ℚ_[p]) := by
    rw [TauCeti.Algebra.coe_normUnits, Algebra.norm_eq_prod_automorphisms]
    have hinv : Function.Involutive (fun σ : K ≃ₐ[ℚ_[p]] K => σ.symm) :=
      AlgEquiv.symm_symm
    exact Equiv.prod_comp (hinv.toPerm _) (fun σ => σ (u.val : K))
  have hnorm : (padicIntUnitsToK p K w : K) = algebraMap ℚ_[p] K (x : ℚ_[p]) :=
    congrArg (algebraMap ℚ_[p] K) hw.symm
  rw [hlift, hχ, hprod, ← hnorm, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
    Units.val_one]

#print axioms serreA6_integerUnits_cyclotomic

end HDec.G0Galois.C8Conrad.SerreAppB.LocalArtin
