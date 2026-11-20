import ZInQKernel.Contrib.OneProof.RC.CMField2.CosetLattice
import ZInQKernel.Contrib.OneProof.RC.CMField2.Degree
import ZInQKernel.Contrib.OneProof.RC.CMField2.IdealDictionary

/-! The remaining exact-order comparison in the modular-polynomial approach (c). -/

noncomputable section
open NumberField Module ModularCurve Polynomial TauCeti.GlobalNumberFields

namespace ZInQ.Manuscript.RC.CMField2

/-- The full sequence of specialized diagonal multiplicities of a proper
ideal lattice determines its exact complex multiplier order. -/
def ExactMultiplierOrderOfDiagonalMultiplicities : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : NumberFieldOrder K)
    (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K) (κ : K →+* ℂ)
    (I : O.invertibleProperFractionalIdeals) (L : PeriodPair),
    (∀ (m : ℕ) [NeZero m] (P : ModularPolynomialData m),
      let j := singularModulus O hk hc κ I
      rootMultiplicity j (P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) j)) =
      rootMultiplicity L.jLattice (P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) L.jLattice))) →
    ∀ z : ℂ, (∀ w ∈ L.lattice, z * w ∈ L.lattice) ↔ z ∈ κ '' (O.toSubalgebra : Set K)

/-- The exact-order comparison yields the conjugacy input to the degree bound.
Preservation of multiplicity and the passage to a proper ideal are proved separately. -/
theorem conjugateSingularModulus_of_exactMultiplier
    (h : ExactMultiplierOrderOfDiagonalMultiplicities) : ConjugateSingularModulus := by
  intro K _ _ O hk hc κ I σ
  let j := singularModulus O hk hc κ I
  let x := IntermediateField.AdjoinSimple.gen ℚ j
  let ι := (IntermediateField.adjoin ℚ {j}).val.toRingHom
  obtain ⟨L, _, hL⟩ := PeriodPair.jLattice_surjective (σ x)
  have hmul := h K O hk hc κ I L (fun m _ P => by
    rw [hL]
    exact rootMultiplicity_specialization_eq_of_embeddings P.Φ ι σ.toRingHom x)
  obtain ⟨J, hJ⟩ := exists_singularModulus_of_exact_multiplier O hk hc κ L hmul
  exact ⟨J, hL.symm.trans hJ⟩


end ZInQ.Manuscript.RC.CMField2
