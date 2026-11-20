import ZInQKernel.Contrib.OneProof.ConradRefereed.AbelianChar
import ZInQKernel.Contrib.TauCeti.RingTheory.Norm.Units

/-! Proof interface for the norm rewrite. `SerreA6NormEquivalence` below is an intermediate
Prop used only after the proof of the norm rewrite. The only printed input is
`LocalArtin.SerreA6Prop6`, which uses reciprocity at the ground field itself. -/

noncomputable section

namespace HDec.G0Galois.C8Conrad.SerreAppB

open HDec.G0Galois.C8Conrad.Bridges
open Module
open scoped TensorProduct Topology Filter

variable (p : ℕ) [Fact p.Prime]

/-- Admissibility after identifying the action of `G_K` with the fixing subgroup
in the common algebraic closure. -/
def SerreTwistAdmissible (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (ψ : PkgI4.GQp p →* Kˣ) (σ : K ≃ₐ[ℚ_[p]] K) (n : ℤ) : Prop :=
  ∃ x : ℂ_[p], x ≠ 0 ∧ ∀ g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p,
    _root_.ZInQ.Contrib.G9.PkgI4.cpAct p (restrictGalois p K g) x =
      (algebraMap K ℂ_[p] (σ ((ψ (restrictGalois p K g) : Kˣ) : K)))⁻¹ *
        algebraMap ℚ_[p] ℂ_[p] (_root_.ZInQ.Contrib.G9.PkgI4.cycPow p (restrictGalois p K g) n) * x

/-- The identity in condition (iv) after applying the proved norm functoriality
of the arithmetic Artin map. -/
def SerreA6NormForm (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ)
    (hc : Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p)))
    (n : (K ≃ₐ[ℚ_[p]] K) → ℤ) : Prop :=
  ∃ U : Subgroup Kˣ, IsOpen (U : Set Kˣ) ∧
    ∀ u ∈ U, ‖(((u : Kˣ) : K) : PadicAlgCl p)‖ = 1 ∧
      ((conradAbelianChar p ψ hc
          (TauCeti.ClassFieldTheory.artinMap ℚ_[p] (TauCeti.Algebra.normUnits ℚ_[p] u)) : Kˣ) : K) *
        ∏ σ : K ≃ₐ[ℚ_[p]] K, σ.symm ((u : Kˣ) : K) ^ n σ = 1

/-- Intermediate equivalence after the Artin norm rewrite. This is proved from
the integer-unit statement at the actual Artin map of `K`, with no additional input. -/
def SerreA6NormEquivalence : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ)
    (hc : Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p)))
    (n : (K ≃ₐ[ℚ_[p]] K) → ℤ),
    (∀ σ : K ≃ₐ[ℚ_[p]] K, SerreTwistAdmissible p K ψ σ (n σ)) ↔ SerreA6NormForm p K ψ hc n

end HDec.G0Galois.C8Conrad.SerreAppB
