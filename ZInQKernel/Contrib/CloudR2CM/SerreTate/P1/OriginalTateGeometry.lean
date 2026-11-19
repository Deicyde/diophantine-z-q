import ZInQKernel.Contrib.OneProof.UniformizationLeafAll
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed
import ZInQKernel.Contrib.OneProof.HomFreeFiniteAlgClosed
import ZInQKernel.OneProof.H.LF4T5
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Geometric Tate rank and completed Hom faithfulness

The original torsion and uniformization theorems supply their full
conclusions. Freeness, the geometric rank formula and the completed Hom
injection are derived here, not supplied as additional hypotheses.
-/

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj TensorProduct

namespace HDec.CMSerreTate.P1

/-- The full original Tate freeness and rank theorem follows from the
actual Mumford torsion theorem through the original T5 construction. -/
theorem originalTateModuleFree_proved : _root_.PkgI3.TateModuleFree :=
  _root_.T5Torsion.TateFree.tateModuleFree_of_torsionStructure
    (_root_.AvSplit.torsionStructure_of_mumford
      _root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof)

/-- The original number-field Hom theorem is supplied by the actual
uniformization and Mumford theorems, with no new leaf premise. -/
theorem originalHomFreeFiniteNF_proved :
    _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteNF :=
  _root_.ZInQ.Contrib.OneProof.HomFreeC.homFreeFiniteNF
    _root_.uniformizationLeafAll_proof
    _root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof

/-- Faithfulness of the original completed Hom action over a number
field. This is the full completion, not only the action of individual
endomorphisms before scalar extension. -/
theorem original_tateHomZl_injective {K : Type} [Field K] [NumberField K]
    (A B : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) :
    Function.Injective (_root_.PkgI3.AbVar.tateHomZl ℓ A B) :=
  (originalHomFreeFiniteNF_proved K A B).2.2.2 ℓ hℓ

/-- Geometric rank two for the same integral Tate module of an elliptic
curve, with actual freeness and finiteness included. -/
theorem original_integral_tate_rank_two {K : Type} [Field K] [NumberField K]
    (A : _root_.PkgI3.AbVar K) (hA : A.dim = 1) (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.Free ℤ_[ℓ] (A.T ℓ) ∧ Module.Finite ℤ_[ℓ] (A.T ℓ) ∧
      Module.finrank ℤ_[ℓ] (A.T ℓ) = 2 := by
  have hℓ : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hFree, hFinite, hRank⟩ := originalTateModuleFree_proved K A ℓ hℓ
  refine ⟨hFree, hFinite, ?_⟩
  have hRank' : ((Module.finrank ℤ_[ℓ] (A.T ℓ) : ℕ∞) : WithBot ℕ∞) = 2 := by
    simpa only [hA, mul_one] using hRank
  exact WithTop.coe_inj.mp (WithBot.coe_inj.mp hRank')

/-- Scalar extension preserves the derived geometric rank of the
original Tate lattice. -/
theorem original_rational_tate_rank_two {K : Type} [Field K] [NumberField K]
    (A : _root_.PkgI3.AbVar K) (hA : A.dim = 1) (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.finrank ℚ_[ℓ] (A.V ℓ) = 2 := by
  obtain ⟨hFree, hFinite, hRank⟩ := original_integral_tate_rank_two A hA ℓ
  letI : Module.Free ℤ_[ℓ] (A.T ℓ) := hFree
  letI : Module.Finite ℤ_[ℓ] (A.T ℓ) := hFinite
  change Module.finrank ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] A.T ℓ) = 2
  rw [Module.finrank_baseChange]
  exact hRank

end HDec.CMSerreTate.P1
