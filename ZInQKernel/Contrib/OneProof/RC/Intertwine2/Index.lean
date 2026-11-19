import ZInQKernel.Contrib.OneProof.RC.Intertwine.AdelicFourier
import ZInQKernel.Contrib.OneProof.RC.Visibility.WeilIndex
import Mathlib.Algebra.BigOperators.Finprod

/-! The real factor and the statement of the missing global Weil index
reciprocity theorem (tex 8694–8695, 9000–9004, 9009–9011). No print is added. -/

noncomputable section

namespace ZInQ.Manuscript.RC.Intertwine2

open Intertwine OldStageLaw Visibility
open scoped BigOperators

abbrev FiniteIndexFamily := (p : Place) → ℚ_[p.val]ˣ → ℂˣ

def rationalDiagonal (a : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)] : List ℚˣ :=
  List.ofFn fun i => Units.mk0 (a i : ℚ) (by
    have h : a i ≠ 0 := fun h => NeZero.ne (2 * a i) (by simp [h])
    exact Nat.cast_ne_zero.mpr h)

def realIndex (q : List ℚˣ) : ℂˣ :=
  gammaDiag gammaReal (q.map (Units.map (algebraMap ℚ ℝ).toMonoidHom))

def indexAt (γ : FiniteIndexFamily) (q : List ℚˣ) (p : Place) : ℂˣ :=
  gammaDiag (γ p) (q.map (Units.map (algebraMap ℚ ℚ_[p.val]).toMonoidHom))

def finiteIndex (γ : FiniteIndexFamily) (q : List ℚˣ) : ℂˣ :=
  ∏ᶠ p, indexAt γ q p

/-- Missing theory, tex 9000–9004: for the actual local Weil indices of
`exp(-2πi {·}_p)`, the finite factors of any nonsingular rational diagonal
form are one almost everywhere, and their product times the real factor
for `exp(2πi ·)` is one. Weil, *Sur certains groupes d'opérateurs
unitaires*, Acta Math. 111 (1964), II.30, Proposition 5 (manuscript's
locator, independently UNVERIFIED). This is a hypothesis, not a print. -/
def WeilIndexProductFormula (γ : FiniteIndexFamily) : Prop :=
  ∀ q : List ℚˣ,
    (indexAt γ q).HasFiniteMulSupport ∧ realIndex q * finiteIndex γ q = 1

theorem realIndex_positive_ternary (a : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)] :
    realIndex (rationalDiagonal a) = zetaEight ^ 3 := by
  have h (i : Fin 3) : 0 < a i :=
    Nat.pos_of_ne_zero fun h => NeZero.ne (2 * a i) (by simp [h])
  have hγ (i : Fin 3) :
      gammaReal (Units.map (algebraMap ℚ ℝ).toMonoidHom
        (Units.mk0 (a i : ℚ) (Nat.cast_ne_zero.mpr (h i).ne'))) = zetaEight := by
    apply gammaReal_pos
    simpa using (Nat.cast_pos.mpr (h i) : (0 : ℝ) < a i)
  simp only [realIndex, rationalDiagonal, gammaDiag, List.map_ofFn]
  have hf : (gammaReal ∘ ⇑(Units.map (algebraMap ℚ ℝ).toMonoidHom) ∘
      fun i : Fin 3 => Units.mk0 (a i : ℚ) (Nat.cast_ne_zero.mpr (h i).ne')) =
      fun _ => zetaEight := funext hγ
  rw [hf, List.ofFn_const, List.prod_replicate]

theorem realIndex_reference (a : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)] :
    realIndex (rationalDiagonal a) = realIndex (rationalDiagonal referenceForm) := by
  rw [realIndex_positive_ternary, realIndex_positive_ternary]

theorem index_products (γ : FiniteIndexFamily) (hγ : WeilIndexProductFormula γ)
    (a : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)] :
    realIndex (rationalDiagonal a) * finiteIndex γ (rationalDiagonal a) = 1 ∧
      realIndex (rationalDiagonal a) * finiteIndex γ (rationalDiagonal referenceForm) = 1 := by
  exact ⟨(hγ _).2, realIndex_reference a ▸ (hγ (rationalDiagonal referenceForm)).2⟩

#print axioms realIndex_positive_ternary
#print axioms realIndex_reference
#print axioms index_products

end ZInQ.Manuscript.RC.Intertwine2
