import ZInQKernel.HDecomp.Textbook.Igusa.Generic

/-!
# T28: the split of `IgusaSeparationEq` into the generic and the special locus

Task igusa-generic (owner of this file). Textbook leaf T28 (`PkgI1.IgusaClebschSeparation`) is
equivalent to `PkgI1.IgusaSeparationEq` (`PkgI1.igusaClebschSeparation_iff`, task t28-igusa).
This file fixes the split of `IgusaSeparationEq` between the two tasks that prove it:

* the **generic locus** `T28.GenericLocus f`: Clebsch's three quadratic covariants
  `y₁ = (f,i)₄, y₂ = (i,y₁)₂, y₃ = (i,y₂)₂` (`PkgI1.yv f`) are linearly independent, i.e.
  `det (yv f) ≠ 0` (Clebsch's `R ≠ 0`; on this locus the curve has no automorphism besides the
  hyperelliptic involution, Bolza 1888). Statement `T28.SeparationGeneric`, task igusa-generic
  (Mestre's reconstruction).
* the **special locus** `¬ T28.GenericLocus f`, i.e. `det (yv f) = 0`. Statement
  `T28.SeparationSpecialLocus` (identical to `PkgI1.SeparationSpecial`), task igusa-special.

`T28.igusaSeparationEq_of_split` and `T28.igusaClebschSeparation_of_split` combine them.
No `sorry`, no `axiom`.
-/

namespace T28
open PkgI1

/-- The generic locus: Clebsch's quadratic covariants `yv f` form a basis of binary quadratics. -/
def GenericLocus {L : Type*} [Field L] (f : Fin 7 → L) : Prop :=
  (Matrix.of (yv f)).det ≠ 0

/-- `IgusaSeparationEq` on the generic locus (task igusa-generic). -/
def SeparationGeneric : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharZero L] (f g : Fin 7 → L),
    J10 f ≠ 0 → J10 g ≠ 0 → GenericLocus f →
      J2 g = J2 f → J4 g = J4 f → J6 g = J6 f → J10 g = J10 f →
        ∃ M : Matrix (Fin 2) (Fin 2) L, M.det ≠ 0 ∧ ∃ e : L, e ≠ 0 ∧ g = sexticAct f M e

/-- `IgusaSeparationEq` on the special locus `det (yv f) = 0` (task igusa-special). -/
def SeparationSpecialLocus : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharZero L] (f g : Fin 7 → L),
    J10 f ≠ 0 → J10 g ≠ 0 → ¬ GenericLocus f →
      J2 g = J2 f → J4 g = J4 f → J6 g = J6 f → J10 g = J10 f →
        ∃ M : Matrix (Fin 2) (Fin 2) L, M.det ≠ 0 ∧ ∃ e : L, e ≠ 0 ∧ g = sexticAct f M e

theorem separationSpecialLocus_iff : SeparationSpecialLocus ↔ SeparationSpecial := by
  unfold SeparationSpecialLocus SeparationSpecial GenericLocus
  simp only [not_not]

/-- The two halves give `IgusaSeparationEq`. -/
theorem igusaSeparationEq_of_split (hG : SeparationGeneric) (hS : SeparationSpecialLocus) :
    IgusaSeparationEq := by
  intro L _ _ _ f g hf hg h2 h4 h6 h10
  by_cases hy : GenericLocus f
  · exact hG L f g hf hg hy h2 h4 h6 h10
  · exact hS L f g hf hg hy h2 h4 h6 h10

/-- The two halves give the leaf T28. -/
theorem igusaClebschSeparation_of_split (hG : SeparationGeneric) (hS : SeparationSpecialLocus) :
    IgusaClebschSeparation :=
  igusaClebschSeparation_iff.mpr (igusaSeparationEq_of_split hG hS)

/-- Equivalence of sextics is symmetric. -/
theorem sexticAct_symm {L : Type*} [Field L] (f g : Fin 7 → L) (M : Matrix (Fin 2) (Fin 2) L)
    (hM : M.det ≠ 0) (e : L) (he : e ≠ 0) (h : g = sexticAct f M e) :
    ∃ M' : Matrix (Fin 2) (Fin 2) L, M'.det ≠ 0 ∧ ∃ e' : L, e' ≠ 0 ∧ f = sexticAct g M' e' := by
  rw [Matrix.det_fin_two] at hM
  refine ⟨!![M 1 1, -M 0 1; -M 1 0, M 0 0], ?_, (e * (M 0 0 * M 1 1 - M 0 1 * M 1 0) ^ 6)⁻¹,
    inv_ne_zero (mul_ne_zero he (pow_ne_zero 6 hM)), ?_⟩
  · rw [Matrix.det_fin_two_of]; intro h0; apply hM; linear_combination h0
  · have key : ∀ δ E : L, actC f δ 0 0 δ E = fun i => E * δ ^ 6 * f i := by
      intro δ E; funext i; fin_cases i <;> simp [actC] <;> ring
    rw [h, sexticAct_eq, sexticAct_eq, actC_actC]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    set δ := M 0 0 * M 1 1 - M 0 1 * M 1 0 with hδ
    rw [show M 0 0 * M 1 1 + M 0 1 * -M 1 0 = δ by rw [hδ]; ring,
      show M 0 0 * -M 0 1 + M 0 1 * M 0 0 = 0 by ring,
      show M 1 0 * M 1 1 + M 1 1 * -M 1 0 = 0 by ring,
      show M 1 0 * -M 0 1 + M 1 1 * M 0 0 = δ by rw [hδ]; ring, key]
    funext i
    field_simp

/-- The special locus as task igusa-special states it: both sextics special. -/
def SeparationBothSpecial : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharZero L] (f g : Fin 7 → L),
    J10 f ≠ 0 → J10 g ≠ 0 → (Matrix.of (yv f)).det = 0 → (Matrix.of (yv g)).det = 0 →
      J2 g = J2 f → J4 g = J4 f → J6 g = J6 f → J10 g = J10 f →
        ∃ M : Matrix (Fin 2) (Fin 2) L, M.det ≠ 0 ∧ ∃ e : L, e ≠ 0 ∧ g = sexticAct f M e

/-- The generic half and the both-special half give `IgusaSeparationEq`. -/
theorem igusaSeparationEq_of_generic_bothSpecial (hG : SeparationGeneric)
    (hS : SeparationBothSpecial) : IgusaSeparationEq := by
  intro L _ _ _ f g hf hg h2 h4 h6 h10
  by_cases hyf : GenericLocus f
  · exact hG L f g hf hg hyf h2 h4 h6 h10
  by_cases hyg : GenericLocus g
  · obtain ⟨M, hM, e, he, h⟩ := hG L g f hg hf hyg h2.symm h4.symm h6.symm h10.symm
    exact sexticAct_symm g f M hM e he h
  · exact hS L f g hf hg (not_not.mp hyf) (not_not.mp hyg) h2 h4 h6 h10

/-- The generic half and the both-special half give the leaf T28. -/
theorem igusaClebschSeparation_of_generic_bothSpecial (hG : SeparationGeneric)
    (hS : SeparationBothSpecial) : IgusaClebschSeparation :=
  igusaClebschSeparation_iff.mpr (igusaSeparationEq_of_generic_bothSpecial hG hS)

/-- Covariance of Clebsch's quadratic covariants (degrees `3, 5, 7`, weights `8, 14, 20`):
`yᵢ(e·(cx+d)⁶f((ax+b)/(cx+d))) = e^{dᵢ} (ad-bc)^{wᵢ} (cx+d)² yᵢ(f)((ax+b)/(cx+d))`.
Checked numerically by `scratch/igusa-generic/cov_check.py`; proved in
`ZInQKernel/Contrib/T28/Covariance.lean` (`T28.yvCovariance`). -/
def YvCovariance : Prop :=
  ∀ (L : Type) [Field L] [CharZero L] (f : Fin 7 → L) (a b c d e : L), a * d - b * c ≠ 0 →
    ∀ i : Fin 3, yv (actC f a b c d e) i =
      fun l => e ^ (![3, 5, 7] i) * (a * d - b * c) ^ (![8, 14, 20] i) *
        T28SO3.qAct (yv f i) a b c d l

end T28
