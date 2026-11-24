import ZInQKernel.Contrib.CloudR2Poincare.L3.B2UniversalAcyclic
import Mathlib.Topology.JacobsonSpace

/-! Jacobson closed-point detection for bounded native finite-free fibre models.
This prevents substitution of all rational closed points for all scheme points. -/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace ZInQ.Contrib.CloudR2Poincare.L3
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u

/-- Outside the actual finite bound, the native fibre-homology dimension is zero. -/
theorem derivedFiberDimension_zero_of_rank_zero {Y : Scheme.{u}}
    (P : CochainComplex Y.Modules ℤ) (r : ℤ → ℕ)
    (e : ∀ q, P.X q ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin (r q))))
    (q : ℤ) (hq : r q = 0) (y : Y) : L1.derivedFiberDimension P q y = 0 := by
  have H := Scheme.Modules.finrank_homology_pullback_add_rank_add_rank e
    (Field.toIsField (Y.residueField y)) (Y.fromSpecResidueField y) q
  change L1.derivedFiberDimension P q y + _ + _ = r q at H
  have Hzero := H.trans hq
  omega

/-- On a Jacobson base, vanishing at every CLOSED point gives genuine vanishing
at all residue-field points, in every degree, for a bounded finite-free model. -/
theorem derivedFiberDimension_zero_of_closedPoints {Y : Scheme.{u}} [JacobsonSpace Y]
    (P : CochainComplex Y.Modules ℤ) (r : ℤ → ℕ)
    (e : ∀ q, P.X q ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin (r q))))
    (bound : ℕ) (hbound : ∀ q : ℤ, q < 0 ∨ (bound : ℤ) < q → r q = 0)
    (hclosed : ∀ y : Y, IsClosed ({y} : Set Y) → ∀ q : ℤ, L1.derivedFiberDimension P q y = 0) :
    ∀ y : Y, ∀ q : ℤ, L1.derivedFiberDimension P q y = 0 := by
  classical
  let S : Set Y := ⋂ q ∈ Finset.Icc (0 : ℤ) (bound : ℤ),
    {y : Y | 1 ≤ L1.derivedFiberDimension P q y}ᶜ
  have hopen : IsOpen S := by
    apply isOpen_biInter_finset
    intro q _
    exact (L1.isClosed_derivedFiberDimension_ge P
      (fun n => ⟨r n, ⟨e n⟩⟩) q 1).isOpen_compl
  have hfull : S = Set.univ := by
    have hempty : Sᶜ ∩ closedPoints Y = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro y ⟨hy, hc⟩
      apply hy
      simp only [S, Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq]
      intro q _
      rw [hclosed y hc q]
      omega
    have hcompl : Sᶜ = ∅ := by
      rw [← closure_inter_closedPoints hopen.isClosed_compl, hempty, closure_empty]
    exact Set.compl_empty_iff.mp hcompl
  intro y q
  by_cases hq : q ∈ Finset.Icc (0 : ℤ) (bound : ℤ)
  · have hy : y ∈ S := by rw [hfull]; trivial
    have H : ¬ 1 ≤ L1.derivedFiberDimension P q y := by
      exact (Set.mem_iInter.mp (Set.mem_iInter.mp hy q) hq)
    omega
  · apply derivedFiberDimension_zero_of_rank_zero P r e q _ y
    apply hbound q
    simp only [Finset.mem_Icc, not_and_or, not_le] at hq
    exact hq

/-- The resulting zero model splits universally near EVERY scheme point. -/
theorem locally_universally_zero_of_closed_fibre_zero {Y : Scheme.{u}} [JacobsonSpace Y]
    (P : CochainComplex Y.Modules ℤ) (r : ℤ → ℕ)
    (e : ∀ q, P.X q ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin (r q))))
    (bound : ℕ) (hbound : ∀ q : ℤ, q < 0 ∨ (bound : ℤ) < q → r q = 0)
    (hclosed : ∀ y : Y, IsClosed ({y} : Set Y) → ∀ q : ℤ, L1.derivedFiberDimension P q y = 0)
    (y : Y) :
    ∃ W : Y.Opens, y ∈ W ∧ ∀ {Z : Scheme.{u}} (g : Z ⟶ Y), Set.range g ⊆ W →
      ∀ q : ℤ, IsZero ((((Scheme.Modules.pullback g).mapHomologicalComplex _).obj P).homology q) :=
  exists_opens_universally_zero_homology_of_fibre_zero P r e bound hbound y
    (derivedFiberDimension_zero_of_closedPoints P r e bound hbound hclosed y)

end ZInQ.Contrib.CloudR2Poincare.L3
