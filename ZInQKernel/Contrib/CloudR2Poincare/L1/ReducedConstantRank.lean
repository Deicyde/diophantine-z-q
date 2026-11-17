import ZInQKernel.Contrib.CloudR2Poincare.L1.NativeCohomologyLocus
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeComplexLocus
import Mathlib.AlgebraicGeometry.Properties

/-!
# Reduced constant-rank matrices: the first constructive Grauert step

A fieldwise rank bound kills the larger minors on a REDUCED scheme. A maximal
nonzero minor then gives an actual split rank factorization on a neighborhood,
valid after every scheme-valued base change. No higher-degree cohomology
vanishing and no desired seesaw/base-change Fact is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- A global function on a reduced scheme is detected on all actual residue-field points. -/
theorem section_eq_zero_of_residueField_appTop_eq_zero
    {Y : Scheme.{u}} [AlgebraicGeometry.IsReduced Y] (s : Γ(Y, ⊤))
    (hs : ∀ y : Y, (Y.fromSpecResidueField y).appTop s = 0) : s = 0 := by
  apply AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot s
  apply bot_unique
  intro y hy
  change False
  obtain ⟨x⟩ : Nonempty (Spec (Y.residueField y)) := inferInstance
  have hy' : (Y.fromSpecResidueField y).base x ∈ Y.basicOpen s := by
    simpa only [Scheme.Modules.fromSpecResidueField_base_apply] using hy
  exact ((Y.fromSpecResidueField y).appTop_ne_zero_iff_mem_basicOpen
    (Scheme.Modules.isField_Γ_Spec_residueField y) s x).mpr hy' (hs y)

/-- A residue-field rank bound gives genuine vanishing of every larger minor
on a reduced parameter scheme, rather than merely nilpotent minors. -/
theorem larger_minor_eq_zero_of_residueRank_le
    {Y : Scheme.{u}} [AlgebraicGeometry.IsReduced Y]
    {m n : Type u} [Fintype m] [Fintype n]
    (A : Matrix m n Γ(Y, ⊤)) (ρ : ℕ)
    (hρ : ∀ y : Y, (A.map (Y.fromSpecResidueField y).appTop).rank ≤ ρ)
    (rows : Fin (ρ + 1) → m) (cols : Fin (ρ + 1) → n) :
    (A.submatrix rows cols).det = 0 := by
  apply section_eq_zero_of_residueField_appTop_eq_zero
  intro y
  letI : Field Γ(Spec (Y.residueField y), ⊤) :=
    (Scheme.Modules.isField_Γ_Spec_residueField y).toField
  by_contra hn
  have hlarge := (Matrix.le_rank_map_iff A (Y.fromSpecResidueField y).appTop.hom (ρ + 1)).mpr
    ⟨rows, cols, hn⟩
  change ρ + 1 ≤ (A.map (Y.fromSpecResidueField y).appTop).rank at hlarge
  have hsmall := hρ y
  omega

/-- Constant residue-field rank gives a split rank factorization on a genuine
open neighborhood, uniformly after arbitrary scheme-valued base change. -/
theorem exists_opens_split_of_constant_residueRank
    {Y : Scheme.{u}} [AlgebraicGeometry.IsReduced Y]
    {m n : Type u} [Fintype m] [Fintype n]
    (A : Matrix m n Γ(Y, ⊤)) (ρ : ℕ)
    (hρ : ∀ y : Y, (A.map (Y.fromSpecResidueField y).appTop).rank = ρ)
    (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ ∀ {Z : Scheme.{u}} (g : Z ⟶ Y), Set.range g ⊆ U →
      ∃ (L : Matrix m (Fin ρ) Γ(Z, ⊤)) (M : Matrix (Fin ρ) n Γ(Z, ⊤))
        (L' : Matrix (Fin ρ) m Γ(Z, ⊤)) (M' : Matrix n (Fin ρ) Γ(Z, ⊤)),
        A.map g.appTop = L * M ∧ L' * L = 1 ∧ M * M' = 1 := by
  classical
  obtain ⟨x⟩ : Nonempty (Spec (Y.residueField y)) := inferInstance
  obtain ⟨rows, cols, hy⟩ :=
    (Scheme.Modules.le_rank_map_appTop_iff (Scheme.Modules.isField_Γ_Spec_residueField y)
      (Y.fromSpecResidueField y) x A ρ).mp (by rw [hρ])
  rw [Scheme.Modules.fromSpecResidueField_base_apply] at hy
  have hzero := larger_minor_eq_zero_of_residueRank_le A ρ (fun z ↦ (hρ z).le)
  refine ⟨Y.basicOpen (A.submatrix rows cols).det, hy, fun g hg ↦ ?_⟩
  have hunit : IsUnit ((A.map g.appTop).submatrix rows cols).det := by
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact Scheme.isUnit_appTop_of_range_subset g _ hg
  apply Matrix.exists_mul_eq_of_isUnit_det_submatrix _ rows cols hunit
  intro r c
  rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hzero r c, map_zero]

/-- With no degree -1 term, fibre H0 dimension one forces the outgoing
matrix rank to be exactly the rank of degree zero minus one. -/
theorem outgoing_residueRank_eq_of_H0_dimension_one
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (r : ℤ → ℕ)
    (e : ∀ q, P.X q ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin (r q))))
    (hneg : r (-1) = 0) (hH0 : ∀ y : Y, derivedFiberDimension P 0 y = 1) :
    ∀ y : Y,
      ((Scheme.Modules.freeMatrix ((e 0).inv ≫ P.d 0 1 ≫ (e 1).hom)).map
        (Y.fromSpecResidueField y).appTop).rank = r 0 - 1 := by
  intro y
  haveI : IsEmpty (ULift.{u} (Fin (r (-1)))) := by rw [hneg]; infer_instance
  have hdim := Scheme.Modules.finrank_homology_pullback_add_rank_add_rank e
    (Field.toIsField (Y.residueField y)) (Y.fromSpecResidueField y) 0
  change derivedFiberDimension P 0 y +
    ((Scheme.Modules.freeMatrix ((e 0).inv ≫ P.d 0 1 ≫ (e 1).hom)).map
      (Y.fromSpecResidueField y).appTop).rank +
    ((Scheme.Modules.freeMatrix ((e (-1)).inv ≫ P.d (-1) 0 ≫ (e 0).hom)).map
      (Y.fromSpecResidueField y).appTop).rank = r 0 at hdim
  have hempty :
      (Scheme.Modules.freeMatrix ((e (-1)).inv ≫ P.d (-1) 0 ≫ (e 0).hom)).map
        (Y.fromSpecResidueField y).appTop = 0 := Subsingleton.elim _ _
  rw [hH0, hempty, Matrix.rank_zero, add_zero] at hdim
  omega

end ZInQ.Contrib.CloudR2Poincare.L1
