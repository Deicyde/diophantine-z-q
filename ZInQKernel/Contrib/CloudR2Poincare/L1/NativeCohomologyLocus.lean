import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeModel
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeComplex

/-!
# Native closed fibre-cohomology loci

H-72 L1 continuation, seesaw A. This uses the NATIVE W07 universal bounded
finite-free model and matrix-minor upper semicontinuity, not Stacks Picard,
curve Picard representability, or a single-degree rank assumption. Higher
cohomology of O_A is not assumed to vanish.

The closed point SET obtained here is not claimed to represent the normalized
triviality functor on nonreduced test schemes. That scheme-theoretic step is
separate from semicontinuity.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

open Scheme

/-- Dimension of actual derived fibre homology of a module complex. -/
def derivedFiberDimension {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ)
    (q : ℤ) (y : Y) : ℕ :=
  Module.finrank (Y.residueField y)
    ((moduleSpecΓFunctor (R := Y.residueField y)).obj
      ((((Modules.pullback (Y.fromSpecResidueField y)).mapHomologicalComplex _).obj P).homology q))

/-- The h^q≥r locus of a termwise finite free complex is topologically closed. -/
theorem isClosed_derivedFiberDimension_ge {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ)
    (hP : ∀ n, ∃ r : ℕ, Nonempty (P.X n ≅
      SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))
    (q : ℤ) (r : ℕ) : IsClosed {y : Y | r ≤ derivedFiberDimension P q y} := by
  have hopen : IsOpen {y : Y | derivedFiberDimension P q y < r} := by
    apply isOpen_iff_forall_mem_open.mpr
    intro y hy
    obtain ⟨V, hV, hle⟩ := Modules.exists_finrank_homology_pullback_le hP q
      (Field.toIsField (Y.residueField y)) (Y.fromSpecResidueField y)
    have hyV : y ∈ V := by
      obtain ⟨z⟩ : Nonempty (Spec (Y.residueField y)) := inferInstance
      exact Modules.fromSpecResidueField_base_apply y z ▸ hV ⟨z, rfl⟩
    refine ⟨V, ?_, V.isOpen, hyV⟩
    intro z hz
    have hzV : Set.range (Y.fromSpecResidueField z).base ⊆ V := by
      rintro _ ⟨w, rfl⟩
      rw [Modules.fromSpecResidueField_base_apply]
      exact hz
    exact lt_of_le_of_lt
      (hle (Field.toIsField (Y.residueField z)) (Y.fromSpecResidueField z) hzV) hy
  convert hopen.isClosed_compl using 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]

/-- Dimension of the actual higher direct image on a residue-field base change. -/
def higherDirectImageResidueRank {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (q : ℕ) (y : Y) : ℕ :=
  let p := Y.fromSpecResidueField y
  letI := Modules.isGrothendieckAbelian (pullback f p)
  Module.finrank (Y.residueField y)
    ((moduleSpecΓFunctor (R := Y.residueField y)).obj
      ((Modules.higherDirectImage (pullback.snd f p) q).obj
        ((Modules.pullback (pullback.fst f p)).obj F)))

/-- Native upper-semicontinuity for a proper family over a noetherian affine base,
with finitely presented relatively flat coefficients. -/
theorem isClosed_higherDirectImageResidueRank_ge
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] (F : X.Modules) [F.IsFinitePresentation]
    (hflat : F.IsFlatOver f) (q r : ℕ) :
    IsClosed {y : Spec (.of R) | r ≤ higherDirectImageResidueRank f F q y} := by
  let Y := Spec (.of R)
  have hopen : IsOpen {y : Y | higherDirectImageResidueRank f F q y < r} := by
    apply isOpen_iff_forall_mem_open.mpr
    intro y hy
    obtain ⟨denominator, P, bound, hyU, hP, comparison⟩ :=
      Modules.exists_isFiniteFreeComplex_higherDirectImage_of_isProper R f F hflat y
    let U := Y.basicOpen denominator
    let py := Y.fromSpecResidueField y
    have hyRange : Set.range py ⊆ Set.range U.ι := by
      rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
      exact Set.singleton_subset_iff.mpr hyU
    let gy := IsOpenImmersion.lift U.ι py hyRange
    have gy_fac : gy ≫ U.ι = py := IsOpenImmersion.lift_fac _ _ _
    have squareY : IsPullback (pullback.fst f py) (pullback.snd f py) f (gy ≫ U.ι) := by
      rw [gy_fac]
      exact IsPullback.of_hasPullback f py
    haveI := Modules.isGrothendieckAbelian (pullback f py)
    let eY := (comparison gy (pullback.fst f py) (pullback.snd f py) squareY q).some
    have dimY : Module.finrank (Y.residueField y)
        ((moduleSpecΓFunctor (R := Y.residueField y)).obj
          ((((Modules.pullback gy).mapHomologicalComplex _).obj P).homology (q : ℤ))) =
        higherDirectImageResidueRank f F q y :=
      ((moduleSpecΓFunctor (R := Y.residueField y)).mapIso eY).toLinearEquiv.finrank_eq
    obtain ⟨V, hyV, hle⟩ := Modules.exists_finrank_homology_pullback_le hP.exists_iso_free
      (q : ℤ) (Field.toIsField (Y.residueField y)) gy
    refine ⟨U.ι '' (V : Set U.toScheme), ?_, U.ι.isOpenMap _ V.isOpen, ?_⟩
    · rintro z ⟨zU, hzV, hz⟩
      let pz := Y.fromSpecResidueField z
      have hzU : z ∈ U := by rw [← hz]; exact zU.property
      have hzRange : Set.range pz ⊆ Set.range U.ι := by
        rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
        exact Set.singleton_subset_iff.mpr hzU
      let gz := IsOpenImmersion.lift U.ι pz hzRange
      have gz_fac : gz ≫ U.ι = pz := IsOpenImmersion.lift_fac _ _ _
      have gzV : Set.range gz.base ⊆ V := by
        rintro _ ⟨w, rfl⟩
        have hpoint : gz w = zU := by
          apply U.ι.isOpenEmbedding.injective
          rw [← Scheme.Hom.comp_apply, gz_fac, Scheme.fromSpecResidueField_apply, hz]
        rw [hpoint]
        exact hzV
      have squareZ : IsPullback (pullback.fst f pz) (pullback.snd f pz) f (gz ≫ U.ι) := by
        rw [gz_fac]
        exact IsPullback.of_hasPullback f pz
      haveI := Modules.isGrothendieckAbelian (pullback f pz)
      let eZ := (comparison gz (pullback.fst f pz) (pullback.snd f pz) squareZ q).some
      have dimZ : Module.finrank (Y.residueField z)
          ((moduleSpecΓFunctor (R := Y.residueField z)).obj
            ((((Modules.pullback gz).mapHomologicalComplex _).obj P).homology (q : ℤ))) =
          higherDirectImageResidueRank f F q z :=
        ((moduleSpecΓFunctor (R := Y.residueField z)).mapIso eZ).toLinearEquiv.finrank_eq
      have hzle := hle (Field.toIsField (Y.residueField z)) gz gzV
      rw [dimY, dimZ] at hzle
      exact lt_of_le_of_lt hzle hy
    · obtain ⟨w⟩ : Nonempty (Spec (Y.residueField y)) := inferInstance
      refine ⟨gy w, hyV ⟨w, rfl⟩, ?_⟩
      rw [← Scheme.Hom.comp_apply, gy_fac, Scheme.fromSpecResidueField_apply]
  convert hopen.isClosed_compl using 1
  ext y
  change (r ≤ higherDirectImageResidueRank f F q y) ↔
    ¬ higherDirectImageResidueRank f F q y < r
  exact not_lt.symm

end ZInQ.Contrib.CloudR2Poincare.L1
