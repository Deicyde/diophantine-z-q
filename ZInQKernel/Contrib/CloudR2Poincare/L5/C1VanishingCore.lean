import ZInQKernel.Contrib.CloudR2Poincare.L5.C1MultiplicativeSeesaw
import ZInQKernel.Contrib.CloudR2Poincare.L5.C1Shear
import ZInQKernel.Contrib.CloudR2Poincare.L1.CohomologyVanishingReduction
import ZInQKernel.Contrib.CloudR2Poincare.L1.TrivialFibreH0Rank
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Proper
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-!
# C1: native vanishing assembly from two concrete product-rank formulas

The only geometric family argument is the exact named existing reduced
normalized seesaw `hA`. Intrinsic native cohomology finiteness, unit H0 rank1,
translation-invariance-to-multiplicativity/inverse-pullback, and shear rank
comparison are proved and used, not assumed.

The two concrete product-rank equations remain ordinary LOCAL arguments to
this glue theorem until the sole shared Stacks supplier is imported in the
thin canonical adapter. No new desired Fact, global Kunneth instance, or
unconditional NativePicZeroVanishing proof is asserted here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped AlgebraicGeometry.Scheme.Modules BigOperators

namespace ZInQ.Contrib.CloudR2Poincare.L5

/-- Native finite cohomology of an actual invertible bundle on an abelian
variety, in the EXACT native field action used in L1's conclusion. -/
theorem native_finiteH_invertible_abVar
    {k : Type} [Field k] (B : PkgI3.AbVar k) (N : B.X.left.Modules) [N.IsInvertible] :
    letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
    ∀ q : ℕ, Module.Finite k (N.H q) := by
  letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
  haveI : N.IsFinitePresentation := inferInstance
  exact Scheme.Modules.hasFiniteH_of_isProper B.X.hom N

/-- The original-field unit H0 rank is 1, not a desired cohomology premise.
The native higher-direct-image sections comparison supplies the field action. -/
theorem native_abVar_unit_finrankH_zero
    {k : Type} [Field k] (B : PkgI3.AbVar k) :
    letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
    Scheme.Modules.finrankH (X := B.X.left) k (SheafOfModules.unit B.X.left.ringCatSheaf) 0 = 1 := by
  letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
  let O : B.X.left.Modules := SheafOfModules.unit B.X.left.ringCatSheaf
  haveI : QuasiCompact (B.X.left ↘ Spec (.of k)) := by
    change QuasiCompact B.X.hom
    infer_instance
  haveI : IsSeparated (B.X.left ↘ Spec (.of k)) := by
    change IsSeparated B.X.hom
    infer_instance
  obtain ⟨comparison⟩ :=
    Scheme.Modules.nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H O k 0
  exact comparison.finrank_eq.symm.trans
    (L1.finrank_higherDirectImage_zero_eq_one_of_iso_unit B.X.hom O (Iso.refl _))

/-- The EXACT local all-q convolution used in L1, once the two literal
product-rank formulas are supplied by the shared Kunneth adapter. Multiplicative
bundle identity is derived from ONE seesaw input, not assumed separately. -/
theorem native_convolution_of_two_product_rank_formulas
    (hA : L2.ReducedGlobalNormalizedSeesaw)
    {k : Type} [Field k] [IsAlgClosed k] (B : PkgI3.AbVar k)
    (N : B.X.left.Modules) [N.IsInvertible]
    (invariant : L3.TranslationInvariant B (Scheme.Pic.mk N))
    (rankNN :
      letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
      letI : (B.X ⊗ B.X).left.Over (Spec (.of k)) := ⟨(B.X ⊗ B.X).hom⟩
      ∀ q : ℕ,
        ((Scheme.Modules.pullback (fst B.X B.X).left).obj N ⊗
          (Scheme.Modules.pullback (snd B.X B.X).left).obj N).finrankH k q =
        ∑ i ∈ Finset.range (q + 1), N.finrankH k i * N.finrankH k (q - i))
    (rankON :
      letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
      letI : (B.X ⊗ B.X).left.Over (Spec (.of k)) := ⟨(B.X ⊗ B.X).hom⟩
      ∀ q : ℕ,
        ((Scheme.Modules.pullback (fst B.X B.X).left).obj
            (SheafOfModules.unit B.X.left.ringCatSheaf) ⊗
          (Scheme.Modules.pullback (snd B.X B.X).left).obj N).finrankH k q =
        ∑ i ∈ Finset.range (q + 1),
          Scheme.Modules.finrankH (X := B.X.left) k (SheafOfModules.unit B.X.left.ringCatSheaf) i * N.finrankH k (q - i)) :
    letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
    ∀ q : ℕ,
      (∑ i ∈ Finset.range (q + 1), N.finrankH k i * N.finrankH k (q - i)) =
        ∑ i ∈ Finset.range (q + 1),
          Scheme.Modules.finrankH (X := B.X.left) k (SheafOfModules.unit B.X.left.ringCatSheaf) i * N.finrankH k (q - i) := by
  letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
  letI : (B.X ⊗ B.X).left.Over (Spec (.of k)) := ⟨(B.X ⊗ B.X).hom⟩
  intro q
  exact (rankNN q).symm.trans
    ((native_product_rank_eq_of_multiplicative_pullback B N
      (mul_pullback_of_translationInvariant hA B N invariant) q).trans (rankON q))

/-- Native higher cohomology vanishes after the concrete Kunneth-rank adapter
supplies its two actual product formulas. No finiteH/H0/inverse symmetry or
multiplicativity premise remains beyond the ONE existing seesaw input. -/
theorem native_vanishing_of_two_product_rank_formulas
    (hA : L2.ReducedGlobalNormalizedSeesaw)
    {k : Type} [Field k] [IsAlgClosed k] (B : PkgI3.AbVar k)
    (N : B.X.left.Modules) [N.IsInvertible]
    (invariant : L3.TranslationInvariant B (Scheme.Pic.mk N)) (nontrivial : Scheme.Pic.mk N ≠ 1)
    (rankNN :
      letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
      letI : (B.X ⊗ B.X).left.Over (Spec (.of k)) := ⟨(B.X ⊗ B.X).hom⟩
      ∀ q : ℕ,
        ((Scheme.Modules.pullback (fst B.X B.X).left).obj N ⊗
          (Scheme.Modules.pullback (snd B.X B.X).left).obj N).finrankH k q =
        ∑ i ∈ Finset.range (q + 1), N.finrankH k i * N.finrankH k (q - i))
    (rankON :
      letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
      letI : (B.X ⊗ B.X).left.Over (Spec (.of k)) := ⟨(B.X ⊗ B.X).hom⟩
      ∀ q : ℕ,
        ((Scheme.Modules.pullback (fst B.X B.X).left).obj
            (SheafOfModules.unit B.X.left.ringCatSheaf) ⊗
          (Scheme.Modules.pullback (snd B.X B.X).left).obj N).finrankH k q =
        ∑ i ∈ Finset.range (q + 1),
          Scheme.Modules.finrankH (X := B.X.left) k (SheafOfModules.unit B.X.left.ringCatSheaf) i * N.finrankH k (q - i)) :
    ∀ q : ℕ, Subsingleton (N.H q) := by
  letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
  haveI : ∀ q : ℕ, Module.Finite k (N.H q) := native_finiteH_invertible_abVar B N
  haveI : Subsingleton (N.H 0) := L1.subsingleton_H_zero_of_inversePullback B N nontrivial
    (inverse_pullback_class_of_translationInvariant hA B (Scheme.Pic.mk N) invariant)
  apply L1.native_cohomology_vanish_of_kunneth_ranks (k := k) N
  · exact Module.finrank_zero_of_subsingleton
  · exact native_abVar_unit_finrankH_zero B
  · exact native_convolution_of_two_product_rank_formulas hA B N invariant rankNN rankON

end ZInQ.Contrib.CloudR2Poincare.L5
