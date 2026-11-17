import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Pullback
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.LongExact
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Sites.SheafCohomology.ExactSequence

/-!
# Connecting-map compatibility of the actual native adjunction map

This owned lemma matches the Ext-defined H.mapOfAdjunction with the actual
connecting maps. Exact inverse image of abelian sheaves and the native mapped
extension class supply the proof; no injectivity or Leray Fact is assumed.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits Abelian

namespace ZInQ.Contrib.CloudR2Poincare.L3.LerayOneConstruction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Y : Scheme.{u}}

local instance {Z : Scheme.{u}} : Functor.PreservesZeroMorphisms
    (C := Z.Modules) (SheafOfModules.toSheaf.{u} Z.ringCatSheaf) where
  map_zero := by intros; ext openSubset sectionValue; rfl

/-- The actual coefficient adjoints form a morphism of the inverse-imaged
abelian short complexes. -/
def adjointShortComplexMap (f : X ⟶ Y) {S : ShortComplex Y.Modules}
    {T : ShortComplex X.Modules} (φ : S ⟶ T.map (Scheme.Modules.pushforward f)) :
    (S.map (SheafOfModules.toSheaf.{u} Y.ringCatSheaf)).map
      (Scheme.Modules.abelianInverseImage f) ⟶
      T.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf) where
  τ₁ := Scheme.Modules.adjointCoefficientMap f φ.τ₁
  τ₂ := Scheme.Modules.adjointCoefficientMap f φ.τ₂
  τ₃ := Scheme.Modules.adjointCoefficientMap f φ.τ₃
  comm₁₂ := (Scheme.Modules.adjointCoefficientMap_naturality f φ.τ₁ φ.τ₂
    S.f T.f φ.comm₁₂.symm).symm
  comm₂₃ := (Scheme.Modules.adjointCoefficientMap_naturality f φ.τ₂ φ.τ₃
    S.g T.g φ.comm₂₃.symm).symm

/-- One named step from module connecting maps to the underlying abelian-sheaf
connecting map. This unfolds only the two existing evaluation formulas. -/
theorem moduleDelta_asSheaf {Z : Scheme.{u}} {S : ShortComplex Z.Modules}
    (hS : S.ShortExact) (n : ℕ) (z : S.X₃.H n) :
    Scheme.Modules.H.δ hS n z =
      Sheaf.H.δSucc (Scheme.Modules.shortExact_map_toSheaf hS) n z := by
  rw [Scheme.Modules.H.δ_apply, Sheaf.H.δSucc_apply]

/-- Evaluate the existing adjunction arrow in one coefficient and degree,
without normalizing an entire mapped short complex at once. -/
theorem adjunction_cohomology_apply (f : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
    (phi : M ⟶ (Scheme.Modules.pushforward f).obj N) (n : ℕ) (z : M.H n) :
    Scheme.Modules.H.mapOfAdjunction f phi n z =
      Sheaf.H.map (Scheme.Modules.adjointCoefficientMap f phi) n
        (Sheaf.H.mapFunctor (Scheme.Modules.abelianInverseImage f)
          (Scheme.Modules.abelianInverseImageConstantIso f).symm
          ((SheafOfModules.toSheaf.{u} Y.ringCatSheaf).obj M) n z) := by
  unfold Scheme.Modules.H.mapOfAdjunction
  rfl

/-- Exact inverse image preserves the native connecting map, including the
actual constant-integer-sheaf comparison used by H.mapFunctor. -/
theorem inverseImage_delta (f : X ⟶ Y)
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (n : ℕ) (z : Sheaf.H S.X₃ n) :
    Sheaf.H.mapFunctor (Scheme.Modules.abelianInverseImage f)
        (Scheme.Modules.abelianInverseImageConstantIso f).symm S.X₁ (n + 1)
        (Sheaf.H.δSucc hS n z) =
      Sheaf.H.δSucc (hS.map_of_exact (Scheme.Modules.abelianInverseImage f)) n
        (Sheaf.H.mapFunctor (Scheme.Modules.abelianInverseImage f)
          (Scheme.Modules.abelianInverseImageConstantIso f).symm S.X₃ n z) := by
  simp only [Sheaf.H.δSucc_apply, Sheaf.H.mapFunctor_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

/-- The original H.mapOfAdjunction commutes with the actual native connecting
maps for an actual morphism to a pushed-forward short exact sequence. -/
theorem mapOfAdjunction_delta (f : X ⟶ Y)
    {S : ShortComplex Y.Modules} {T : ShortComplex X.Modules}
    (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T.map (Scheme.Modules.pushforward f)) (n : ℕ) (z : S.X₃.H n) :
    Scheme.Modules.H.mapOfAdjunction f φ.τ₁ (n + 1) (Scheme.Modules.H.δ hS n z) =
      Scheme.Modules.H.δ hT n (Scheme.Modules.H.mapOfAdjunction f φ.τ₃ n z) := by
  let AS := S.map (SheafOfModules.toSheaf.{u} Y.ringCatSheaf)
  let AT := T.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
  have hAS : AS.ShortExact := Scheme.Modules.shortExact_map_toSheaf hS
  have hAT : AT.ShortExact := Scheme.Modules.shortExact_map_toSheaf hT
  let ψ := adjointShortComplexMap f φ
  change Sheaf.H.map ψ.τ₁ (n + 1)
      (Sheaf.H.mapFunctor (Scheme.Modules.abelianInverseImage f)
        (Scheme.Modules.abelianInverseImageConstantIso f).symm AS.X₁ (n + 1)
        (Sheaf.H.δSucc hAS n z)) =
    Sheaf.H.δSucc hAT n
      (Sheaf.H.map ψ.τ₃ n
        (Sheaf.H.mapFunctor (Scheme.Modules.abelianInverseImage f)
          (Scheme.Modules.abelianInverseImageConstantIso f).symm AS.X₃ n z))
  rw [inverseImage_delta]
  exact Sheaf.H.map_δSucc (hAS.map_of_exact (Scheme.Modules.abelianInverseImage f))
    hAT ψ n _

end ZInQ.Contrib.CloudR2Poincare.L3.LerayOneConstruction
