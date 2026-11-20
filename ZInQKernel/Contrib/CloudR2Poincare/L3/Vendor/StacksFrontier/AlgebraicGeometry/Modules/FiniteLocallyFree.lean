import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
Only upstream lines [(53, 65), (82, 109), (130, 130)] are retained.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory

 noncomputable section
#cloudR2LocalInstances

open _root_.AlgebraicGeometry _root_.CategoryTheory
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v₁ u₁

namespace Stacks.FiniteLocallyFree
#cloudR2LocalInstances

section Site
#cloudR2LocalInstances

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
#cloudR2Vendor localGeneratorsDataOfIsIso in
/-- Transport local generators data along an isomorphism of sheaves of modules, keeping the same
covering and pushing each generating family forward. -/
def localGeneratorsDataOfIsIso {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
    (q : M.LocalGeneratorsData) : N.LocalGeneratorsData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi (f.over (q.X i))
#cloudR2Vendor isFiniteType_localGeneratorsDataOfIsIso in

/-- Transporting local generators data along an isomorphism preserves finiteness. -/
local instance isFiniteType_localGeneratorsDataOfIsIso {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    [IsIso f] (q : M.LocalGeneratorsData) [h : q.IsFiniteType] :
    (localGeneratorsDataOfIsIso f q).IsFiniteType where
  isFiniteType i :=
    have := h.isFiniteType i
    inferInstanceAs ((q.generators i).ofEpi (f.over (q.X i))).IsFiniteType
#cloudR2Vendor isLocallyFreeData_localGeneratorsDataOfIsIso in

/-- Transporting local generators data along an isomorphism preserves local freeness. -/
local instance isLocallyFreeData_localGeneratorsDataOfIsIso {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    [IsIso f] (q : M.LocalGeneratorsData) [h : q.IsLocallyFreeData] :
    (localGeneratorsDataOfIsIso f q).IsLocallyFreeData where
  isIso i := by
    have h₁ : IsIso (q.generators i).π := h.isIso i
    have h₂ : IsIso (f.over (q.X i)) :=
      inferInstanceAs (IsIso ((SheafOfModules.overFunctor R (q.X i)).map f))
    change IsIso ((q.generators i).ofEpi (f.over (q.X i))).π
    rw [SheafOfModules.GeneratingSections.ofEpi_π]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂
end Site
end Stacks.FiniteLocallyFree
end

end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
