import Mathlib
import ZInQKernel.Contrib.CloudW01Spread.ProperVendor.StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Diagonal

/-!
# Properness descent from an actual proper envelope

Adapted from AxiomMath/Stacks revision c496df0d9beea9deaeabcea8492605f9a0a2313b,
`StacksFrontier/AlgebraicGeometry/ProperLimitStage/Basic.lean` (Apache-2.0).
Original license is retained in CloudW01Spread/LICENSE.

Modification notice (2026-11-14): the projective-space envelope is generalized
here to an arbitrary proper scheme over the target; separatedness is assumed
at this intermediate stage so its second descent/meet is unnecessary. The
fixed H65 theorem has neither extra hypothesis: its stage is first made
separated by the actual 01ZQ proof, and its envelope is constructed separately.
All morphisms and their base changes are native schemes, not replacement data.
This intermediate theorem alone is not claimed as closure of H65.
-/

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudW01Spread.R2Envelope

universe u

/-- The native properness conclusion of Stacks 03GN. -/
theorem proper_of_surjective_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [UniversallyClosed (f ≫ g)] [Surjective f] [IsSeparated g] [LocallyOfFiniteType g] :
    IsProper g := by
  haveI : UniversallyClosed g := UniversallyClosed.of_comp_surjective f g
  exact ⟨⟩

/-- A proper surjective modification immersed into a proper envelope suffices
for descent of properness; the envelope need not be one projective space. -/
theorem exists_proper_stage_of_envelope
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (X Y : Over (D.obj i)) (f : X ⟶ Y)
    [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
    [LocallyOfFiniteType f.left] [IsSeparated f.left]
    [IsProper ((Over.pullback (c.π.app i)).map f).left]
    (X' P : Scheme.{u}) (ρ : X' ⟶ X.left) (g : P ⟶ Y.left) (j : X' ⟶ P)
    (hρ : IsProper ρ) (hρs : Surjective ρ) (hg : IsProper g)
    (hj : IsImmersion j) (hcomm : j ≫ g = ρ ≫ f.left) :
    ∃ (k : I) (a : k ⟶ i), IsProper ((Over.pullback (D.map a)).map f).left := by
  letI : IsProper ρ := hρ
  letI : Surjective ρ := hρs
  letI : IsProper g := hg
  letI : IsImmersion j := hj
  let Pe : Over (D.obj i) := Over.mk (g ≫ Y.hom)
  let Xe : Over (D.obj i) := Over.mk (ρ ≫ X.hom)
  let pr : Pe ⟶ Y := Over.homMk g rfl
  let rho : Xe ⟶ X := Over.homMk ρ rfl
  have hjbase : j ≫ Pe.hom = Xe.hom := by
    change j ≫ (g ≫ Y.hom) = ρ ≫ X.hom
    rw [← Category.assoc, hcomm, Category.assoc, Over.w f]
  let jo : Xe ⟶ Pe := Over.homMk j hjbase
  have htriangle : jo ≫ pr = rho ≫ f := by
    ext
    exact hcomm
  haveI : CompactSpace Xe.left := QuasiCompact.compactSpace_of_compactSpace ρ
  haveI : QuasiSeparatedSpace Xe.left := quasiSeparatedSpace_of_quasiSeparated ρ
  haveI : CompactSpace Pe.left := QuasiCompact.compactSpace_of_compactSpace g
  haveI : QuasiSeparatedSpace Pe.left := quasiSeparatedSpace_of_quasiSeparated g
  haveI : LocallyOfFiniteType jo.left := inferInstanceAs (LocallyOfFiniteType j)
  have htriangle_bc {T : Scheme.{u}} (q : T ⟶ D.obj i) :
      ((Over.pullback q).map jo).left ≫ ((Over.pullback q).map pr).left =
        ((Over.pullback q).map rho).left ≫ ((Over.pullback q).map f).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← Functor.map_comp, ← Functor.map_comp, htriangle]
  have hpr {T : Scheme.{u}} (q : T ⟶ D.obj i) :
      IsProper ((Over.pullback q).map pr).left :=
    MorphismProperty.overPullbackMap (P := @IsProper) q pr hg
  haveI : IsClosedImmersion ((Over.pullback (c.π.app i)).map jo).left := by
    haveI : IsImmersion ((Over.pullback (c.π.app i)).map jo).left :=
      MorphismProperty.overPullbackMap (P := @IsImmersion) (c.π.app i) jo hj
    haveI : IsProper ((Over.pullback (c.π.app i)).map rho).left :=
      MorphismProperty.overPullbackMap (P := @IsProper) (c.π.app i) rho hρ
    haveI := hpr (c.π.app i)
    haveI : IsProper (((Over.pullback (c.π.app i)).map jo).left ≫
        ((Over.pullback (c.π.app i)).map pr).left) := by
      rw [htriangle_bc]
      infer_instance
    haveI : IsProper ((Over.pullback (c.π.app i)).map jo).left :=
      IsProper.of_comp _ ((Over.pullback (c.π.app i)).map pr).left
    exact IsClosedImmersion.of_isPreimmersion _
      (((Over.pullback (c.π.app i)).map jo).left.isClosedMap.isClosed_range)
  obtain ⟨k, a, hclosed⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_baseChange_of_isLimit D c hc i Xe Pe jo
  letI : IsClosedImmersion ((Over.pullback (D.map a)).map jo).left := hclosed
  haveI := hpr (D.map a)
  haveI : IsProper (((Over.pullback (D.map a)).map rho).left ≫
      ((Over.pullback (D.map a)).map f).left) := by
    rw [← htriangle_bc]
    infer_instance
  haveI : Surjective ((Over.pullback (D.map a)).map rho).left :=
    MorphismProperty.overPullbackMap (P := @Surjective) (D.map a) rho hρs
  haveI : IsSeparated ((Over.pullback (D.map a)).map f).left :=
    MorphismProperty.overPullbackMap (P := @IsSeparated) (D.map a) f inferInstance
  haveI : LocallyOfFiniteType ((Over.pullback (D.map a)).map f).left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) (D.map a) f inferInstance
  exact ⟨k, a, proper_of_surjective_comp ((Over.pullback (D.map a)).map rho).left
    ((Over.pullback (D.map a)).map f).left⟩

end ZInQ.Contrib.CloudW01Spread.R2Envelope

#print axioms ZInQ.Contrib.CloudW01Spread.R2Envelope.exists_proper_stage_of_envelope
