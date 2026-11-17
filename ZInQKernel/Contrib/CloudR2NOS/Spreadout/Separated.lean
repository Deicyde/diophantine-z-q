/-
# H5 / NOS round 2, lane 3 (`Spreadout/`): separatedness at a stage, and the properness interface

New glue (no vendored source in this file).

* `exists_isSeparated_next`: if the base change of a finitely presented stage object to `lim D` is
  separated, so is its base change to some later stage (EGA IV₃ 8.10.5 (v)).  The diagonal of a
  stage object is a morphism of `Over (D.obj i)`; base change carries it to the diagonal of the
  base change (`Over.pullback` preserves products), and closed immersions descend by the published
  H65/W01 port of Stacks 01ZQ (`AlgebraicGeometry.exists_isClosedImmersion_baseChange_of_isLimit`).
* `StacksProperNoetherian`: the exact statement (at universe `u` for the index category) of the
  AxiomMath/Stacks theorem `AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_isNoetherian`
  (StacksFrontier/AlgebraicGeometry/ProperLimitStage/NoetherianChow.lean at
  c496df0d9beea9deaeabcea8492605f9a0a2313b), whose universe-polymorphic port is owned by H65
  child 04.  It is an explicit input here, NOT proved.
* `properDescendsFor_of_stacksNoetherian`: that statement, together with Noetherian stages, gives
  `ProperDescendsFor D c` for an arbitrary (essentially small, cofiltered) system, with
  separatedness at the stage derived by `exists_isSeparated_next`.
* `isNoetherian_specDiagram_of_etale`: the stages of an ind-étale presentation over a Noetherian
  ring are Noetherian.
-/
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.HensDiagram
import ZInQKernel.Contrib.CloudW01Spread.StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Spreadout

universe u

open ZInQ.Contrib.SpreadOut (stθ pbNat)

/-! ### The diagonal in `Over S` -/

section Diagonal

variable {S T : Scheme.{u}}

/-- The diagonal of an object of `Over S`, as a morphism of `Over S`. -/
abbrev overDiag (X : Over S) : X ⟶ X ⊗ X := lift (𝟙 X) (𝟙 X)

theorem overDiag_left (X : Over S) : (overDiag X).left = pullback.diagonal X.hom := by
  apply pullback.hom_ext <;> simp

/-- Base change carries the diagonal to the diagonal, up to the product comparison. -/
theorem pullback_map_overDiag (f : T ⟶ S) (X : Over S) :
    (Over.pullback f).map (overDiag X) =
      overDiag ((Over.pullback f).obj X) ≫
        Functor.LaxMonoidal.μ (Over.pullback f) X X := by
  rw [overDiag, overDiag, ← (Over.pullback f).map_id X, Functor.Monoidal.lift_μ]

/-- Separatedness of an object of `Over S` is closed immersion of its diagonal in `Over S`. -/
theorem isSeparated_iff_overDiag (X : Over S) :
    IsSeparated X.hom ↔ IsClosedImmersion (overDiag X).left := by
  rw [overDiag_left, isSeparated_iff]

/-- Separatedness of a base change is closed immersion of the base-changed diagonal. -/
theorem isSeparated_pullback_iff (f : T ⟶ S) (X : Over S) :
    IsSeparated ((Over.pullback f).obj X).hom ↔
      IsClosedImmersion ((Over.pullback f).map (overDiag X)).left := by
  rw [pullback_map_overDiag, Over.comp_left, isSeparated_iff_overDiag]
  haveI : IsIso (Functor.LaxMonoidal.μ (Over.pullback f) X X).left :=
    inferInstanceAs (IsIso ((Functor.Monoidal.μIso (Over.pullback f) X X).hom.left))
  exact (MorphismProperty.cancel_right_of_respectsIso (@IsClosedImmersion) _ _).symm

end Diagonal

/-! ### Separatedness descends to a stage -/

section Separated

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D}

/-- **Separatedness descends to a later stage (EGA IV₃ 8.10.5 (v)).** -/
theorem exists_isSeparated_next (hc : IsLimit c) {i : I} (X : Over (D.obj i))
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (h : IsSeparated ((Over.pullback (c.π.app i)).obj X).hom) :
    ∃ (j : I) (a : j ⟶ i), IsSeparated ((Over.pullback (D.map a)).obj X).hom := by
  haveI : EssentiallySmall.{u} I := inferInstance
  haveI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  haveI : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  haveI : QuasiCompact (X ⊗ X).hom := qc_tensor X X
  haveI : QuasiSeparated (X ⊗ X).hom := qs_tensor X X
  haveI : CompactSpace (X ⊗ X).left := QuasiCompact.compactSpace_of_compactSpace (X ⊗ X).hom
  haveI : QuasiSeparatedSpace (X ⊗ X).left := quasiSeparatedSpace_of_quasiSeparated (X ⊗ X).hom
  haveI : LocallyOfFiniteType (overDiag X).left := by
    rw [overDiag_left]
    infer_instance
  haveI : IsClosedImmersion ((Over.pullback (c.π.app i)).map (overDiag X)).left :=
    (isSeparated_pullback_iff (c.π.app i) X).1 h
  obtain ⟨j, a, ha⟩ := AlgebraicGeometry.exists_isClosedImmersion_baseChange_of_isLimit
    D c hc i X (X ⊗ X) (overDiag X)
  exact ⟨j, a, (isSeparated_pullback_iff (D.map a) X).2 ha⟩

end Separated

/-! ### The properness interface -/

/-- **Exact statement (index universe `u`) of the AxiomMath/Stacks theorem
`AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_isNoetherian`** (EGA IV₃ 8.10.5 (xii)
over a Noetherian target, via Chow's lemma), Stacks@c496df0d `ProperLimitStage/NoetherianChow.lean`.
Input, not proved here; H65 child 04 owns the port. -/
def StacksProperNoetherian : Prop :=
  ∀ {I : Type u} [Category.{u} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (_ : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    [IsProper ((Over.pullback (c.π.app i₀)).map f₀).left]
    [IsNoetherian Y₀.left] [IsSeparated f₀.left],
    ∃ (i : I) (hi : i ⟶ i₀), IsProper ((Over.pullback (D.map hi)).map f₀).left

section Proper

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D)

/-- For `X` over `S`, properness of `X.hom` is properness of `X → 𝟙`. -/
theorem isProper_pullback_toTerminal_iff {S T : Scheme.{u}} (g : T ⟶ S) (X : Over S) :
    IsProper ((Over.pullback g).map (Over.homMk X.hom : X ⟶ Over.mk (𝟙 S))).left ↔
      IsProper ((Over.pullback g).obj X).hom := by
  haveI : MorphismProperty.RespectsIso (@IsProper : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact ZInQ.Contrib.CloudW01Spread.pullback_to_identity_iff (@IsProper) g X

/-- **`ProperDescendsFor` from the Stacks Noetherian properness theorem.**  Stage Noetherianity is
required; separatedness at the stage is derived. -/
theorem properDescendsFor_of_stacksNoetherian (hS : StacksProperNoetherian.{u}) (hc : IsLimit c)
    (hnoeth : ∀ i, IsNoetherian (D.obj i)) : ProperDescendsFor D c := by
  intro i X hlfp hqc hqs hpr
  haveI : EssentiallySmall.{u} I := inferInstance
  haveI := hlfp
  haveI := hqc
  haveI := hqs
  -- 1. separatedness at a stage
  obtain ⟨j, a, hsep⟩ := exists_isSeparated_next hc X (by
    haveI := hpr
    infer_instance)
  -- 2. the stage object and its structure map to the terminal object of `Over (D.obj j)`
  let X₀ := (Over.pullback (D.map a)).obj X
  let Y₀ : Over (D.obj j) := Over.mk (𝟙 (D.obj j))
  let f₀ : X₀ ⟶ Y₀ := Over.homMk X₀.hom
  haveI : CompactSpace X₀.left := QuasiCompact.compactSpace_of_compactSpace X₀.hom
  haveI : QuasiSeparatedSpace X₀.left := quasiSeparatedSpace_of_quasiSeparated X₀.hom
  haveI : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj j))
  haveI : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType X₀.hom)
  haveI : IsNoetherian Y₀.left := hnoeth j
  haveI : IsSeparated f₀.left := hsep
  haveI : MorphismProperty.RespectsIso (@IsProper : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hpr₀ : IsProper ((Over.pullback (c.π.app j)).obj X₀).hom :=
    prop_of_iso (@IsProper) ((stθ D c a).app X) hpr
  haveI : IsProper ((Over.pullback (c.π.app j)).map f₀).left :=
    (isProper_pullback_toTerminal_iff (c.π.app j) X₀).2 hpr₀
  -- 3. the Stacks theorem at the stage
  obtain ⟨k, b, hk⟩ := hS D c hc j X₀ Y₀ f₀
  have hk' : IsProper ((Over.pullback (D.map b)).obj X₀).hom :=
    (isProper_pullback_toTerminal_iff (D.map b) X₀).1 hk
  -- 4. back to a base change of the original stage object
  refine ⟨k, b ≫ a, ?_⟩
  have e : (Over.pullback (D.map (b ≫ a))).obj X ≅ (Over.pullback (D.map b)).obj X₀ :=
    ((pbNat (D.map b) (D.map a) (D.map (b ≫ a)) (D.map_comp b a).symm).app X).symm
  exact prop_of_iso (@IsProper) e hk'

end Proper

/-- The stages of an ind-étale presentation over a Noetherian ring are Noetherian schemes. -/
theorem isNoetherian_specDiagram_of_etale {R : Type u} [CommRing R] [IsNoetherianRing R]
    {S : CommAlgCat.{u} R} {J : Type u} [SmallCategory J] (pres : ColimitPresentation J S)
    (het : ∀ j : J, Algebra.Etale R (pres.diag.obj j)) (j : Jᵒᵖ) :
    IsNoetherian ((specDiagram pres).obj j) := by
  rw [specDiagram_obj]
  haveI := het j.unop
  haveI : Algebra.FiniteType R (pres.diag.obj j.unop) := inferInstance
  haveI : IsNoetherianRing (pres.diag.obj j.unop) := Algebra.FiniteType.isNoetherianRing R _
  infer_instance

/-- **`ProperDescendsFor` for an ind-étale presentation over a Noetherian ring, from the Stacks
Noetherian properness theorem.** -/
theorem properDescendsFor_specDiagram {R : Type u} [CommRing R] [IsNoetherianRing R]
    {S : CommAlgCat.{u} R} {J : Type u} [SmallCategory J] [IsFiltered J]
    (pres : ColimitPresentation J S) (het : ∀ j : J, Algebra.Etale R (pres.diag.obj j))
    (hS : StacksProperNoetherian.{u}) :
    ProperDescendsFor (specDiagram pres) (specCone pres) :=
  properDescendsFor_of_stacksNoetherian (specDiagram pres) (specCone pres) hS
    (isLimit_specCone pres) (isNoetherian_specDiagram_of_etale pres het)

end ZInQ.Contrib.CloudR2NOS.Spreadout
