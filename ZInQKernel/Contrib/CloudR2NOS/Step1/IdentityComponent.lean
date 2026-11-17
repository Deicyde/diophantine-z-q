/-
H5 FIX EDITION STEP-F2 (NEW edition, 2026-11-17, H5 lane3 ). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step1-i1/src/ZInQKernel/Contrib/CloudR2NOS/Step1/IdentityComponent.lean (sha256 a8b12937aa060b70cb62743e1cf6f4c650b79b113de0574df7ea317dc3efe2fb).
Body change relative to the base: ONLY P5, the line `open CategoryTheory.CartesianMonoidalCategory` inserted before `namespace` (record step-fix2/FIX_RECORD_STEP_F2.json). Any header below describes the BASE edition.
-/
/-
H5 lane3 Step 1: `IdentityComponentClosedUnderOps` (GM3Assembly.lean) PROVED from C5's
`GeomIrreducibleOverAlgClosed` and ONE new Mathlib-gap obligation, `UniversallyOpenOverField`.
2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

The proof:
* Take `C_red`, the reduced induced closed subscheme on the component `C`. It is irreducible
  (`irreducibleSpaceOfClosedImmersionRange`), geometrically irreducible
  (`GeomIrreducibleOverAlgClosed`) and universally open over `K`.
* So `C_red ×_K C_red` is irreducible (Mathlib Geometrically/Irreducible.lean:111 instance).
* Topological lemma `range_subset_of_irreducible`: if `P` is irreducible, `g` is continuous and
  `C ⊆ closure (range g)` with `C` a maximal irreducible set, then `range g ⊆ C`.
* Multiplication `g₁ = (ι_C ⊗ ι_C) ≫ μ`: its range contains `C` via the section
  `c ↦ (c, e)` (unit law `lift 𝟙 (toUnit ≫ η) ≫ μ = 𝟙`). So `range g₁ ⊆ C`. A point of
  `G ×_K G` with both projections in `C` lies in the range of `ι_C ⊗ ι_C` (Mathlib
  `Scheme.Pullback.range_map`).
* Inverse `g₂ = (ι_C ⊗ (ι_C ≫ ι)) ≫ μ`: its range contains `C` via `c ↦ (c, e)`. So
  `ι(c) = g₂(e, c) ∈ C`.

New obligation (TRUE; Stacks 0383, any morphism to the spectrum of a field is universally open;
not an instance in this Mathlib pin): `UniversallyOpenOverField`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.ReducedSubscheme
import ZInQKernel.Contrib.CloudR2NOS.Step1.GM3Small

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory TopologicalSpace
open scoped CategoryTheory.MonObj

open CategoryTheory.CartesianMonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- Obligation (TRUE; Stacks 0383): morphisms to the spectrum of a field are universally open. -/
def UniversallyOpenOverField : Prop :=
  ∀ {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)), UniversallyOpen f

/-- PROVED (topology): a continuous image of an irreducible space whose closure contains a maximal
irreducible set `C` lies in `C`. -/
theorem range_subset_of_irreducible {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]
    [IrreducibleSpace P] {C : Set X} (hC : C ∈ irreducibleComponents X) (g : P → X)
    (hg : Continuous g) (hsub : C ⊆ closure (Set.range g)) : Set.range g ⊆ C := by
  have hirr : IsIrreducible (closure (Set.range g)) := by
    rw [← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ P).image g hg.continuousOn).closure
  exact subset_closure.trans (hC.2 hirr hsub)

theorem identityComponentClosedUnderOps (hI : GeomIrreducibleOverAlgClosed.{u})
    (hUO : UniversallyOpenOverField.{u}) : IdentityComponentClosedUnderOps.{u} := by
  intro K _ _ G _ _ C hC he
  let Cc : Closeds G.X.left := ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩
  let ιC := (Scheme.IdealSheafData.vanishingIdeal Cc).subschemeι
  haveI : IsReduced (Scheme.IdealSheafData.vanishingIdeal Cc).subscheme :=
    isReducedSubschemeVanishingIdeal Cc
  have hrange : Set.range ιC.base = C := range_subschemeι_vanishingIdeal Cc
  haveI : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Cc).subscheme :=
    irreducibleSpaceOfClosedImmersionRange ιC (by rw [hrange]; exact hC.1)
  let Co : Over (Spec (CommRingCat.of K)) := Over.mk (ιC ≫ G.X.hom)
  let jo : Co ⟶ G.X := Over.homMk ιC rfl
  haveI : LocallyOfFiniteType Co.hom := inferInstance
  haveI : GeometricallyIrreducible Co.hom := hI Co.hom
  haveI : UniversallyOpen Co.hom := hUO Co.hom
  haveI : IrreducibleSpace (Co ⊗ Co).left :=
    (inferInstance : IrreducibleSpace (Limits.pullback Co.hom Co.hom))
  -- the unit of `C_red`
  have h1 : Set.range (η[G.X] : Pt K ⟶ G.X).left.base ⊆ (Cc : Set G.X.left) := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint K)]
    exact he
  let eC : Pt K ⟶ Co := Over.homMk (liftToReduced Cc _ h1) (by
    change liftToReduced Cc _ h1 ≫ ιC ≫ G.X.hom = _
    rw [← Category.assoc, liftToReduced_fac]
    exact Over.w (η[G.X] : Pt K ⟶ G.X))
  have heC : eC ≫ jo = η[G.X] := Over.OverMorphism.ext (liftToReduced_fac Cc _ h1)
  -- the section `c ↦ (c, e)` and the unit law
  have hsec : ∀ (φ : Co ⟶ G.X), lift (𝟙 Co) (toUnit Co ≫ eC) ≫ (jo ⊗ₘ φ) ≫ μ[G.X] =
      jo * (toUnit Co ≫ eC ≫ φ) := by
    intro φ
    rw [← Category.assoc, lift_map, Category.id_comp, ← MonObj.Hom.mul_def, Category.assoc]
  have hC_sub : ∀ φ : Co ⟶ G.X, eC ≫ φ = η[G.X] →
      C ⊆ closure (Set.range ((jo ⊗ₘ φ) ≫ μ[G.X]).left.base) := by
    intro φ hφ c hc
    rw [← hrange] at hc
    obtain ⟨c', rfl⟩ := hc
    have hmul : lift (𝟙 Co) (toUnit Co ≫ eC) ≫ (jo ⊗ₘ φ) ≫ μ[G.X] = jo := by
      rw [hsec, hφ, ← MonObj.Hom.one_def, mul_one]
    refine subset_closure ⟨(lift (𝟙 Co) (toUnit Co ≫ eC)).left.base c', ?_⟩
    exact congrArg (fun ψ : Co ⟶ G.X => ψ.left.base c') hmul
  -- (a) closure under multiplication
  have hrange₁ : Set.range ((jo ⊗ₘ jo) ≫ μ[G.X]).left.base ⊆ C :=
    range_subset_of_irreducible hC _ (Scheme.Hom.continuous _) (hC_sub jo heC)
  -- (b) closure under inversion
  have hη : eC ≫ (jo ≫ ι[G.X]) = η[G.X] := by
    rw [← Category.assoc, heC, GrpObj.one_inv]
  have hrange₂ : Set.range ((jo ⊗ₘ (jo ≫ ι[G.X])) ≫ μ[G.X]).left.base ⊆ C :=
    range_subset_of_irreducible hC _ (Scheme.Hom.continuous _) (hC_sub (jo ≫ ι[G.X]) hη)
  refine ⟨fun p hp1 hp2 => ?_, fun a ha => ?_⟩
  · have hp : p ∈ Set.range (jo ⊗ₘ jo).left.base := by
      have := Scheme.Pullback.range_map Co.hom Co.hom G.X.hom G.X.hom ιC ιC (𝟙 _)
        (by simp [Co]) (by simp [Co])
      change p ∈ Set.range (pullback.map Co.hom Co.hom G.X.hom G.X.hom ιC ιC (𝟙 _) _ _)
      rw [this]
      exact ⟨by rw [hrange]; exact hp1, by rw [hrange]; exact hp2⟩
    obtain ⟨q, rfl⟩ := hp
    exact hrange₁ ⟨q, rfl⟩
  · rw [← hrange] at ha
    obtain ⟨a', rfl⟩ := ha
    -- `ι(a) = μ(e, ι a)` is the image of the point `(e, a')` of `C_red ×_K C_red`
    have hinv : lift (toUnit Co ≫ eC) (𝟙 Co) ≫ (jo ⊗ₘ (jo ≫ ι[G.X])) ≫ μ[G.X] =
        jo ≫ ι[G.X] := by
      rw [← Category.assoc, lift_map, Category.id_comp, ← MonObj.Hom.mul_def, Category.assoc,
        heC, ← MonObj.Hom.one_def, one_mul]
    have hpt := congrArg (fun ψ : Co ⟶ G.X => ψ.left.base a') hinv
    have h2 : (lift (toUnit Co ≫ eC) (𝟙 Co) ≫ (jo ⊗ₘ (jo ≫ ι[G.X])) ≫ μ[G.X]).left.base a' ∈ C :=
      hrange₂ ⟨(lift (toUnit Co ≫ eC) (𝟙 Co)).left.base a', rfl⟩
    simp only at hpt
    rw [hpt] at h2
    exact h2

/-- E3b with every one of my obligations discharged. It rests only on C5's
`TranslateComponent`, `GeomReducedOverAlgClosed`, `GeomIrreducibleOverAlgClosed` and the new
`UniversallyOpenOverField`. -/
theorem identityComponentIntegral_final (hT : TranslateComponent.{u})
    (hR : GeomReducedOverAlgClosed.{u}) (hI : GeomIrreducibleOverAlgClosed.{u})
    (hUO : UniversallyOpenOverField.{u}) : IdentityComponentIntegral.{u} :=
  identityComponentIntegral hT (identityComponentClosedUnderOps hI hUO)
    (reducedSubgroupOfClosedSubset_final hR) irreducibleSpaceOfClosedImmersionRange hR hI

end ZInQ.Contrib.CloudR2NOS.Step1
