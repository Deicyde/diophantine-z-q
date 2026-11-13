import ZInQKernel.Contrib.Dim.Trdeg

/-!
# Dimension of an integral scheme of finite type over a field

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task dim-contrib, 2026-11-13,
adopting task curve-infra, `scratch/curve-infra/`). Mathlib only.

## Main definitions

* `ZInQ.Contrib.Dim.functionFieldAlgebra K X f`: the `K`-algebra structure on the function field
  `K(X)` of an integral scheme `X` over `Spec K`, through `K ≅ Γ(Spec K, ⊤) → Γ(X, ⊤) → K(X)`.

## Main results

* `ZInQ.Contrib.Dim.topologicalKrullDim_eq_trdeg_functionField`: for an integral scheme `X`,
  locally of finite type over a field `K`, `dim X = trdeg_K K(X)`.
* `ZInQ.Contrib.Dim.topologicalKrullDim_affineOpen_eq_trdeg_functionField`: the same for every
  nonempty affine open of `X`.

Sources (STANDARD; numbering UNVERIFIED): Hartshorne, *Algebraic Geometry*, I Prop. 1.7,
Thm. 1.8A and Ex. II.3.20; the Stacks Project, *Varieties*, section "Dimension of varieties".
The named statement `DimEqTrdeg` is curve-infra's, unchanged up to the name of the algebra
structure (`fnFieldAlgebra` there).
-/

namespace ZInQ.Contrib.Dim

open AlgebraicGeometry CategoryTheory

universe u

/-- The top open of a nonempty scheme is nonempty. -/
instance nonempty_top_opens (X : Scheme.{u}) [Nonempty X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Nonempty.some inferInstance, trivial⟩⟩

/-- The `K`-algebra structure on the function field of an integral scheme `X` over `Spec K`,
through `K ≅ Γ(Spec K, ⊤) → Γ(X, ⊤) → K(X)`. -/
noncomputable abbrev functionFieldAlgebra (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) : Algebra K X.functionField :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫ X.germToFunctionField ⊤).hom.toAlgebra

/-- The `K`-algebra structure on `Γ(X, U)` through `f : X ⟶ Spec K`. -/
noncomputable abbrev sectionsAlgebra (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) : Algebra K Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra

/-- On a nonempty affine open `U` of an integral scheme `X`, locally of finite type over a field
`K`: `dim U = trdeg_K K(X)`. -/
theorem topologicalKrullDim_affineOpen_eq_trdeg_functionField (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := functionFieldAlgebra K X f
    topologicalKrullDim U = ((Algebra.trdeg K X.functionField).toENat : WithBot ℕ∞) := by
  let := functionFieldAlgebra K X f
  let := sectionsAlgebra K X f U
  have hft : Algebra.FiniteType K Γ(X, U) := by
    have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
    exact h1.comp h2
  have : IsScalarTower K Γ(X, U) X.functionField := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫ X.germToFunctionField ⊤).hom x =
      (X.germToFunctionField U).hom
        (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ U le_top).hom x)
    rw [← CommRingCat.comp_apply]
    congr 2
    simp only [Category.assoc, Scheme.Hom.appLE, Scheme.Hom.appTop]
    congr 2
    exact (X.presheaf.germ_res (homOfLE le_top) _ _).symm
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  rw [trdeg_eq_of_isFractionRing K Γ(X, U) X.functionField, ← ringKrullDim_eq_trdeg K Γ(X, U),
    show topologicalKrullDim U = topologicalKrullDim U.toScheme from rfl,
    topologicalKrullDim_eq_of_iso hU.isoSpec, topologicalKrullDim_spec]

/-- **Dimension equals transcendence degree.** For an integral scheme `X`, locally of finite type
over a field `K`, `dim X = trdeg_K K(X)`. -/
theorem topologicalKrullDim_eq_trdeg_functionField (K : Type u) [Field K] (X : Scheme.{u})
    [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] :
    letI := functionFieldAlgebra K X f
    topologicalKrullDim X = ((Algebra.trdeg K X.functionField).toENat : WithBot ℕ∞) := by
  let := functionFieldAlgebra K X f
  let ι := {U : X.Opens // IsAffineOpen U ∧ (U : Set X).Nonempty}
  have hcov : ∀ x : X, ∃ i : ι, x ∈ Set.range (fun y : (i.1 : Set X) => (y : X)) := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨V, hV, ⟨x, hxV⟩⟩, ⟨x, hxV⟩, rfl⟩
  rw [topologicalKrullDim_eq_iSup_of_isOpenEmbedding (Y := fun i : ι => (i.1 : Set X))
    (fun i y => (y : X)) (fun i => i.1.isOpen.isOpenEmbedding_subtypeVal) hcov]
  have : Nonempty ι := by
    obtain ⟨i, -⟩ := hcov (Nonempty.some inferInstance)
    exact ⟨i⟩
  have : ∀ i : ι, topologicalKrullDim (i.1 : Set X) =
      ((Algebra.trdeg K X.functionField).toENat : WithBot ℕ∞) := by
    intro i
    have : Nonempty i.1 := i.2.2.to_subtype
    exact topologicalKrullDim_affineOpen_eq_trdeg_functionField K X f i.1 i.2.1
  simp only [this, ciSup_const]

/-! ## Named statement (curve-infra) -/

/-- **(AD), general form: dimension equals transcendence degree.** Step (AD) of curve-glue's
image-plane step, in the general form cited by curve-glue §6 and §8 ("the Krull dimension of a
finitely generated `K`-domain equals the transcendence degree of its fraction field").
For an integral scheme `X` locally of finite type over a field `K`, the Krull dimension of `X`
equals the transcendence degree over `K` of its function field `K(X)` (with the `K`-algebra
structure induced by `f`). Source as in the module docstring. Glue: proved here
(`dimEqTrdeg`) from Mathlib's Noether normalization. -/
def DimEqTrdeg : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f],
    letI := functionFieldAlgebra K X f
    topologicalKrullDim X = ((Algebra.trdeg K X.functionField).toENat : WithBot ℕ∞)

theorem dimEqTrdeg : DimEqTrdeg := by
  intro K _ X _ f _
  exact topologicalKrullDim_eq_trdeg_functionField K X f

end ZInQ.Contrib.Dim
