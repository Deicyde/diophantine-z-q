import RaynaudWild.FrobFixedFieldV001
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Spreading out a morphism from `Spec Ω[M]` to a finite residue field

Let `k` be a finite field, `Ω / k` algebraic with a residue Frobenius `σ` (`σ x = x ^ |k|`), and
`M` a commutative monoid.  The group ring `Ω[M]` is the increasing union of the subrings
`Kₙ[M]`, `Kₙ` the fixed field of `σ ^ n!`.

* `stageFunctor`, `stageCocone`, `stageCoconeIsColimit`: `Ω[M] = colim Kₙ[M]` in commutative rings;
* `stageDiagram`, `stageCone`, `stageConeIsLimit`: `Spec Ω[M] = lim Spec Kₙ[M]` in schemes, a
  cofiltered limit of affine schemes over `Spec k`;
* `exists_frob_invariant`: for every `k`-scheme `X` locally of finite presentation (the special
  fibre of a smooth group scheme over the valuation ring, or an open subscheme of it) and every
  `k`-morphism `x : Spec Ω[M] → X`, there is `n` with `x ∘ Spec(σ^{n!} on coefficients) = x`.
  The spread-out step is Mathlib's EGA IV 8.14.2 for cofiltered limits with affine transitions.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace RaynaudWild.FrobDescent

variable {k Ω : Type} [Field k] [Finite k] [Field Ω] [Algebra k Ω] (σ : Ω ≃ₐ[k] Ω)
  (M : Type) [CommMonoid M]

/-- The stages `Kₙ[M]` with the coefficient inclusions. -/
def stageFunctor : ℕ ⥤ CommRingCat where
  obj n := CommRingCat.of (MonoidAlgebra (fixedFrob σ n) M)
  map {n m} h := CommRingCat.ofHom (MonoidAlgebra.mapAlgHom M
    (IntermediateField.inclusion (fixedFrob_mono σ (leOfHom h)))).toRingHom
  map_id n := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    apply MonoidAlgebra.coeff_injective
    ext m
    simp
  map_comp {n m l} f g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    apply MonoidAlgebra.coeff_injective
    ext j
    simp

/-- The cocone `Kₙ[M] → Ω[M]`. -/
def stageCocone : Cocone (stageFunctor σ M) where
  pt := CommRingCat.of (MonoidAlgebra Ω M)
  ι :=
    { app n := CommRingCat.ofHom (MonoidAlgebra.mapAlgHom M (fixedFrob σ n).val).toRingHom
      naturality {n m} h := by
        have hcomp : (MonoidAlgebra.mapAlgHom M (fixedFrob σ m).val).comp
            (MonoidAlgebra.mapAlgHom M (IntermediateField.inclusion (fixedFrob_mono σ (leOfHom h)))) =
            MonoidAlgebra.mapAlgHom M (fixedFrob σ n).val := by
          rw [← MonoidAlgebra.mapRangeAlgHom_comp]
          congr 1
        refine (CommRingCat.hom_ext ?_).trans (Category.comp_id _).symm
        exact congrArg AlgHom.toRingHom hcomp }

theorem coeff_stageCocone_ι (n : ℕ) (x : MonoidAlgebra (fixedFrob σ n) M) (j : M) :
    (((stageCocone σ M).ι.app n) x : MonoidAlgebra Ω M).coeff j = (x.coeff j : Ω) := by
  change ((MonoidAlgebra.mapAlgHom M (fixedFrob σ n).val) x).coeff j = _
  rw [MonoidAlgebra.coeff_mapAlgHom]
  rfl

theorem coeff_stageFunctor_map {n m : ℕ} (h : n ⟶ m) (x : MonoidAlgebra (fixedFrob σ n) M)
    (j : M) : ((((stageFunctor σ M).map h) x : MonoidAlgebra (fixedFrob σ m) M).coeff j : Ω) =
      (x.coeff j : Ω) := by
  change (((MonoidAlgebra.mapAlgHom M (IntermediateField.inclusion _)) x).coeff j : Ω) = _
  rw [MonoidAlgebra.coeff_mapAlgHom]
  rfl

/-- `Ω[M]` is the filtered colimit of the `Kₙ[M]`. -/
def stageCoconeIsColimit [Algebra.IsAlgebraic k Ω] (hσ : ∀ x : Ω, σ x = x ^ Nat.card k) :
    IsColimit (stageCocone σ M) := by
  haveI : ReflectsColimit (stageFunctor σ M) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf
  · intro x
    change MonoidAlgebra Ω M at x
    classical
    choose N hN using fun j : M => exists_mem_fixedFrob σ hσ (x.coeff j)
    let n := x.coeff.support.sup N
    have hmem : ∀ j, x.coeff j ∈ fixedFrob σ n := by
      intro j
      by_cases hj : j ∈ x.coeff.support
      · exact fixedFrob_mono σ (Finset.le_sup hj) (hN j)
      · rw [Finsupp.notMem_support_iff.mp hj]
        exact (fixedFrob σ n).zero_mem
    have hrange : x ∈ Set.range (MonoidAlgebra.map (M := M)
        ((fixedFrob σ n).val.toRingHom.toAddMonoidHom)) := by
      rw [MonoidAlgebra.range_map]
      intro j
      exact ⟨⟨x.coeff j, hmem j⟩, rfl⟩
    obtain ⟨xi, hxi⟩ := hrange
    refine ⟨n, xi, ?_⟩
    change x = ((stageCocone σ M).ι.app n) xi
    apply MonoidAlgebra.coeff_injective
    ext j
    rw [coeff_stageCocone_ι, ← hxi, MonoidAlgebra.coeff_map, Finsupp.mapRange_apply]
    rfl
  · intro i j xi xj h
    change MonoidAlgebra (fixedFrob σ i) M at xi
    change MonoidAlgebra (fixedFrob σ j) M at xj
    change (MonoidAlgebra.mapAlgHom M (fixedFrob σ i).val) xi =
      (MonoidAlgebra.mapAlgHom M (fixedFrob σ j).val) xj at h
    have hc : ∀ m, (MonoidAlgebra.mapAlgHom M (fixedFrob σ i).val xi).coeff m =
        (MonoidAlgebra.mapAlgHom M (fixedFrob σ j).val xj).coeff m := fun m => by rw [h]
    simp only [MonoidAlgebra.coeff_mapAlgHom] at hc
    refine ⟨max i j, homOfLE (le_max_left i j), homOfLE (le_max_right i j), ?_⟩
    change (MonoidAlgebra.mapAlgHom M (IntermediateField.inclusion _)) xi =
      (MonoidAlgebra.mapAlgHom M (IntermediateField.inclusion _)) xj
    apply MonoidAlgebra.coeff_injective
    ext m
    simp only [MonoidAlgebra.coeff_mapAlgHom, IntermediateField.coe_inclusion]
    exact hc m

/-- The cofiltered diagram `n ↦ Spec Kₙ[M]` of affine schemes. -/
def stageDiagram : ℕᵒᵖ ⥤ Scheme := (stageFunctor σ M).op ⋙ Scheme.Spec

/-- The cone `Spec Ω[M] → Spec Kₙ[M]`. -/
def stageCone : Cone (stageDiagram σ M) := Scheme.Spec.mapCone (stageCocone σ M).op

/-- `Spec Ω[M]` is the limit of the `Spec Kₙ[M]`. -/
def stageConeIsLimit [Algebra.IsAlgebraic k Ω] (hσ : ∀ x : Ω, σ x = x ^ Nat.card k) :
    IsLimit (stageCone σ M) :=
  isLimitOfPreserves Scheme.Spec (stageCoconeIsColimit σ M hσ).op

/-- The structure morphisms `Spec Kₙ[M] → Spec k`. -/
def stageToBase : stageDiagram σ M ⟶ (Functor.const ℕᵒᵖ).obj (Spec (CommRingCat.of k)) where
  app n := Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra (fixedFrob σ n.unop) M)))
  naturality {n n'} f := by
    refine ((Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)).trans (Category.comp_id _).symm
    apply CommRingCat.hom_ext
    exact (MonoidAlgebra.mapAlgHom M (IntermediateField.inclusion _)).comp_algebraMap

/-- **Spreading out to a finite residue field.** A `k`-morphism from `Spec Ω[M]` to a `k`-scheme
locally of finite presentation is invariant under `σ ^ n!` acting on coefficients, for some
`n`. -/
theorem exists_frob_invariant [Algebra.IsAlgebraic k Ω] (hσ : ∀ x : Ω, σ x = x ^ Nat.card k)
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFinitePresentation X.hom]
    (x : Spec (CommRingCat.of (MonoidAlgebra Ω M)) ⟶ X.left)
    (hx : x ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra Ω M)))) :
    ∃ n : ℕ, Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapAlgHom M
      ((σ ^ n.factorial : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω)).toRingHom) ≫ x = x := by
  haveI : ∀ i, IsAffine ((stageDiagram σ M).obj i) := fun i => inferInstanceAs (IsAffine (Spec _))
  haveI : ∀ {i j} (f : i ⟶ j), IsAffineHom ((stageDiagram σ M).map f) := fun _ => inferInstance
  haveI : ∀ i, CompactSpace ((stageDiagram σ M).obj i) := fun _ => inferInstance
  haveI : ∀ i, QuasiSeparatedSpace ((stageDiagram σ M).obj i) := fun _ => inferInstance
  obtain ⟨n, g, hg, -⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (stageDiagram σ M) (stageToBase σ M) X.hom (stageCone σ M) (stageConeIsLimit σ M hσ) x (by
      ext n
      change Spec.map _ ≫ Spec.map _ = x ≫ X.hom
      rw [hx]
      refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
      apply CommRingCat.hom_ext
      exact (MonoidAlgebra.mapAlgHom M (fixedFrob σ n.unop).val).comp_algebraMap)
  refine ⟨n.unop, ?_⟩
  have hfix : (MonoidAlgebra.mapAlgHom M ((σ ^ n.unop.factorial : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω)).comp
      (MonoidAlgebra.mapAlgHom M (fixedFrob σ n.unop).val) =
      MonoidAlgebra.mapAlgHom M (fixedFrob σ n.unop).val := by
    rw [← MonoidAlgebra.mapRangeAlgHom_comp]
    congr 1
    ext y
    exact (mem_fixedFrob_iff σ n.unop y).mp y.2
  let σM : Spec (CommRingCat.of (MonoidAlgebra Ω M)) ⟶ Spec (CommRingCat.of (MonoidAlgebra Ω M)) :=
    Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapAlgHom M
      ((σ ^ n.unop.factorial : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω)).toRingHom)
  let ιn : Spec (CommRingCat.of (MonoidAlgebra Ω M)) ⟶
      Spec (CommRingCat.of (MonoidAlgebra (fixedFrob σ n.unop) M)) :=
    Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapAlgHom M (fixedFrob σ n.unop).val).toRingHom)
  let g' : Spec (CommRingCat.of (MonoidAlgebra (fixedFrob σ n.unop) M)) ⟶ X.left := g
  have hg' : ιn ≫ g' = x := hg
  have key : σM ≫ ιn = ιn := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom hfix
  change σM ≫ x = x
  calc σM ≫ x = σM ≫ (ιn ≫ g') := by rw [hg']
    _ = (σM ≫ ιn) ≫ g' := (Category.assoc _ _ _).symm
    _ = ιn ≫ g' := by rw [key]
    _ = x := hg'

end RaynaudWild.FrobDescent
