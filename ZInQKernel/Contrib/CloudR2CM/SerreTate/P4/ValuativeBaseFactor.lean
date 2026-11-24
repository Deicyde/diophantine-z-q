import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Properness from factorizations of valuative test maps

Every test keeps its original valuation ring and fraction field. A
factorization through a base change which is proper supplies its lift;
separatedness supplies uniqueness. No proper-fibre or open-neighborhood
criterion is substituted for the full valuative criterion.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace HDec.CMSerreTate.P4

universe u

/-- A proper morphism satisfies the existence part of the full valuative
criterion. -/
theorem properValuativeExistence {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    ValuativeCriterion.Existence f := by
  have h : IsProper f := inferInstance
  rw [IsProper.eq_valuativeCriterion] at h
  exact ValuativeCriterion.existence h.1.1.1

/-- Proper base changes through which every valuative bottom map factors
supply existence for the original morphism. The test valuation ring need
not be discrete or have characteristic zero. -/
theorem valuativeExistence_of_proper_base_factor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hFactor : ∀ S : ValuativeCommSq f,
      ∃ (Z : Scheme.{u}) (j : Z ⟶ Y) (v : Spec (CommRingCat.of S.R) ⟶ Z),
        v ≫ j = S.i₂ ∧ IsProper (pullback.snd f j)) :
    ValuativeCriterion.Existence f := by
  intro S
  obtain ⟨Z, j, v, hv, hProper⟩ := hFactor S
  letI : IsProper (pullback.snd f j) := hProper
  let ι : Spec (CommRingCat.of S.K) ⟶ Spec (CommRingCat.of S.R) :=
    Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))
  let a : Spec (CommRingCat.of S.K) ⟶ pullback f j :=
    pullback.lift S.i₁ (ι ≫ v) (by
      rw [Category.assoc, hv]
      exact S.commSq.w)
  let S' : ValuativeCommSq (pullback.snd f j) :=
    { R := S.R
      K := S.K
      i₁ := a
      i₂ := v
      commSq := ⟨by
        change a ≫ pullback.snd f j = ι ≫ v
        exact pullback.lift_snd _ _ _⟩ }
  obtain ⟨l, hl₁, hl₂⟩ := (properValuativeExistence (pullback.snd f j) S').exists_lift
  have hl₁' : ι ≫ l = a := hl₁
  have hl₂' : l ≫ pullback.snd f j = v := hl₂
  refine ⟨⟨⟨l ≫ pullback.fst f j, ?_, ?_⟩⟩⟩
  · change ι ≫ (l ≫ pullback.fst f j) = S.i₁
    rw [← Category.assoc, hl₁']
    exact pullback.lift_fst _ _ _
  · change (l ≫ pullback.fst f j) ≫ f = S.i₂
    rw [Category.assoc, pullback.condition, ← Category.assoc, hl₂', hv]

/-- With the actual finiteness and separation conditions, the preceding
factorization-and-lifting argument gives properness. -/
theorem isProper_of_proper_base_factor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [IsSeparated f] [LocallyOfFiniteType f]
    (hFactor : ∀ S : ValuativeCommSq f,
      ∃ (Z : Scheme.{u}) (j : Z ⟶ Y) (v : Spec (CommRingCat.of S.R) ⟶ Z),
        v ≫ j = S.i₂ ∧ IsProper (pullback.snd f j)) : IsProper f := by
  exact IsProper.of_valuativeCriterion f (ValuativeCriterion.iff.mpr
    ⟨valuativeExistence_of_proper_base_factor f hFactor, IsSeparated.valuativeCriterion f⟩)

end HDec.CMSerreTate.P4
