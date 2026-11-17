import ZInQKernel.Contrib.CloudR2Poincare.L1.NativeTrivialityLocus
import ZInQKernel.Contrib.CloudR2Poincare.L2.ReducedComponents
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Actual reduced closed support of the native affine triviality locus

The closed SET is given its actual radical vanishing-ideal scheme structure.
For every REDUCED parameter scheme, maps with image contained in that closed
set factor through this scheme. This is a genuine scheme/coverage result, not
an assertion that the PULLED-BACK line-bundle family is globally trivial.
Reduced-base normalized global seesaw is still needed for that last statement.

L2 owns the radical-quotient reducedness argument; this module reuses it.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Actual reduced induced closed scheme of a given closed subset. -/
def reducedClosedSupport (Y : Scheme.{u}) (Z : Closeds Y) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal Z).radical.subscheme

/-- The actual closed inclusion into the original scheme. -/
def reducedClosedSupportι (Y : Scheme.{u}) (Z : Closeds Y) : reducedClosedSupport Y Z ⟶ Y :=
  (Scheme.IdealSheafData.vanishingIdeal Z).radical.subschemeι

instance reducedClosedSupport_closed (Y : Scheme.{u}) (Z : Closeds Y) :
    IsClosedImmersion (reducedClosedSupportι Y Z) := by
  unfold reducedClosedSupportι
  infer_instance

instance reducedClosedSupport_reduced (Y : Scheme.{u}) (Z : Closeds Y) :
    AlgebraicGeometry.IsReduced (reducedClosedSupport Y Z) :=
  ZInQ.Contrib.CloudR2Poincare.L2.isReduced_radical_subscheme _

/-- Radical reduction does not change the closed point set. -/
theorem range_reducedClosedSupportι (Y : Scheme.{u}) (Z : Closeds Y) :
    Set.range (reducedClosedSupportι Y Z) = Z := by
  change Set.range (Scheme.IdealSheafData.vanishingIdeal Z).radical.subschemeι = (Z : Set Y)
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_radical,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- A reduced scheme mapping into the closed support factors through its
actual reduced induced scheme structure. No line-bundle triviality is inferred. -/
theorem exists_factor_reducedClosedSupport {T Y : Scheme.{u}}
    [AlgebraicGeometry.IsReduced T] (Z : Closeds Y) (g : T ⟶ Y)
    (h : Set.range g ⊆ Z) :
    ∃ a : T ⟶ reducedClosedSupport Y Z, a ≫ reducedClosedSupportι Y Z = g := by
  let I : Y.IdealSheafData := (Scheme.IdealSheafData.vanishingIdeal Z).radical
  have hsupport : (I.comap g).support = ⊤ := by
    rw [Scheme.IdealSheafData.support_comap]
    ext t
    change (g t ∈ I.support) ↔ True
    constructor
    · intro _; trivial
    · intro _
      change g t ∈ ((Scheme.IdealSheafData.vanishingIdeal Z).radical.support : Set Y)
      rw [Scheme.IdealSheafData.support_radical, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact h ⟨t, rfl⟩
  have hzero : I.comap g = ⊥ :=
    Scheme.IdealSheafData.support_eq_top_iff.mp hsupport
  haveI : IsIso (pullback.fst g I.subschemeι) :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hzero
  refine ⟨inv (pullback.fst g I.subschemeι) ≫ pullback.snd g I.subschemeι, ?_⟩
  change (inv (pullback.fst g I.subschemeι) ≫ pullback.snd g I.subschemeι) ≫ I.subschemeι = g
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- Exact reduced-test classification by IMAGE containment, not by a false
all-fibres-to-whole-Picard-class implication. -/
theorem factor_reducedClosedSupport_iff {T Y : Scheme.{u}}
    [AlgebraicGeometry.IsReduced T] (Z : Closeds Y) (g : T ⟶ Y) :
    (∃ a : T ⟶ reducedClosedSupport Y Z, a ≫ reducedClosedSupportι Y Z = g) ↔
      Set.range g ⊆ Z := by
  constructor
  · rintro ⟨a, ha⟩ _ ⟨t, rfl⟩
    rw [← ha, Scheme.Hom.comp_apply]
    have ht : reducedClosedSupportι Y Z (a t) ∈ Set.range (reducedClosedSupportι Y Z) :=
      ⟨a t, rfl⟩
    simpa only [range_reducedClosedSupportι] using ht
  · exact exists_factor_reducedClosedSupport Z g

/-- The actual native affine residue-fibre triviality closed subset. -/
def affineFibreTrivialityClosed
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible] : Closeds (Spec (.of R)) :=
  ⟨{y | Scheme.Pic.map
    (pullback.fst f ((Spec (.of R)).fromSpecResidueField y)) (Scheme.Pic.mk M) = 1},
    isClosed_fibrePicardClass_trivial R f M⟩

/-- Actual closed reduced scheme underlying the affine fibre-triviality set. -/
def affineReducedTrivialityLocus
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible] : Scheme.{u} :=
  reducedClosedSupport _ (affineFibreTrivialityClosed R f M)

/-- Its actual closed inclusion into the affine parameter base. -/
def affineReducedTrivialityLocusι
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible] : affineReducedTrivialityLocus R f M ⟶ Spec (.of R) :=
  reducedClosedSupportι _ (affineFibreTrivialityClosed R f M)

instance affineReducedTrivialityLocus_closed
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible] :
    IsClosedImmersion (affineReducedTrivialityLocusι R f M) :=
  reducedClosedSupport_closed _ _

instance affineReducedTrivialityLocus_reduced
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible] :
    AlgebraicGeometry.IsReduced (affineReducedTrivialityLocus R f M) :=
  reducedClosedSupport_reduced _ _

/-- Its literal closed point set equals the native fibre-triviality set. -/
theorem range_affineReducedTrivialityLocusι
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible] :
    Set.range (affineReducedTrivialityLocusι R f M) =
      {y | Scheme.Pic.map (pullback.fst f ((Spec (.of R)).fromSpecResidueField y))
        (Scheme.Pic.mk M) = 1} :=
  range_reducedClosedSupportι _ _

/-- Reduced-test IMAGE containment is represented by this actual affine closed
scheme. Global triviality of the family on the parameter scheme stays separate. -/
theorem factor_affineReducedTrivialityLocus_iff
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X T : Scheme.{u}}
    [AlgebraicGeometry.IsReduced T]
    (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible] (g : T ⟶ Spec (.of R)) :
    (∃ a : T ⟶ affineReducedTrivialityLocus R f M,
      a ≫ affineReducedTrivialityLocusι R f M = g) ↔
    ∀ t : T, Scheme.Pic.map
      (pullback.fst f ((Spec (.of R)).fromSpecResidueField (g t))) (Scheme.Pic.mk M) = 1 := by
  change (∃ a : T ⟶ reducedClosedSupport _ (affineFibreTrivialityClosed R f M),
    a ≫ reducedClosedSupportι _ (affineFibreTrivialityClosed R f M) = g) ↔ _
  rw [factor_reducedClosedSupport_iff]
  constructor
  · intro h t
    exact h ⟨t, rfl⟩
  · intro h _ hp
    obtain ⟨t, rfl⟩ := hp
    exact h t

end ZInQ.Contrib.CloudR2Poincare.L1
