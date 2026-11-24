/-
Multiplication-etale construction: CanonicalFibres.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import ZInQKernel.Contrib.MulEtale.Direct.LocalPromotion

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace H101DirectGlobalDetection.CanonicalFibres
universe u

/-- Exact original canonical map between actual scheme-theoretic fibres. -/
def fiberHom {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    (f ≫ g).fiber s ⟶ g.fiber s :=
  Limits.pullback.lift ((f ≫ g).fiberι s ≫ f) ((f ≫ g).fiberToSpecResidueField s)
    ((f ≫ g).fiber_fac s)

lemma fiberHom_fiberι {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    fiberHom f g s ≫ g.fiberι s = (f ≫ g).fiberι s ≫ f :=
  Limits.pullback.lift_fst ..

lemma fiberHom_fiberToSpecResidueField {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    fiberHom f g s ≫ g.fiberToSpecResidueField s =
      (f ≫ g).fiberToSpecResidueField s :=
  Limits.pullback.lift_snd ..

/-- The canonical fibre map carries the ACTUAL point asFiber x to asFiber(f x). -/
theorem fiberHom_asFiber {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    fiberHom f g ((f ≫ g) x) ((f ≫ g).asFiber x) = g.asFiber (f x) := by
  have hpoint : (f ≫ g) x = g (f x) := Scheme.Hom.comp_apply f g x
  have hιcast : ∀ {s t : S} (h : s = t) (v : (f ≫ g).fiber s),
      (f ≫ g).fiberι t (h ▸ v) = (f ≫ g).fiberι s v := by
    intro s t h v
    cases h
    rfl
  let v : (f ≫ g).fiber (g (f x)) := hpoint ▸ (f ≫ g).asFiber x
  have hv : (f ≫ g).fiberι (g (f x)) v = x :=
    (hιcast hpoint ((f ≫ g).asFiber x)).trans
      (Scheme.Hom.fiberι_asFiber (f ≫ g) x)
  have H : fiberHom f g (g (f x)) v = g.asFiber (f x) := by
    apply (g.fiberι (g (f x))).isEmbedding.injective
    calc
      g.fiberι (g (f x)) (fiberHom f g (g (f x)) v) =
          (fiberHom f g (g (f x)) ≫ g.fiberι (g (f x))) v :=
        (Scheme.Hom.comp_apply (fiberHom f g (g (f x))) (g.fiberι (g (f x))) v).symm
      _ = ((f ≫ g).fiberι (g (f x)) ≫ f) v :=
        congrArg (fun a : (f ≫ g).fiber (g (f x)) ⟶ Y => a v)
          (fiberHom_fiberι f g (g (f x)))
      _ = f ((f ≫ g).fiberι (g (f x)) v) :=
        Scheme.Hom.comp_apply ((f ≫ g).fiberι (g (f x))) f v
      _ = f x := congrArg f hv
      _ = g.fiberι (g (f x)) (g.asFiber (f x)) :=
        (Scheme.Hom.fiberι_asFiber g (f x)).symm
  have hmapcast : ∀ {s t : S} (h : s = t) (u : (f ≫ g).fiber s),
      HEq (fiberHom f g s u) (fiberHom f g t (h ▸ u)) := by
    intro s t h u
    cases h
    rfl
  exact eq_of_heq
    ((hmapcast hpoint ((f ≫ g).asFiber x)).trans (heq_of_eq H))

/-- Stalk-map naturality for an ACTUAL commuting square, including the
canonical source-point equality map. No ring square is assumed separately. -/
theorem stalkMap_square
    {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (iX : X' ⟶ X) (iY : Y' ⟶ Y)
    (hsq : f' ≫ iY = iX ≫ f) (x' : X') :
    (Y.presheaf.stalkCongr
        (.of_eq (congrArg (fun h : X' ⟶ Y => h x') hsq).symm)).hom ≫
      iY.stalkMap (f' x') ≫ f'.stalkMap x' =
        f.stalkMap (iX x') ≫ iX.stalkMap x' := by
  have hcongr : ∀ (a b : X' ⟶ Y) (h : a = b),
      (Y.presheaf.stalkCongr
        (.of_eq (congrArg (fun q : X' ⟶ Y => q x') h).symm)).hom ≫
          a.stalkMap x' = b.stalkMap x' := by
    intro a b h
    cases h
    exact (Scheme.Hom.stalkMap_congr_hom a a rfl x').symm
  have H := hcongr (f' ≫ iY) (iX ≫ f) hsq
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at H
  exact H

/-- Structural smoothness supplies formal smoothness of both ACTUAL stalk
algebra maps R -> S0 and R -> T0. Smoothness of f itself is never an input. -/
theorem structuralStalkMaps_formallySmooth
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Smooth g] [Smooth (f ≫ g)] (x : X) :
    (g.stalkMap (f x)).hom.FormallySmooth ∧
      ((f.stalkMap x).hom.comp (g.stalkMap (f x)).hom).FormallySmooth := by
  constructor
  · apply (Scheme.Hom.mem_smoothLocus).1
    rw [g.smoothLocus_eq_top]
    trivial
  · rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
    apply (Scheme.Hom.mem_smoothLocus).1
    rw [(f ≫ g).smoothLocus_eq_top]
    trivial

/-- Source LFP is derived from structural smoothness and the honest
LFPFromComposite source provider. It is not required as a new H101 premise. -/
theorem locallyOfFinitePresentation_of_smooth_structural
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Smooth g] [Smooth (f ≫ g)] : LocallyOfFinitePresentation f :=
  ZInQ.Contrib.MulEtale.StacksVendor.locallyOfFinitePresentation_of_comp f g

/-- An ACTUAL etale fibre morphism has an ACTUAL formally-etale stalk map.
This does not assume formal etaleness of f.stalkMap on the total space. -/
theorem formallyEtale_stalkMap_of_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (x : X) :
    (f.stalkMap x).hom.FormallyEtale := by
  letI := (f.stalkMap x).hom.toAlgebra
  change Algebra.FormallyEtale (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
  apply Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
  constructor
  · change (f.stalkMap x).hom.FormallyUnramified
    exact AlgebraicGeometry.FormallyUnramified.stalkMap f x
  · change (f.stalkMap x).hom.FormallySmooth
    apply (Scheme.Hom.mem_smoothLocus).1
    rw [f.smoothLocus_eq_top]
    trivial

/-- Actual formal-etale stalk maps cover f by actual etale open charts;
this reuses LocalPromotion rather than reauthoring its chart proofs. -/
theorem etale_of_formallyEtale_stalkMaps
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (H : ∀ x : X, (f.stalkMap x).hom.FormallyEtale) : Etale f := by
  letI : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @Etale.{u}) (Q := @RingHom.Etale)
  have hcover :
      (⨆ V : {V : X.Opens // Etale (V.ι ≫ f)}, V.1) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    obtain ⟨V, _, hxV, HE⟩ :=
      H101DirectFieldRoute.LocalPromotion.exists_etale_open_of_formallyEtale_stalkMap
        f x (H x)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, HE⟩, hxV⟩
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale.{u})
    (fun V : {V : X.Opens // Etale (V.ι ≫ f)} => V.1) hcover (fun V => V.2)

end H101DirectGlobalDetection.CanonicalFibres
