/-
Multiplication-etale construction: FibreStalkNaturality.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import ZInQKernel.Contrib.MulEtale.Direct.Global.CanonicalFibres
import ZInQKernel.Contrib.MulEtale.Direct.Shared.StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
import ZInQKernel.Contrib.MulEtale.Direct.Shared.StacksFrontier.AlgebraicGeometry.FiberCotangentAssembly.Transport

noncomputable section
open CategoryTheory AlgebraicGeometry
open H101DirectGlobalDetection.CanonicalFibres
open ZInQ.Contrib.MulEtale.StacksVendor.Stacks.FiberCotangentAssembly

namespace H101DirectGlobalDetection.ActualQuotient
universe u

variable {X Y B : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ B) (x : X)

abbrev R0 := B.presheaf.stalk ((f ≫ g) x)
abbrev S0 := Y.presheaf.stalk (f x)
abbrev T0 := X.presheaf.stalk x

/-- Actual extended maximal ideals; the structural maps are native stalk maps. -/
def JS : Ideal (S0 f x) :=
  (IsLocalRing.maximalIdeal (R0 f g x)).map (g.stalkMap (f x)).hom

def JT : Ideal (T0 x) :=
  (IsLocalRing.maximalIdeal (R0 f g x)).map ((f ≫ g).stalkMap x).hom

/-- The actual stalk map sends the actual source fibre ideal into the target
fibre ideal, by native stalkMap_comp and Ideal.map_map. -/
theorem JS_le_comap_JT : JS f g x ≤ (JT f g x).comap (f.stalkMap x).hom := by
  have hmap : ∀ (R A T : Type u) [CommRing R] [CommRing A] [CommRing T]
      (i : R →+* A) (j : A →+* T) (k : R →+* T) (I : Ideal R),
      j.comp i = k → I.map i ≤ (I.map k).comap j := by
    intro R A T _ _ _ i j k I hcomp
    apply Ideal.map_le_iff_le_comap.mp
    exact ((Ideal.map_map i j).trans
      (congrArg (fun q : R →+* T => I.map q) hcomp)).le
  have hcomp : (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom =
      ((f ≫ g).stalkMap x).hom :=
    (congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp f g x)).symm
  exact hmap (R0 f g x) (S0 f x) (T0 x)
    (g.stalkMap (f x)).hom (f.stalkMap x).hom ((f ≫ g).stalkMap x).hom
    (IsLocalRing.maximalIdeal (R0 f g x)) hcomp

/-- The canonical quotient map induced by precisely f.stalkMap x. -/
def quotientMap : (S0 f x ⧸ JS f g x) →+* (T0 x ⧸ JT f g x) :=
  Ideal.quotientMap (JT f g x) (f.stalkMap x).hom (JS_le_comap_JT f g x)

/-- The actual canonical fibre point of X. -/
abbrev xFiber := (f ≫ g).asFiber x

/-- The source quotient-to-fibre equivalence is transported ONLY by the
proved equality between f_s(xFiber) and the canonical point over f x. -/
def sourceQuotientEquiv :
    (S0 f x ⧸ JS f g x) ≃+*
      ((g.fiber ((f ≫ g) x)).presheaf.stalk
        (fiberHom f g ((f ≫ g) x) (xFiber f g x))) :=
  (ZInQ.Contrib.MulEtale.StacksVendor.AlgebraicGeometry.quotientStalkEquivFiberStalk
      g (f x)).trans
    ((g.fiber ((f ≫ g) x)).presheaf.stalkCongr
      (.of_eq (fiberHom_asFiber f g x).symm)).commRingCatIsoToRingEquiv

/-- The actual target quotient-to-fibre equivalence. -/
def targetQuotientEquiv :
    (T0 x ⧸ JT f g x) ≃+*
      (((f ≫ g).fiber ((f ≫ g) x)).presheaf.stalk (xFiber f g x)) :=
  ZInQ.Contrib.MulEtale.StacksVendor.AlgebraicGeometry.quotientStalkEquivFiberStalk
    (f ≫ g) x

/-- The quotient-stalk dictionary intertwines the ACTUAL quotient map and
the ACTUAL f_s.stalkMap at the ACTUAL point. This is the missing map equation
proved from the canonical scheme square and point-congruence naturality,
not supplied as a hypothesis. -/
theorem quotientMap_fiberStalk_naturality (a : S0 f x ⧸ JS f g x) :
    targetQuotientEquiv f g x (quotientMap f g x a) =
      (fiberHom f g ((f ≫ g) x)).stalkMap (xFiber f g x)
        (sourceQuotientEquiv f g x a) := by
  let p := f ≫ g
  let s := p x
  let xf := xFiber f g x
  let mf := fiberHom f g s
  let yf := mf xf
  let y0 := g.asFiber (f x)
  let iX := p.fiberι s
  let iY := g.fiberι s
  have hX : iX xf = x := p.fiberι_asFiber x
  have hY0 : iY y0 = f x := g.fiberι_asFiber (f x)
  have hY : yf = y0 := fiberHom_asFiber f g x
  have hsq : mf ≫ iY = iX ≫ f := fiberHom_fiberι f g s
  have hy : iY yf = f x := by
    rw [hY]
    exact hY0
  let cX := (X.presheaf.stalkCongr (.of_eq hX.symm)).hom
  let cY0 := (Y.presheaf.stalkCongr (.of_eq hY0.symm)).hom
  let cY1 := (Y.presheaf.stalkCongr (.of_eq (congrArg iY hY.symm))).hom
  let cY := (Y.presheaf.stalkCongr (.of_eq hy.symm)).hom
  let dY := ((g.fiber s).presheaf.stalkCongr (.of_eq hY.symm)).hom
  have HY := Scheme.Hom.stalkMap_congr_point iY y0 yf hY.symm
  have HX := Scheme.Hom.stalkMap_congr_point f x (iX xf) hX.symm
  have hpoint : f (iX xf) = iY yf := by
    calc
      f (iX xf) = (iX ≫ f) xf := (Scheme.Hom.comp_apply iX f xf).symm
      _ = (mf ≫ iY) xf := congrArg (fun q : p.fiber s ⟶ Y => q xf) hsq.symm
      _ = iY yf := Scheme.Hom.comp_apply mf iY xf
  let cSq := (Y.presheaf.stalkCongr (.of_eq hpoint)).hom
  have HC : cSq ≫ iY.stalkMap yf ≫ mf.stalkMap xf =
      f.stalkMap (iX xf) ≫ iX.stalkMap xf := by
    have H : cSq ≫ (mf ≫ iY).stalkMap xf = (iX ≫ f).stalkMap xf :=
      (stalkMap_eq_of_eq hsq.symm xf (.of_eq hpoint)).symm
    exact (congrArg (fun q => cSq ≫ q) (Scheme.Hom.stalkMap_comp mf iY xf)).symm.trans
      (H.trans (Scheme.Hom.stalkMap_comp iX f xf))
  have hcollapse : ∀ {a b c : Y} (h₁ : a = b) (h₂ : b = c) (h₃ : a = c)
      {Z : CommRingCat.{u}} (q : Y.presheaf.stalk c ⟶ Z),
      (Y.presheaf.stalkCongr (.of_eq h₁)).hom ≫
        (Y.presheaf.stalkCongr (.of_eq h₂)).hom ≫ q =
          (Y.presheaf.stalkCongr (.of_eq h₃)).hom ≫ q := by
    intro a b c h₁ h₂ h₃ Z q
    cases h₁
    cases h₂
    simp [TopCat.Presheaf.stalkCongr]
  have hmaps : cY0 ≫ iY.stalkMap y0 ≫ dY ≫ mf.stalkMap xf =
      f.stalkMap x ≫ cX ≫ iX.stalkMap xf := by
    calc
      cY0 ≫ iY.stalkMap y0 ≫ dY ≫ mf.stalkMap xf =
          cY0 ≫ cY1 ≫ iY.stalkMap yf ≫ mf.stalkMap xf := by
        simpa only [Category.assoc] using
          congrArg (fun z => cY0 ≫ z ≫ mf.stalkMap xf) HY
      _ = cY ≫ iY.stalkMap yf ≫ mf.stalkMap xf := by
        dsimp only [cY0, cY1, cY]
        rw [stalkCongr_hom_comp_assoc]
      _ = f.stalkMap x ≫ cX ≫ iX.stalkMap xf := by
        symm
        calc
          f.stalkMap x ≫ cX ≫ iX.stalkMap xf =
              (Y.presheaf.stalkCongr (.of_eq (congrArg f hX.symm))).hom ≫
                f.stalkMap (iX xf) ≫ iX.stalkMap xf := by
            simpa only [Category.assoc] using
              congrArg (fun z => z ≫ iX.stalkMap xf) HX
          _ = (Y.presheaf.stalkCongr (.of_eq (congrArg f hX.symm))).hom ≫
                cSq ≫ iY.stalkMap yf ≫ mf.stalkMap xf :=
            congrArg (fun q => (Y.presheaf.stalkCongr
              (.of_eq (congrArg f hX.symm))).hom ≫ q) HC.symm
          _ = cY ≫ iY.stalkMap yf ≫ mf.stalkMap xf :=
            hcollapse (congrArg f hX.symm) hpoint hy.symm
              (iY.stalkMap yf ≫ mf.stalkMap xf)
  have hTmk (c : T0 x) :
      targetQuotientEquiv f g x (Ideal.Quotient.mk (JT f g x) c) =
        (iX.stalkMap xf).hom (cX.hom c) :=
    ZInQ.Contrib.MulEtale.StacksVendor.AlgebraicGeometry.quotientStalkEquivFiberStalk_mk
      (f ≫ g) x c
  have hSmk (b : S0 f x) :
      sourceQuotientEquiv f g x (Ideal.Quotient.mk (JS f g x) b) =
        dY.hom ((iY.stalkMap y0).hom (cY0.hom b)) :=
    congrArg (fun c => dY.hom c)
      (ZInQ.Contrib.MulEtale.StacksVendor.AlgebraicGeometry.quotientStalkEquivFiberStalk_mk
        g (f x) b)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  calc
    targetQuotientEquiv f g x
        (quotientMap f g x (Ideal.Quotient.mk (JS f g x) b)) =
      targetQuotientEquiv f g x
        (Ideal.Quotient.mk (JT f g x) ((f.stalkMap x).hom b)) :=
      congrArg (targetQuotientEquiv f g x)
        (Ideal.quotientMap_mk (H := JS_le_comap_JT f g x) (x := b))
    _ = (iX.stalkMap xf).hom (cX.hom ((f.stalkMap x).hom b)) :=
      hTmk ((f.stalkMap x).hom b)
    _ = (mf.stalkMap xf).hom (dY.hom ((iY.stalkMap y0).hom (cY0.hom b))) :=
      (congrArg (fun h : Y.presheaf.stalk (f x) ⟶
        (p.fiber s).presheaf.stalk xf => h.hom b) hmaps).symm
    _ = (mf.stalkMap xf).hom
        (sourceQuotientEquiv f g x (Ideal.Quotient.mk (JS f g x) b)) :=
      congrArg (fun c => (mf.stalkMap xf).hom c) (hSmk b).symm

end H101DirectGlobalDetection.ActualQuotient
