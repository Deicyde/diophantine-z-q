import ZInQKernel.Contrib.OneProof.WeilFormulaTheta
import ZInQKernel.Contrib.OneProof.MulEtale

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite Limits

namespace WeilProof.Theta

open PicDict PkgI3 PkgI3.AbVar MonoidalCategory
open scoped CategoryTheory.MonObj

/-- Geometrically integral implies geometrically connected (copy of
`FrobPiecesNeron.geometricallyConnected_of_geometricallyIntegral`). -/
theorem geomConn_of_geomInt {X Y : Scheme.{0}} (g : X ⟶ Y) [GeometricallyIntegral g] :
    GeometricallyConnected g := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
  infer_instance

/-- **Divisibility of `X(k)`** for `n` invertible in `k` (proved: `[n]` is étale (the tree's
`mulEtaleAbelianScheme_proof`), hence open; proper, hence closed; `X` is connected; so `[n]` is surjective,
and the fibre over a `k`-point has a `k`-point). -/
theorem divisibleAC : DivisibleAC := by
  intro k _ _ X n hn hnk x
  have : GeometricallyConnected X.X.hom := geomConn_of_geomInt X.X.hom
  have : PkgI2.IsAbelianScheme (ObjBridge.toGrp X) := ⟨X.proper, X.smooth, inferInstance⟩
  have hE : Etale ((𝟙 (ObjBridge.toGrp X).X ^ n : (ObjBridge.toGrp X).X ⟶ (ObjBridge.toGrp X).X).left) :=
    ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof k (ObjBridge.toGrp X) n
      (by exact (IsUnit.mk0 _ hnk))
  have hE' : Etale (AC.mul X n).left := hE
  set f := (AC.mul X n).left with hfdef
  have hopen : IsOpenMap f := isOpenMap_of_generalizingMap f (Flat.generalizingMap f)
  have hw : f ≫ X.X.hom = X.X.hom := Over.w (AC.mul X n)
  have : IsProper (f ≫ X.X.hom) := by rw [hw]; infer_instance
  have : IsProper f := IsProper.of_comp f X.X.hom
  have hclosed : IsClosedMap f := f.isClosedMap
  have : IsIntegral X.X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.X.hom
  have hrange : Set.range f = Set.univ := by
    have hne : (Set.range f).Nonempty := by
      obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
      exact ⟨_, ⟨η[X.X].left p, rfl⟩⟩
    exact (IsClopen.eq_univ ⟨hclosed.isClosed_range, hopen.isOpen_range⟩ hne)
  have : Surjective f := ⟨fun y => by
    have : y ∈ Set.range f := by rw [hrange]; trivial
    exact this⟩
  let zl : Spec (CommRingCat.of k) ⟶ X.X.left := x.left
  let s : pullback f zl ⟶ Spec (CommRingCat.of k) := pullback.snd f zl
  have : IsProper s := by dsimp [s]; infer_instance
  have : Surjective s := by dsimp [s]; infer_instance
  have : CompactSpace ((pullback f zl : Scheme) : Type) := QuasiCompact.compactSpace_of_compactSpace s
  have : Nonempty ((pullback f zl : Scheme) : Type) := by
    obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
    exact ⟨(s.surjective p).choose⟩
  obtain ⟨x0, -, hx0⟩ := IsClosed.exists_closed_singleton (X := ((pullback f zl : Scheme) : Type))
    isClosed_univ Set.univ_nonempty
  let pt := pointOfClosedPoint s x0 hx0
  have hpt : pt ≫ s = 𝟙 _ := pointOfClosedPoint_comp s x0 hx0
  have hz : zl ≫ X.X.hom = 𝟙 _ := Over.w x
  let yy : AC.Kpt X := Over.homMk (pt ≫ pullback.fst f zl) (by
    change (pt ≫ pullback.fst f zl) ≫ X.X.hom = 𝟙 _
    rw [Category.assoc, ← hw, pullback.condition_assoc, hz, Category.comp_id]
    exact hpt)
  refine ⟨yy, ?_⟩
  have hyx : yy ≫ AC.mul X n = x := by
    apply Over.OverMorphism.ext
    change (pt ≫ pullback.fst f zl) ≫ f = zl
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (pt ≫ s) ≫ _ = _
    rw [hpt, Category.id_comp]
  rw [← hyx]
  simp only [AC.mul, MonObj.comp_pow, Category.comp_id]

end WeilProof.Theta
#print axioms WeilProof.Theta.divisibleAC
