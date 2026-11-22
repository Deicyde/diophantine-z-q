import ZInQKernel.Contrib.OneProof.NeronDVR.SectionCover
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Hilbert.SectionPencil.Divisor
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.HomSection

/-!
# Effective descent from spanning compatible sections

At a point, sections vanishing there form a submodule, so a spanning
family has a section nonvanishing whenever any section is nonvanishing.
Compatibility across the overlap makes its nonvanishing locus invariant.
-/

open CategoryTheory Opposite AlgebraicGeometry
open scoped MonoidalCategory

universe u v

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {L : X.Modules} [L.IsInvertible]

set_option backward.isDefEq.respectTransparency false in
/-- A spanning family of global sections has a nonvanishing member at every
point where some global section is nonvanishing. -/
theorem exists_nonvanishing_of_span {R : Type v} [CommRing R]
    (r : R →+* Γ(X, ⊤)) (P : Γ(L, ⊤) → Prop)
    (hspan : letI := Module.compHom Γ(L, ⊤) r
      ∀ s, s ∈ Submodule.span R {s | P s})
    {x : X} (hx : ∃ s : 𝟙_ X.Modules ⟶ L, x ∈ s.zeroLocus.support.compl) :
    ∃ s : Γ(L, ⊤), P s ∧ x ∈ (homOfGlobalSection L s).zeroLocus.support.compl := by
  classical
  let := Module.compHom Γ(L, ⊤) r
  obtain ⟨V, hxV, _, e, he⟩ := exists_isFreeGenerator L (W := ⊤) (x := x) (by trivial)
  let j : V.1 ⟶ ⊤ := homOfLE le_top
  let coeff (s : Γ(L, ⊤)) :=
    X.presheaf.germ V.1 x hxV (he.coeff (L.presheaf.map j.op s))
  let m := IsLocalRing.maximalIdeal (X.presheaf.stalk x)
  have hnonzero (s : Γ(L, ⊤)) :
      x ∈ (homOfGlobalSection L s).zeroLocus.support.compl ↔ coeff s ∉ m := by
    have heq : X.basicOpen (he.coeff (L.presheaf.map j.op s)) =
        V.1 ⊓ (homOfGlobalSection L s).zeroLocus.support.compl := by
      rw [← homOfGlobalSection_app_one]
      exact basicOpen_coeff_eq (homOfGlobalSection L s) V he
    rw [show coeff s ∉ m ↔ IsUnit (coeff s) by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]]
    rw [← X.mem_basicOpen _ x hxV, heq]
    exact ⟨fun h => ⟨hxV, h⟩, fun h => h.2⟩
  let vanishing : Submodule R Γ(L, ⊤) :=
    { carrier := {s | coeff s ∈ m}
      zero_mem' := by simp [coeff]
      add_mem' := by
        intro a b ha hb
        change coeff (a + b) ∈ m
        exact (by simpa [coeff] using Ideal.add_mem m ha hb)
      smul_mem' := by
        intro c a ha
        change coeff ((r c) • a) ∈ m
        change X.presheaf.germ V.1 x hxV
          (he.coeff (L.presheaf.map j.op (r c • a))) ∈ m
        rw [Scheme.Modules.map_smul, he.coeff_smul_left, map_mul]
        exact Ideal.mul_mem_left m _ ha }
  by_contra! hn
  have hall : Submodule.span R {s | P s} ≤ vanishing := Submodule.span_le.mpr fun s hs =>
    show coeff s ∈ m from not_not.mp (fun hs' => hn s hs ((hnonzero s).2 hs'))
  obtain ⟨s, hs⟩ := hx
  let t := unitHomAddEquiv L s
  have ht : homOfGlobalSection L t = s := (unitHomAddEquiv L).left_inv s
  have ht' : coeff t ∉ m := (hnonzero t).mp (ht ▸ hs)
  exact ht' (hall (hspan t))

end AlgebraicGeometry.Scheme.Modules

namespace CategoryTheory.Over.DescentDatum

open Limits Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- A section respected by the overlap isomorphism has an invariant
nonvanishing locus. -/
theorem isInvariant_nonvanishing_of_pullbackSection
    {S S' : Scheme.{u}} {p : S' ⟶ S} {X : Over S'} (d : DescentDatum p X)
    {L : X.left.Modules} [L.IsInvertible]
    (ψ : (Scheme.Modules.pullback (pullback.fst (X.hom ≫ p) p)).obj L ≅
      (Scheme.Modules.pullback d.toHom).obj L)
    (s : Γ(L, ⊤))
    (hs : ψ.hom.app ⊤ (Scheme.Modules.pullbackSection (pullback.fst (X.hom ≫ p) p) (U := ⊤) s) =
      Scheme.Modules.pullbackSection d.toHom (U := ⊤) s) :
    d.IsInvariant (homOfGlobalSection L s).zeroLocus.support.compl := by
  let Y := Limits.pullback (X.hom ≫ p) p
  let a : Y ⟶ X.left := pullback.fst _ _
  let b : Y ⟶ X.left := d.toHom
  let t := homOfGlobalSection L s
  let ta := AlgebraicGeometry.SectionPencil.pullbackSectionHom a t
  let tb := AlgebraicGeometry.SectionPencil.pullbackSectionHom b t
  have happ (g : Y ⟶ X.left) :
      (AlgebraicGeometry.SectionPencil.pullbackSectionHom g t).app ⊤ (1 : Γ(Y, ⊤)) =
        Scheme.Modules.pullbackSection g (U := ⊤) s := by
    change (((pullbackObjUnitIso g).inv ≫ (Scheme.Modules.pullback g).map t).app (g ⁻¹ᵁ ⊤))
      (1 : Γ(Y, ⊤)) = _
    rw [← pullbackSection_app_one]
    exact congrArg (Scheme.Modules.pullbackSection g (U := ⊤)) ((unitHomAddEquiv L).right_inv s)
  have hcomp : ta ≫ ψ.hom = tb := by
    apply (unitHomAddEquiv ((Scheme.Modules.pullback b).obj L)).injective
    change (ta ≫ ψ.hom).app ⊤ (1 : Γ(Y, ⊤)) = tb.app ⊤ (1 : Γ(Y, ⊤))
    rw [Hom.comp_app, ConcreteCategory.comp_apply, happ a, happ b]
    exact hs
  let e : Arrow.mk ta ≅ Arrow.mk tb :=
    Arrow.isoMk' ta tb (Iso.refl _) ψ (by simpa using hcomp.symm)
  have heq : t.zeroLocus.comap a = t.zeroLocus.comap b := by
    rw [← AlgebraicGeometry.SectionPencil.pullbackSectionHom_zeroLocus a,
      ← AlgebraicGeometry.SectionPencil.pullbackSectionHom_zeroLocus b]
    exact Hom.zeroLocus_eq_of_arrowIso ta tb e
  have hSupport := congrArg (fun J : Y.IdealSheafData => (J.support : Set Y)) heq
  rw [Scheme.IdealSheafData.coe_support_comap, Scheme.IdealSheafData.coe_support_comap] at hSupport
  apply (d.isInvariant_iff _).mpr
  intro x hx
  change x ∉ b ⁻¹' (t.zeroLocus.support : Set X.left)
  rw [← hSupport]
  exact hx

/-- Effective descent follows when an invertible module has an affine
nonvanishing cover and its compatible sections span all global sections. -/
theorem isEffective_of_span_compatible_sections
    {S S' : Scheme.{u}} [IsAffine S] [IsAffine S'] {p : S' ⟶ S}
    [Flat p] [Surjective p] [QuasiCompact p] {X : Over S'} [CompactSpace X.left]
    (d : DescentDatum p X) {L : X.left.Modules} [L.IsInvertible]
    (ψ : (Scheme.Modules.pullback (pullback.fst (X.hom ≫ p) p)).obj L ≅
      (Scheme.Modules.pullback d.toHom).obj L)
    {R : Type v} [CommRing R] (r : R →+* Γ(X.left, ⊤))
    (hspan : letI := Module.compHom Γ(L, ⊤) r
      ∀ s, s ∈ Submodule.span R {s |
        ψ.hom.app ⊤ (Scheme.Modules.pullbackSection (pullback.fst (X.hom ≫ p) p) (U := ⊤) s) =
          Scheme.Modules.pullbackSection d.toHom (U := ⊤) s})
    (hAffine : ∀ x : X.left, ∃ s : 𝟙_ X.left.Modules ⟶ L,
      x ∈ s.zeroLocus.support.compl ∧ IsAffineOpen s.zeroLocus.support.compl) :
    d.IsEffective := by
  apply d.isEffective_of_nonvanishing_cover hAffine
  intro x
  obtain ⟨s, hs, hx⟩ := Scheme.Modules.exists_nonvanishing_of_span r _ hspan
    (let ⟨t, ht, _⟩ := hAffine x; ⟨t, ht⟩)
  exact ⟨homOfGlobalSection L s, hx, d.isInvariant_nonvanishing_of_pullbackSection ψ s hs⟩

end CategoryTheory.Over.DescentDatum
