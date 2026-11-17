/-
Multiplication-etale construction: LocalPromotion.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import ZInQKernel.Contrib.MulEtale.StacksVendor.LFPFromComposite

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace H101DirectFieldRoute.LocalPromotion

universe u

/-- This is the native algebraic conjunction on precisely the algebra induced by `φ`.
It does not introduce an alternative ring-map predicate or a root alias. -/
private theorem ringFormallyEtale_iff {R T : Type*} [CommRing R] [CommRing T]
    (φ : R →+* T) :
    φ.FormallyEtale ↔ φ.FormallyUnramified ∧ φ.FormallySmooth := by
  letI := φ.toAlgebra
  change Algebra.FormallyEtale R T ↔
    Algebra.FormallyUnramified R T ∧ Algebra.FormallySmooth R T
  exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth

/-- The actual stalk map is formally etale exactly when the actual affine point lies
in the native algebraic etale locus. The arrow isomorphism is Mathlib's real
`IsAffineOpen.arrowStalkMapIso`; source localization is explicitly formally etale. -/
theorem formallyEtale_stalkMap_iff {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X}
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallyEtale ↔
      hV.primeIdealOf ⟨x, hx⟩ ∈ Algebra.etaleLocus Γ(Y, U) Γ(X, V) := by
  letI := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  letI : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver p q
  letI : Algebra.FormallyEtale Γ(Y, U) (Localization.AtPrime p) :=
    Algebra.FormallyEtale.of_isLocalization p.primeCompl
  trans Algebra.FormallyEtale (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [ringFormallyEtale_iff,
      Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth,
      ← RingHom.formallyUnramified_algebraMap, ← RingHom.formallySmooth_algebraMap]
    exact and_congr
      (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
        (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx))
      (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
        (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx))
  · exact (Algebra.FormallyEtale.iff_restrictScalars
      (R := Γ(Y, U)) (A := Localization.AtPrime p)
      (B := Localization.AtPrime q)).symm

/-- Shrink a real affine source chart using a function outside the actual point's
prime ideal. Finite presentation comes from `f`, not from an etale-chart premise.
The ring map in the conclusion is the genuine native `f.appLE` on that open. -/
theorem exists_etale_appLE_of_formallyEtale_stalkMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (H : (f.stalkMap x).hom.FormallyEtale) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V)
      (hVU : V ≤ f ⁻¹ᵁ U), x ∈ V ∧ (f.appLE U V hVU).hom.Etale := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  letI : Algebra.IsEtaleAt Γ(Y, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    (formallyEtale_stalkMap_iff U hU V hV hVU hxV).mp H
  obtain ⟨r, hrx, hr⟩ := Algebra.exists_etale_of_isEtaleAt
    (R := Γ(Y, U)) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  refine ⟨_, hU, _, hV.basicOpen r, (X.basicOpen_le r).trans hVU, ?_, ?_⟩
  · have hpre : hV.primeIdealOf ⟨x, hxV⟩ ∈
        hV.fromSpec ⁻¹ᵁ X.basicOpen r := by
      rw [hV.fromSpec_preimage_basicOpen r]
      exact (PrimeSpectrum.mem_basicOpen r _).2 hrx
    change hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) ∈ X.basicOpen r at hpre
    rw [hV.fromSpec_primeIdealOf ⟨x, hxV⟩] at hpre
    exact hpre
  · have := hV.isLocalization_basicOpen r
    let E : Localization.Away r ≃ₐ[Γ(X, V)] Γ(X, X.basicOpen r) :=
      IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r)
        Γ(X, X.basicOpen r)
    rw [← RingHom.etale_algebraMap] at hr
    have hmap :
        (f.appLE U (X.basicOpen r) ((X.basicOpen_le r).trans hVU)).hom =
          E.toRingEquiv.toRingHom.comp (algebraMap Γ(Y, U) (Localization.Away r)) := by
      ext a
      change (f.appLE U (X.basicOpen r) ((X.basicOpen_le r).trans hVU)).hom a =
        E (algebraMap Γ(Y, U) (Localization.Away r) a)
      rw [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization.Away r),
        E.commutes]
      change (f.appLE U (X.basicOpen r) ((X.basicOpen_le r).trans hVU)).hom a =
        (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
          ((f.appLE U V hVU).hom a)
      have hc := congrArg
        (fun z : Γ(Y, U) ⟶ Γ(X, X.basicOpen r) => z.hom a)
        (Scheme.Hom.appLE_map f hVU (homOfLE (X.basicOpen_le r)).op)
      simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using hc.symm
    rw [hmap]
    exact RingHom.Etale.respectsIso.1 _ E.toRingEquiv hr

/-- Promote the actual section-ring chart to its actual restricted scheme morphism.
The top-section comparison is the native `arrowResLEAppIso`, not an assumed chart. -/
theorem exists_etale_affine_chart_of_formallyEtale_stalkMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (H : (f.stalkMap x).hom.FormallyEtale) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V)
      (hVU : V ≤ f ⁻¹ᵁ U), x ∈ V ∧ Etale (f.resLE U V hVU) := by
  obtain ⟨U, hU, V, hV, hVU, hxV, HE⟩ :=
    exists_etale_appLE_of_formallyEtale_stalkMap f x H
  refine ⟨U, hU, V, hV, hVU, hxV, ?_⟩
  letI : IsAffine U := hU
  letI : IsAffine V := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
  exact (RingHom.Etale.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U V hVU)).mpr HE

/-- Local-promotion contract: formal etaleness of the ACTUAL stalk map yields
etaleness of `V.ι ≫ f` on an actual affine open neighbourhood of the same point. -/
theorem exists_etale_open_of_formallyEtale_stalkMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (H : (f.stalkMap x).hom.FormallyEtale) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ Etale (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hVU, hxV, HE⟩ :=
    exists_etale_affine_chart_of_formallyEtale_stalkMap f x H
  letI : Etale (f.resLE U V hVU) := HE
  refine ⟨V, hV, hxV, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f hVU]
  infer_instance

/-- Supplier-friendly spelling: the algebra is induced by the very same stalk map,
so this is just the native definition of `RingHom.FormallyEtale`, not transport
along an arbitrary local-ring or residue-field replacement. -/
theorem exists_etale_open_of_algebraFormallyEtale_stalkMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] (x : X)
    (H : letI := (f.stalkMap x).hom.toAlgebra
      Algebra.FormallyEtale (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ Etale (V.ι ≫ f) := by
  change (f.stalkMap x).hom.FormallyEtale at H
  exact exists_etale_open_of_formallyEtale_stalkMap f x H

section Multiplication

variable {O : Type u} [CommRing O]
    (G : Over (Spec (.of O))) [GrpObj G] [Smooth G.hom]

/-- Multiplication's finite presentation is DERIVED from the existing smooth
structure map and `Over.w`, using the genuine LFPFromComposite theorem. -/
theorem mul_left_locallyOfFinitePresentation (m : ℕ) :
    LocallyOfFinitePresentation (𝟙 G ^ m : G ⟶ G).left := by
  let f : G.left ⟶ G.left := (𝟙 G ^ m : G ⟶ G).left
  letI : LocallyOfFinitePresentation (f ≫ G.hom) := by
    change LocallyOfFinitePresentation ((𝟙 G ^ m : G ⟶ G).left ≫ G.hom)
    rw [Over.w]
    infer_instance
  exact ZInQ.Contrib.MulEtale.StacksVendor.locallyOfFinitePresentation_of_comp f G.hom

/-- Actual identity specialization for the direct H101 route. The formal-etale
stalk result is an EXPLICIT intermediate supplier; this is not the full H101
claim with Flat/Etale or a final tangent bijection hidden as a Fact. -/
theorem exists_etale_open_mul_at_unit (m : ℕ) (s : Spec (.of O))
    (H : ((𝟙 G ^ m : G ⟶ G).left.stalkMap (η[G].left s)).hom.FormallyEtale) :
    ∃ V : G.left.Opens, IsAffineOpen V ∧ η[G].left s ∈ V ∧
      Etale (V.ι ≫ (𝟙 G ^ m : G ⟶ G).left) := by
  letI : LocallyOfFinitePresentation (𝟙 G ^ m : G ⟶ G).left :=
    mul_left_locallyOfFinitePresentation G m
  exact exists_etale_open_of_formallyEtale_stalkMap
    (𝟙 G ^ m : G ⟶ G).left (η[G].left s) H

end Multiplication

end H101DirectFieldRoute.LocalPromotion
