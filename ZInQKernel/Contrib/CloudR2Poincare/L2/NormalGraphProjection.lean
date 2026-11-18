import ZInQKernel.Contrib.CloudR2Poincare.L2.RegularNormalAffines

/-!
# Proven native normal graph projection criterion

The original proper projection is finite and surjective by its all-Ω point
bijections. Its original underlying map is a homeomorphism, so reduced G is
integral. Native universal injectivity makes its residue extensions purely
inseparable; characteristic zero makes them separable and hence trivial.
Thus its actual generic stalk map is an iso. The genuinely smooth target J
has all-dimensional normal affine rings by the published W07 regular-scheme
UFD proof and Mathlib local integral closure. Finite integrality and the
actual generic field then make every affine section map an iso, and actual
Zariski-locality makes p itself an iso.

No graph-lift surjectivity, normality, field-degree, birationality, UFD,
isomorphism, or desired conclusion is assumed as a Fact. The original named
Prop remains unchanged; this file supplies its proof.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Fully proved projection isomorphism over the ORIGINAL arbitrary char-zero
field. All original geometric field-test types are quantified literally. -/
theorem normalGraphProjection_isIso
    {k : Type u} [Field k] [CharZero k] (J : PkgI3.AbVar k)
    (G : Over (Spec (.of k))) [AlgebraicGeometry.IsReduced G.left]
    (p : G ⟶ J.X) [IsProper p.left]
    (hp : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra k Ω],
      Function.Bijective (fun a : L1.fieldTest k Ω ⟶ G => a ≫ p)) : IsIso p := by
  have hinj : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra k Ω],
      Function.Injective (fun a : L1.fieldTest k Ω ⟶ G => a ≫ p) := by
    intro Ω _ _ _ _ a b h
    exact (hp Ω).1 h
  letI : IsFinite p.left := isFinite_of_geometricFieldPoint_injective p hinj
  letI : IsIntegral G.left := isIntegral_source_of_geometricFieldPoint_bijective J G p hp
  letI : IsIntegral J.X.left := GeometricallyIntegral.isIntegral_of_subsingleton J.X.hom
  have hgen := genericPoint_map_of_geometricFieldPoint_bijective J G p hp
  letI : IsIso (p.left.stalkMap (genericPoint G.left)) :=
    isIso_genericStalkMap_of_geometricFieldPoint_bijective J G p hp
  letI : IsIso p.left := by
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
      J.X.left.affineCover).mpr fun i => ?_
    let U : J.X.left.affineOpens :=
      ⟨(J.X.left.affineCover.f i).opensRange, isAffineOpen_opensRange (J.X.left.affineCover.f i)⟩
    letI : Nonempty U.1 := by
      let V := (J.X.left.local_affine i).choose
      let e := Classical.choice (J.X.left.local_affine i).choose_spec.choose_spec
      let z := e.hom.base ⟨i, V.2⟩
      exact ⟨⟨(J.X.left.affineCover.f i).base z, Set.mem_range_self _⟩⟩
    letI : IsIntegrallyClosed Γ(J.X.left, U.1) := isIntegrallyClosed_affineOpen_abVar J U
    have hU : IsIso (p.left.app U.1) := isIso_app_of_integral_genericStalk_iso_normal p.left hgen U
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (morphismRestrictOpensRange p.left (J.X.left.affineCover.f i))).mp
      ((isIso_morphismRestrict_iff_isIso_app p.left U.2).2 hU)
  letI : IsIso ((Over.forget (Spec (.of k))).map p) := by
    change IsIso p.left
    infer_instance
  exact isIso_of_reflects_iso p (Over.forget (Spec (.of k)))

/-- The unchanged internal geometric Prop now has an actual closed proof.
No new premise replaces the discharged graph criterion. -/
theorem nativeNormalGraphProjectionCriterion_proof : NativeNormalGraphProjectionCriterion := by
  intro k _ _ J G _ p _ hp
  exact normalGraphProjection_isIso J G p hp

end ZInQ.Contrib.CloudR2Poincare.L2
