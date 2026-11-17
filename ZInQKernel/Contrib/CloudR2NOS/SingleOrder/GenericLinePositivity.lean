/-
# H5 / NOS round 2, lane 1: generic FIELD positivity of an actual projective twist

Newly authored glue (H5 round-2 lane 1, 2026-11-15). Every geometric input is an existing PUBLISHED
theorem of the vendored W07 contribution `ZInQKernel.Contrib.CloudW07JacobiansCurves` (frenzymath/
Jacobian-Challenge @ c4254cce15b3e284a0a3ae1d73936f2ee195d272, Apache-2.0, Copyright 2026 Axel Delaval,
Jie Xu and Shitan Xu; see that directory's LICENSE/NOTICE) or of Mathlib; no W07 file is copied or edited.

For an actual proper `k`-scheme `X` with a closed immersion `ι : X ⟶ ℙ(coords; Spec k)` (W07's relative
projective space, finitely many coordinates) and the pulled-back twists
`L_d := ProjectiveSpace.twistRestrict ι d = ι^* 𝒪(d)`:
* `exists_subsingleton_H_twistRestrict`: W07 Serre vanishing
  (`Scheme.Modules.exists_subsingleton_H_tensor_pullback_twist_of_isFinite`), transported along W07's
  ACTUAL coordinate comparison `ProjectiveSpace.affineIso` / `pullbackAffineIsoTwistIso` to
  `Proj.projectiveSpaceOverAffine coords k`: `H^q(X, L_d) = 0` for all `q > 0` and all `d ≥ N`;
* `nontrivial_H_zero_twistRestrict`: the pulled-back coordinate power `T_i^d`
  (`ProjectiveSpace.pullbackTwistPowSection`) is a NONZERO global section when `X` is nonempty
  (it trivializes `L_d` on the nonempty `ι⁻¹ D₊(T_i)`), via W07 `H.unitHomAddEquiv`;
* `finite_H_twistRestrict`: W07 `hasFiniteH_of_isProper`;
* `hFiber_twistRestrict`: for `d ≥ N`, W07 native fibre cohomology (`Scheme.Modules.hFiber`,
  `eulerCharFiber`, identified over the field by W07 `hFiber_eq_finrankH`) satisfies
  `h^q = 0 (q > 0)`, `0 < h^0` and `χ = h^0`.
At the ORIGINAL abelian variety `A` (any field `K`, any universe): W07
`GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral` gives a projective
immersion of `A.X.left` over `A.X.hom`, made a closed immersion by properness (Mathlib
`IsClosedImmersion.of_isPreimmersion`); `exists_positive_twist` returns the actual twist `L = ι^* 𝒪(d)`,
`0 < d`, with its embedding/degree anchor and the positivity; `exists_line_hFiber_pos_eulerCharFiber_ne_zero`
is C6's consumer shape (W07 sheaf `IsInvertible`; C6's `AmpleCoefficientBridge.source_isInvertible_iff_sheaf`
converts to the source-native predicate). No ampleness, χ or `H^0` positivity is assumed anywhere.
-/
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.SerreVanishing
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.FiberField
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Proper
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Sections
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.AffineTwist
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Twist
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Group.QuasiProjective
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Invertible

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.SingleOrder.GenericLinePositivity

section General

variable {K : Type u} [Field K] {X : Scheme.{u}} {coords : Type u} [Finite coords]
  (ι : X ⟶ ℙ(coords; Spec (CommRingCat.of K))) [IsClosedImmersion ι]

/-- The map to W07's polynomial projective space through the ACTUAL comparison isomorphism. -/
abbrev toPolynomialProj : X ⟶ Proj.projectiveSpaceOverAffine coords (CommRingCat.of K) :=
  ι ≫ (ProjectiveSpace.affineIso coords (CommRingCat.of K)).hom

instance isFinite_toPolynomialProj : IsFinite (toPolynomialProj ι) := by
  unfold toPolynomialProj
  infer_instance

/-- `ι^* 𝒪(d)` is the module of W07's Serre-vanishing theorem (unit tensor the pullback of the
polynomial twist along `toPolynomialProj ι`), by the actual comparison isomorphisms. -/
def twistRestrictIso (d : ℤ) :
    ProjectiveSpace.twistRestrict ι d ≅
      unit X ⊗ (Scheme.Modules.pullback (toPolynomialProj ι)).obj
        (Proj.twist (MvPolynomial.homogeneousSubmodule coords (CommRingCat.of K)) d) :=
  (Scheme.Modules.pullback ι).mapIso (ProjectiveSpace.pullbackAffineIsoTwistIso coords (CommRingCat.of K) d).symm ≪≫
    (pullbackComp ι (ProjectiveSpace.affineIso coords (CommRingCat.of K)).hom).app _ ≪≫
    (λ_ _).symm

/-- **Serre vanishing for the pulled-back twists** (W07). -/
theorem exists_subsingleton_H_twistRestrict :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ q : ℕ, 0 < q →
      Subsingleton ((ProjectiveSpace.twistRestrict ι (d : ℤ)).H q) := by
  obtain ⟨bound, vanishing⟩ :=
    exists_subsingleton_H_tensor_pullback_twist_of_isFinite coords (CommRingCat.of K)
      (toPolynomialProj ι) (unit X)
  refine ⟨bound.toNat, fun d hd q hq => ?_⟩
  haveI := vanishing (d : ℤ) (by omega) q hq
  exact (H.mapLinearEquiv (twistRestrictIso ι (d : ℤ)) q).toEquiv.subsingleton

omit [Finite coords] [IsClosedImmersion ι] in
/-- **A nonzero global section**: some pulled-back coordinate power `T_i^d` is nonzero. -/
theorem nontrivial_H_zero_twistRestrict [Nonempty X] (d : ℕ) :
    Nontrivial ((ProjectiveSpace.twistRestrict ι (d : ℤ)).H 0) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hx : ι x ∈ (⨆ i, ProjectiveSpace.standardOpen coords (Spec (CommRingCat.of K)) i) := by
    rw [ProjectiveSpace.iSup_standardOpen]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let U : X.Opens := ι ⁻¹ᵁ ProjectiveSpace.standardOpen coords (Spec (CommRingCat.of K)) i
  have hxU : x ∈ U := hi
  let s := ProjectiveSpace.pullbackTwistPowSection ι i d
  have hs : s ≠ 0 := by
    intro h0
    have hiso : IsIso ((restrictFunctor U.ι).map s) :=
      ProjectiveSpace.isIso_restrict_pullbackTwistPowSection ι i d
    rw [h0, Functor.map_zero] at hiso
    have hzero : IsZero ((restrictFunctor U.ι).obj (unit X)) :=
      IsZero.of_mono_zero _ ((restrictFunctor U.ι).obj (ProjectiveSpace.twistRestrict ι (d : ℤ)))
    -- W07: cohomology of a zero sheaf vanishes; `H^0 = Γ(-, ⊤)`; and `Γ` of the restricted
    -- structure sheaf is the ring `Γ(X, U.ι ''ᵁ ⊤)` (`restrictAppIso` is the identity).
    have hsub : Subsingleton Γ((restrictFunctor U.ι).obj (unit X), ⊤) := by
      haveI := subsingleton_H_of_isZero hzero 0
      exact (H.zeroLinearEquiv ((restrictFunctor U.ι).obj (unit X))).toEquiv.symm.subsingleton
    haveI : Nonempty ↥(U.ι ''ᵁ ⊤) := ⟨⟨U.ι ⟨x, hxU⟩, ⟨⟨x, hxU⟩, trivial, rfl⟩⟩⟩
    exact (not_subsingleton Γ(X, U.ι ''ᵁ ⊤)) hsub
  refine ⟨⟨H.unitHomAddEquiv _ s, 0, fun h => hs ?_⟩⟩
  exact (H.unitHomAddEquiv _).injective (h.trans (map_zero _).symm)

omit [Finite coords] [IsClosedImmersion ι] in
/-- **Finiteness** of the cohomology over the field (W07 `hasFiniteH_of_isProper`, proper coherent),
for the `K`-structure given by the structure morphism `f` (W07 `moduleHOfField`). -/
theorem finite_H_twistRestrict (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    [hX : X.Over (Spec (CommRingCat.of K))] (hf : X ↘ Spec (CommRingCat.of K) = f) (d : ℤ) (q : ℕ) :
    Module.Finite K ((ProjectiveSpace.twistRestrict ι d).H q) := by
  obtain ⟨g⟩ := hX
  change g = f at hf
  subst hf
  exact hasFiniteH_of_isProper g (ProjectiveSpace.twistRestrict ι d) q

/-- **Positivity in W07 native fibre cohomology**, for all sufficiently large twists. -/
theorem hFiber_twistRestrict (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [Nonempty X] :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ s : Spec (CommRingCat.of K),
      (∀ q : ℕ, 0 < q → (ProjectiveSpace.twistRestrict ι (d : ℤ)).hFiber f q s = 0) ∧
      0 < (ProjectiveSpace.twistRestrict ι (d : ℤ)).hFiber f 0 s ∧
      (ProjectiveSpace.twistRestrict ι (d : ℤ)).eulerCharFiber f s =
        ((ProjectiveSpace.twistRestrict ι (d : ℤ)).hFiber f 0 s : ℤ) := by
  obtain ⟨N, hN⟩ := exists_subsingleton_H_twistRestrict ι
  refine ⟨N, fun d hd s => ?_⟩
  letI : X.Over (Spec (CommRingCat.of K)) := ⟨f⟩
  have hvan : ∀ q : ℕ, 0 < q → (ProjectiveSpace.twistRestrict ι (d : ℤ)).hFiber f q s = 0 := by
    intro q hq
    rw [hFiber_eq_finrankH f _ q s]
    haveI := hN d hd q hq
    exact Module.finrank_zero_of_subsingleton
  have hpos : 0 < (ProjectiveSpace.twistRestrict ι (d : ℤ)).hFiber f 0 s := by
    rw [hFiber_eq_finrankH f _ 0 s]
    haveI := finite_H_twistRestrict ι f rfl (d : ℤ) 0
    haveI := nontrivial_H_zero_twistRestrict ι d
    exact Module.finrank_pos
  refine ⟨hvan, hpos, ?_⟩
  rw [eulerCharFiber, finsum_eq_single _ 0]
  · simp
  · intro q hq
    rw [hvan q (Nat.pos_of_ne_zero hq)]
    simp

end General

section Original

variable {K : Type u} [Field K] (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]

omit [PkgI2.IsAbelianVariety A] in
open scoped CategoryTheory.MonObj in
/-- `A.X.left` is nonempty: it contains the image of the `K`-rational identity point
(`1 : PkgI2.Pts A K`, the unit of the group object), checked Objects-only in probe run
`h5-lane1-probe-nonempty-001` (rc 0, AX3). -/
theorem nonempty_left : Nonempty A.X.left :=
  ⟨(1 : PkgI2.Pts A K).left (IsLocalRing.closedPoint K)⟩

/-- The ORIGINAL abelian variety has a closed immersion into W07's finite-coordinate projective
space over its own field, compatible with its own structure morphism. -/
theorem exists_closedImmersion_projectiveSpace :
    ∃ (coords : Type u) (_ : Finite coords) (ι : A.X.left ⟶ ℙ(coords; Spec (CommRingCat.of K))),
      IsClosedImmersion ι ∧
        ι ≫ ℙ(coords; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) = A.X.hom := by
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : Smooth A.X.hom := PkgI2.IsAbelianVariety.smooth
  haveI : GeometricallyIntegral A.X.hom := PkgI2.IsAbelianVariety.geomIntegral
  obtain ⟨coords, finite, ι, immersion, over⟩ :=
    GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral A.X
  letI := finite
  letI := immersion
  haveI : IsProper (ι ≫ ℙ(coords; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
    rw [over]
    infer_instance
  haveI : IsProper ι := IsProper.of_comp ι (ℙ(coords; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))
  exact ⟨coords, finite, ι, IsClosedImmersion.of_isPreimmersion ι ι.isClosedMap.isClosed_range, over⟩

/-- **Field positivity on the ORIGINAL abelian variety**, with the actual twist anchor. -/
theorem exists_positive_twist :
    ∃ (coords : Type u) (_ : Finite coords) (ι : A.X.left ⟶ ℙ(coords; Spec (CommRingCat.of K)))
      (d : ℕ), IsClosedImmersion ι ∧
        ι ≫ ℙ(coords; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) = A.X.hom ∧ 0 < d ∧
        (ProjectiveSpace.twistRestrict ι (d : ℤ)).IsInvertible ∧
        (∀ q : ℕ, 0 < q →
          (ProjectiveSpace.twistRestrict ι (d : ℤ)).hFiber A.X.hom q (IsLocalRing.closedPoint K) = 0) ∧
        0 < (ProjectiveSpace.twistRestrict ι (d : ℤ)).hFiber A.X.hom 0 (IsLocalRing.closedPoint K) ∧
        (ProjectiveSpace.twistRestrict ι (d : ℤ)).eulerCharFiber A.X.hom (IsLocalRing.closedPoint K) =
          ((ProjectiveSpace.twistRestrict ι (d : ℤ)).hFiber A.X.hom 0 (IsLocalRing.closedPoint K) : ℤ) := by
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  obtain ⟨coords, finite, ι, hι, over⟩ := exists_closedImmersion_projectiveSpace A
  letI := finite
  haveI := hι
  haveI : Nonempty A.X.left := nonempty_left A
  obtain ⟨N, hN⟩ := hFiber_twistRestrict ι A.X.hom
  obtain ⟨h1, h2, h3⟩ := hN (max N 1) (le_max_left _ _) (IsLocalRing.closedPoint K)
  exact ⟨coords, finite, ι, max N 1, hι, over, by omega, inferInstance, h1, h2, h3⟩

/-- **C6's consumer shape**: an actual invertible module on the original `A.X.left` with positive
`H^0` and nonzero Euler characteristic of its unique fibre. -/
theorem exists_line_hFiber_pos_eulerCharFiber_ne_zero :
    ∃ L : A.X.left.Modules, L.IsInvertible ∧
      0 < L.hFiber A.X.hom 0 (IsLocalRing.closedPoint K) ∧
      L.eulerCharFiber A.X.hom (IsLocalRing.closedPoint K) ≠ 0 := by
  obtain ⟨coords, finite, ι, d, -, -, -, hinv, -, hpos, heq⟩ := exists_positive_twist A
  refine ⟨_, hinv, hpos, ?_⟩
  rw [heq]
  exact_mod_cast hpos.ne'

end Original

end ZInQ.Contrib.CloudR2NOS.SingleOrder.GenericLinePositivity
