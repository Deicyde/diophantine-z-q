/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 scheme-only effective descent, route Q. This follows the Parent-approved plan
SCHEME_DESCENT_NATIVE_PLAN_001, sha 7a0aede9.

Sub-statements in this file:
* Q1: the standing consequences of a closed-immersion presentation;
* Q6: finitely many descended sections span the sections of the given presentation;
* Q7: the presentation by those sections;
* Q8: that presentation is a closed immersion.

NATIVE assembly. SOURCE ONLY, UNCOMPILED. Universe u. The only option is autoImplicit false.

Suppliers:
* lane4 G1a `PresentationTwist.nonempty_iso_pullback_twist`;
* lane4 G5 `ProjOfFrames.presentationOfFramesNear`;
* `PresentationBasics` (resTop/res helpers, PresChart);
* route-Q (a′) edition `ProjPresentation.isClosedImmersion_toProj_of_forall_exists_eq_sum_smul`;
* W07 `Scheme.Modules.isInvertible_iff_forall_exists_pullback_unit`,
  `SheafOfModules.IsInvertible.exists_isoUnit`, and the instances
  `Proj.isInvertible_twist_homogeneousSubmodule` and `isInvertible_pullback`;
* Mathlib `Submodule.mem_span_finite_of_mem_span` and
  `Submodule.mem_span_range_iff_exists_fun`.
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.ProjOfFrames
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.PresentationTwist
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_forall_exists_eq_sum_smul
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Invertible
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.Polynomial

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.Descent

local notation "Pres" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation
local notation "CIBS" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections
local notation "FramesNear" => ZInQ.Contrib.CloudR2NOS.ClosedSection.FramesNear

/-- The `S'`-module structure on the global sections of a module over `X' → Spec S'`: a scalar
`s : S'` acts as the global function `f'^♯ s`. -/
abbrev moduleTop {S' : Type u} [CommRing S'] {X' : Scheme.{u}} (f' : X' ⟶ Spec (CommRingCat.of S'))
    (L' : X'.Modules) : Module S' Γ(L', ⊤) :=
  Module.compHom Γ(L', ⊤) ((f'.appLE ⊤ ⊤ le_top).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of S')).inv.hom)

/-- Invertibility transports along isomorphisms. -/
theorem isInvertible_of_iso {X : Scheme.{u}} {M M' : X.Modules} (e : M ≅ M') [hM : M.IsInvertible] :
    M'.IsInvertible := by
  rw [Scheme.Modules.isInvertible_iff_forall_exists_pullback_unit]
  intro x
  obtain ⟨U, hxU, ⟨t⟩⟩ := hM.exists_isoUnit x
  exact ⟨U, hxU, ⟨((Scheme.Modules.pullback U.ι).mapIso e).symm ≪≫ t⟩⟩

/-- **Q1.** A closed-immersion presentation makes the structure map proper and the presented
module (natively) invertible.

Truth check: `f' = 𝔓.toProj ≫ π` is a closed immersion followed by a proper map. By G1a,
`L' ≅ 𝔓.toProj^*𝒪(1)`, and `𝒪(1)` is invertible (W07). -/
theorem isProper_and_isInvertible_of_closedImmersionBySections {S' : Type u} [CommRing S']
    {X' : Scheme.{u}} (f' : X' ⟶ Spec (CommRingCat.of S')) (L' : X'.Modules) (hva : CIBS L' f') :
    IsProper f' ∧ L'.IsInvertible := by
  obtain ⟨N, 𝔓, h𝔓⟩ := hva
  haveI : IsClosedImmersion 𝔓.toProj := h𝔓
  refine ⟨?_, ?_⟩
  · rw [← 𝔓.toProj_π]; infer_instance
  · obtain ⟨e⟩ :=
      ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationTwist.nonempty_iso_pullback_twist S' N 𝔓
    exact isInvertible_of_iso e.symm

open ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationBasics in
/-- If a sum `∑ aⱼ • tⱼ` frames near `x`, then some summand `tⱼ` frames near `x`. This restates,
with explicit binders, the lane4 proof of `Step2B3.FramesNearOfSum` (B3Small). -/
theorem framesNear_of_sum {X : Scheme.{u}} (M : X.Modules) {m : ℕ} (a : Fin m → Γ(X, ⊤))
    (t : Fin m → Γ(M, ⊤)) (x : X) (hfr : FramesNear M (∑ j, a j • t j) x) :
    ∃ j, FramesNear M (t j) x := by
  obtain ⟨U, hxU, hU⟩ := hfr
  have hbijU := hU U le_rfl
  choose c hc0 using fun j => hbijU.2 (resTop M U (t j))
  have hc : ∀ j, c j • resTop M U (∑ j, a j • t j) = resTop M U (t j) := hc0
  have hsum : (∑ j, X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (a j) * c j) •
        resTop M U (∑ j, a j • t j) =
      (1 : Γ(X, U)) • resTop M U (∑ j, a j • t j) := by
    rw [Finset.sum_smul, one_smul]
    show _ = M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (∑ j, a j • t j)
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul, hc j, Scheme.Modules.map_smul]
  have h1 : ∑ j, X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (a j) * c j = 1 := hbijU.1 hsum
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (X.presheaf.germ U x hxU (c j)) := by
    by_contra hcon
    push_neg at hcon
    have hmem : ∀ j, X.presheaf.germ U x hxU
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (a j) * c j) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) := fun j => by
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hcon j))
    have hsum_mem := Ideal.sum_mem (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (t := Finset.univ) fun j _ => hmem j
    rw [← map_sum, h1, map_one] at hsum_mem
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      ((Ideal.eq_top_iff_one _).2 hsum_mem)
  refine ⟨j, X.basicOpen (c j), (X.mem_basicOpen (c j) x hxU).2 hj, fun V hV => ?_⟩
  have hVU : V ≤ U := hV.trans (X.basicOpen_le (c j))
  have hres : resTop M V (t j) =
      X.presheaf.map (homOfLE hVU).op (c j) • resTop M V (∑ j, a j • t j) := by
    have h := congrArg (res M hVU) (hc j)
    rw [res_smul, res_resTop, res_resTop] at h
    exact h.symm
  have hu : IsUnit (X.presheaf.map (homOfLE hVU).op (c j)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro v hv
    have hvB : IsUnit (X.presheaf.germ U v (hVU hv) (c j)) :=
      (X.mem_basicOpen (c j) v (hVU hv)).1 (hV hv)
    have e := X.presheaf.germ_res_apply (homOfLE hVU) v hv (c j)
    exact (congrArg IsUnit e).mpr hvB
  obtain ⟨w, hw⟩ := hu
  have hfun : (fun g : Γ(X, V) => g • resTop M V (t j)) =
      (fun g : Γ(X, V) => g • resTop M V (∑ j, a j • t j)) ∘ fun g => g * (w : Γ(X, V)) := by
    funext g
    simp only [Function.comp_apply, hres, ← hw, mul_smul]
  change Function.Bijective fun g : Γ(X, V) => g • resTop M V (t j)
  rw [hfun]
  exact (hU V hVU).comp w.mulRight_bijective

/-- **Q6.** Suppose every global section of `L'` lies in the `S'`-span of the sections
satisfying `P` (for the action through `f'`), and `P 0` holds. Then finitely many `P`-sections
`τ` span the sections `σ` of any presentation, with coefficients from `S'`.

Truth check: each `σ i` lies in the span of a finite subset of the `P`-sections. Take the union
of these finite subsets, enumerate it, and pad with `0`. -/
theorem exists_sections_of_span {S' : Type u} [CommRing S'] {X' : Scheme.{u}}
    (f' : X' ⟶ Spec (CommRingCat.of S')) (L' : X'.Modules) {N : ℕ} (σ : Fin (N + 1) → Γ(L', ⊤))
    (P : Γ(L', ⊤) → Prop) (hP0 : P 0)
    (hspan : letI := moduleTop f' L'; ∀ n : Γ(L', ⊤), n ∈ Submodule.span S' {d | P d}) :
    ∃ (M : ℕ) (τ : Fin (M + 1) → Γ(L', ⊤)), (∀ j, P (τ j)) ∧
      ∀ i, ∃ c : Fin (M + 1) → S', σ i =
        ∑ j, ((f'.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S')).inv.hom (c j))) •
          τ j := by
  classical
  letI := moduleTop f' L'
  -- a finite subset of the `P`-sections spanning each `σ i`
  choose T hTP hTσ using fun i => Submodule.mem_span_finite_of_mem_span (hspan (σ i))
  let T₀ : Finset Γ(L', ⊤) := Finset.univ.biUnion T
  have hT₀P : ∀ d ∈ T₀, P d := fun d hd => by
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hd
    exact hTP i hi
  let τ' : Fin T₀.card → Γ(L', ⊤) := fun j => (T₀.equivFin.symm j : Γ(L', ⊤))
  have hrange : Set.range τ' = (T₀ : Set Γ(L', ⊤)) := by
    ext d
    constructor
    · rintro ⟨j, rfl⟩; exact (T₀.equivFin.symm j).2
    · intro hd; exact ⟨T₀.equivFin ⟨d, hd⟩, by simp [τ']⟩
  have hmem : ∀ i, σ i ∈ Submodule.span S' (Set.range τ') := fun i => by
    rw [hrange]
    refine Submodule.span_mono ?_ (hTσ i)
    intro d hd
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hd⟩
  refine ⟨T₀.card, Fin.cons 0 τ', fun j => ?_, fun i => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hP0
    · simpa using hT₀P _ (T₀.equivFin.symm j).2
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S').mp (hmem i)
    refine ⟨Fin.cons 0 c, ?_⟩
    rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_zero, smul_zero, zero_add]
    simp only [Fin.cons_succ]
    exact hc.symm

/-- **Q7 and Q8.** In the setting of Q6, the `P`-sections `τ` carry a presentation `𝔗` of `L'`
over `S'`, and its presentation map is a closed immersion.

Truth check: the sections of the given closed-immersion presentation frame near every point,
and each is an `S'`-combination of the `τ`. So some `τ j` frames near every point
(`framesNear_of_sum`), and G5 then gives `𝔗` with `𝔗.σ = τ`. The FLT leaf
`isClosedImmersion_toProj_of_forall_exists_eq_sum_smul` makes `𝔗.toProj` a closed immersion. -/
theorem exists_closedImmersion_presentation_of_span {S' : Type u} [CommRing S'] {X' : Scheme.{u}}
    (f' : X' ⟶ Spec (CommRingCat.of S')) (L' : X'.Modules) (hva : CIBS L' f')
    (P : Γ(L', ⊤) → Prop) (hP0 : P 0)
    (hspan : letI := moduleTop f' L'; ∀ n : Γ(L', ⊤), n ∈ Submodule.span S' {d | P d}) :
    ∃ (M : ℕ) (𝔗 : Pres L' f' M), (∀ j, P (𝔗.σ j)) ∧ IsClosedImmersion 𝔗.toProj := by
  obtain ⟨N, 𝔓, h𝔓⟩ := hva
  obtain ⟨M, τ, hτP, hτσ⟩ := exists_sections_of_span f' L' 𝔓.σ P hP0 hspan
  -- some `τ j` frames near every point
  have hframes : ∀ x : X', ∃ j, FramesNear L' (τ j) x := by
    intro x
    obtain ⟨i, hi⟩ :=
      ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationBasics.PresChart.exists_mem_basicOpen_X S' N
        (𝔓.toProj.base x)
    have hfr : FramesNear L' (𝔓.σ i) x :=
      ⟨𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S')
          (MvPolynomial.X i), hi, fun V hV => 𝔓.frame i V hV⟩
    obtain ⟨c, hc⟩ := hτσ i
    rw [hc] at hfr
    exact framesNear_of_sum L' _ τ x hfr
  obtain ⟨𝔗, h𝔗⟩ :=
    ZInQ.Contrib.CloudR2NOS.ClosedSection.ProjOfFrames.presentationOfFramesNear f' L' M τ hframes
  refine ⟨M, 𝔗, fun j => by rw [h𝔗]; exact hτP j, ?_⟩
  refine ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_forall_exists_eq_sum_smul
    𝔓 𝔗 (fun i => ?_) h𝔓
  obtain ⟨c, hc⟩ := hτσ i
  exact ⟨c, by rw [h𝔗]; exact hc⟩

end ZInQ.Contrib.CloudR2NOS.Descent
