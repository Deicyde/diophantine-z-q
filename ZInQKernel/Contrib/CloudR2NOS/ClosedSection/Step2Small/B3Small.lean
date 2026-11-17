/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 Step-2 small obligations for C3's B3 (`Step2B3/FieldDescent.lean` 1c49e9c7; statements used
verbatim through the import), PROVED natively. SOURCE ONLY, UNCOMPILED. Native HELD.
Universe u, default options.

* `presentationFramesEverywhere`: every point lies over some standard chart `D₊(Xᵢ)`
  (`PresChart.exists_mem_basicOpen_X`), where the presentation's frame field gives `σᵢ`.
* `projSpaceMapSurjective`: `ℙ^m_K → ℙ^m_k` is the base change (adapted FLT `isPullback_map`) of
  the surjective `Spec K → Spec k`; surjectivity is stable under base change (Mathlib).
* `framesNearOfSum`: if `s = ∑ aⱼ tⱼ` frames near `x` on `U`, write `tⱼ|_U = cⱼ s|_U`; then
  `∑ aⱼ cⱼ = 1` on `U`, so some germ `cⱼ,ₓ` is a unit (local ring), and `tⱼ` frames on the basic
  open of `cⱼ` (unit multiple of a frame). Invertibility of `M` is not needed.
(`PulledSectionsSpan` is delivered separately.)
Truth: all TRUE (these are the proofs).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B3.FieldDescent

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small

open ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationBasics

/-- **`PresentationFramesEverywhere` proved.** -/
theorem presentationFramesEverywhere :
    ZInQ.Contrib.CloudR2NOS.Step2B3.PresentationFramesEverywhere.{u} := by
  intro R _ X f M N 𝔓 x
  obtain ⟨i, hi⟩ := PresChart.exists_mem_basicOpen_X R N (𝔓.toProj.base x)
  exact ⟨i, 𝔓.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i),
    hi, fun V hV => 𝔓.frame i V hV⟩

/-- **`ProjSpaceMapSurjective` proved.** -/
theorem projSpaceMapSurjective : ZInQ.Contrib.CloudR2NOS.Step2B3.ProjSpaceMapSurjective.{u} := by
  intro k K _ _ _ m
  have hpb :=
    ZInQ.Contrib.CloudR2NOS.ClosedSection.FLTA.AlgebraicGeometry.ProjSpace.isPullback_map k K m
  haveI : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  exact (MorphismProperty.of_isPullback (P := @Surjective) hpb.flip inferInstance).surj

/-- **`FramesNearOfSum` proved.** -/
theorem framesNearOfSum : ZInQ.Contrib.CloudR2NOS.Step2B3.FramesNearOfSum.{u} := by
  intro X M _ m a t x hfr
  obtain ⟨U, hxU, hU⟩ := hfr
  -- the frame on `U` and the coefficients of the `t j`
  have hbijU := hU U le_rfl
  choose c hc0 using fun j => hbijU.2 (resTop M U (t j))
  have hc : ∀ j, c j • resTop M U (∑ j, a j • t j) = resTop M U (t j) := hc0
  -- `∑ aⱼ cⱼ = 1` on `U`
  have hsum : (∑ j, X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (a j) * c j) •
        resTop M U (∑ j, a j • t j) =
      (1 : Γ(X, U)) • resTop M U (∑ j, a j • t j) := by
    rw [Finset.sum_smul, one_smul]
    show _ = M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (∑ j, a j • t j)
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul, hc j, Scheme.Modules.map_smul]
  have h1 : ∑ j, X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (a j) * c j = 1 := hbijU.1 hsum
  -- some `cⱼ` has a unit germ at `x`
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
  -- `tⱼ` frames on the basic open of `cⱼ`
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

end ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small
