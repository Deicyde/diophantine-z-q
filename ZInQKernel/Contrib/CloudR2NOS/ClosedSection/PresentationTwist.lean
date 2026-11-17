/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section GM11 sub-gap (G1) `PresentationTwistIso`, PROVED. SOURCE ONLY, UNCOMPILED.
Native HELD. No kernel/ABI/admission grade.

(G1a) `nonempty_iso_pullback_twist`: a presentation `𝔓` of `L` identifies `L` with the pullback
along `𝔓.toProj` of the W07 twist `𝒪(1)` on the SAME `Proj R[T₀..T_N]` (FLT coordinates `Fin`).
Proof: W07 `nonempty_iso_of_isFreeGenerator` on the cover `toProj⁻¹ D₊(Xᵢ)`. Generators: the frames
`σ i` of `L`, and the pulled-back GLOBAL sections `Xᵢ` of `𝒪(1)` (W07 `unitToTwist`), which are free
by W07 `isFreeGenerator_unitToTwist` and the adapted FLT frame pullback (`FramePullback.main`).
Transition functions agree: both equal `toProj^♯(awayToSection (Xⱼ/Xᵢ))` — for `L` by the
presentation field `app_ratio_smul`, for `𝒪(1)` by W07 `map_unitToTwist_eq_smul` pulled back.

(G1b) the graded renaming `MvPolynomial.rename Equiv.ulift` gives a `Proj` ISOMORPHISM
`Proj R[T_Fin] ≅ Proj R[T_{ULift Fin}]` (Mathlib `Proj.map`, `Proj.map_comp`, `Proj.map_id`), and the
twist transports along it (W07 `Proj.pullbackTwistIso`). This is an actual graded-rename iso
(C6 review 012), not a universe transfer.
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.PresentationBasics
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.Pullback
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Gluing
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationTwist

open PresentationBasics

local notation "Pres" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation
local notation "FLTratio" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio
local notation "FLTXmem" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.X_mem_one

/-! ### (G1a) the presented module is the pullback of `𝒪(1)` -/

section G1a

variable (R : Type u) [CommRing R] (N : ℕ)

/-- `𝒪(1)` on `Proj R[T₀..T_N]` in the degree form `0 + 1` produced by W07 `unitToTwist`. -/
abbrev O1 : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).Modules :=
  Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (0 + ((1 : ℕ) : ℤ))

/-- The global section `Xᵢ` of `𝒪(1)` (W07 `unitToTwist`). -/
noncomputable def coordSection (i : Fin (N + 1)) : Γ(O1 R N, ⊤) :=
  Scheme.Modules.Hom.app (Proj.unitToTwist (FLTXmem R N i)) ⊤
    (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R), ⊤))

/-- `Xᵢ` freely generates `𝒪(1)` on every open inside `D₊(Xᵢ)`. -/
theorem coordSection_frame (i : Fin (N + 1))
    (V : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).Opens)
    (hV : V ≤ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i)) :
    Function.Bijective fun g : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R), V) =>
      g • resTop (O1 R N) V (coordSection R N i) := by
  have hfree := Proj.isFreeGenerator_unitToTwist (FLTXmem R N i)
  have he : Scheme.Modules.Hom.app (Proj.unitToTwist (FLTXmem R N i))
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))
      (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))) =
      resTop (O1 R N) (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (MvPolynomial.X i)) (coordSection R N i) := by
    have h1 : res (Scheme.Modules.unit (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)))
        (le_top : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (MvPolynomial.X i) ≤ ⊤)
        (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R), ⊤)) =
        (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R),
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))) := by
      change ((Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).ringCatSheaf.obj.map
        (homOfLE le_top).op).hom 1 = 1
      exact map_one _
    rw [← h1, app_res]
    rfl
  have hb := hfree V hV
  rw [he, map_resTop] at hb
  exact hb

/-- The twist transition rule `Xⱼ = (Xⱼ/Xᵢ) • Xᵢ` on `D₊(Xᵢ)`, with the FLT ratio. -/
theorem coordSection_ratio (i j : Fin (N + 1)) :
    resTop (O1 R N) (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (MvPolynomial.X i)) (coordSection R N j) =
      Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)
          (FLTratio R N i j) •
        resTop (O1 R N) (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (MvPolynomial.X i)) (coordSection R N i) :=
  Proj.map_unitToTwist_eq_smul (FLTXmem R N j) (FLTXmem R N i) (by simpa using FLTXmem R N j)

variable {R N}

/-- **(G1a)** A presentation identifies the presented module with the pullback of `𝒪(1)`. -/
theorem nonempty_iso_pullback_twist {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    {L : X.Modules} (𝔓 : Pres L f N) :
    Nonempty (L ≅ (Scheme.Modules.pullback 𝔓.toProj).obj (O1 R N)) := by
  classical
  let P := (Scheme.Modules.pullback 𝔓.toProj).obj (O1 R N)
  let D : Fin (N + 1) → (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).Opens :=
    fun i => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)
  let U : Fin (N + 1) → X.Opens := fun i => 𝔓.toProj ⁻¹ᵁ D i
  let τ₀ : Fin (N + 1) → Γ(P, ⊤) := fun i =>
    show Γ(P, ⊤) from FramePullback.eta 𝔓.toProj (O1 R N) ⊤ (coordSection R N i)
  let e : ∀ i, Γ(L, U i) := fun i => resTop L (U i) (𝔓.σ i)
  let τ : ∀ i, Γ(P, U i) := fun i => resTop P (U i) (τ₀ i)
  have hU : ⨆ i, U i = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨i, hi⟩ := PresChart.exists_mem_basicOpen_X R N (𝔓.toProj x)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  have he : ∀ i, Scheme.Modules.IsFreeGenerator (e i) := by
    intro i V hV
    have h := 𝔓.frame i V hV
    simpa only [e, map_resTop] using h
  have hτ : ∀ i, Scheme.Modules.IsFreeGenerator (τ i) := by
    intro i V hV
    have h := FramePullback.main 𝔓.toProj (O1 R N) (coordSection R N i)
      (coordSection_frame R N i) V hV
    simpa only [τ, τ₀, map_resTop] using h
  -- the common transition coefficient on `W ≤ U i`
  let c : ∀ (i j : Fin (N + 1)) (W : X.Opens), W ≤ U i → Γ(X, W) := fun i j W hWi =>
    X.presheaf.map (homOfLE hWi).op
      (𝔓.toProj.app (D i) (Proj.awayToSection _ (MvPolynomial.X i) (FLTratio R N i j)))
  have hσrel : ∀ (i j : Fin (N + 1)) (W : X.Opens) (hWi : W ≤ U i),
      resTop L W (𝔓.σ j) = c i j W hWi • resTop L W (𝔓.σ i) := by
    intro i j W hWi
    have h := congrArg (res L hWi) (𝔓.app_ratio_smul i j)
    rw [res_smul, res_resTop, res_resTop] at h
    exact h.symm
  have hτrel : ∀ (i j : Fin (N + 1)) (W : X.Opens) (hWi : W ≤ U i),
      resTop P W (τ₀ j) = c i j W hWi • resTop P W (τ₀ i) := by
    intro i j W hWi
    have h1 := congrArg (FramePullback.eta 𝔓.toProj (O1 R N) (D i)) (coordSection_ratio R N i j)
    rw [FramePullback.eta_smul, ← FramePullback.res_eta, ← FramePullback.res_eta] at h1
    have h2 := congrArg (res P hWi) h1
    rw [res_smul, res_res, res_res] at h2
    exact h2
  have hc : ∀ (i j : Fin (N + 1)) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (a b : Γ(X, W)),
      a • L.presheaf.map (homOfLE hi).op (e i) = b • L.presheaf.map (homOfLE hj).op (e j) →
        a • P.presheaf.map (homOfLE hi).op (τ i) = b • P.presheaf.map (homOfLE hj).op (τ j) := by
    intro i j W hi hj a b hab
    have hab' : a • resTop L W (𝔓.σ i) = (b * c i j W hi) • resTop L W (𝔓.σ i) := by
      have h := hab
      rw [show L.presheaf.map (homOfLE hi).op (e i) = resTop L W (𝔓.σ i) from map_resTop L hi _,
        show L.presheaf.map (homOfLE hj).op (e j) = resTop L W (𝔓.σ j) from map_resTop L hj _,
        hσrel i j W hi, smul_smul] at h
      exact h
    have hac : a = b * c i j W hi := (𝔓.frame i W hi).1 hab'
    rw [show P.presheaf.map (homOfLE hi).op (τ i) = resTop P W (τ₀ i) from map_resTop P hi _,
      show P.presheaf.map (homOfLE hj).op (τ j) = resTop P W (τ₀ j) from map_resTop P hj _,
      hτrel i j W hi, smul_smul, hac]
  exact Scheme.Modules.nonempty_iso_of_isFreeGenerator hU he hc hτ

end G1a

/-! ### (G1b) graded renaming of the coordinates to `ULift` -/

section G1b

variable (R : Type u) [CommRing R]

/-- Renaming of variables along an equivalence, as a graded ring hom of polynomial gradings. -/
noncomputable def renameGraded {σ τ : Type*} (e : σ ≃ τ) :
    MvPolynomial.homogeneousSubmodule σ R →+*ᵍ MvPolynomial.homogeneousSubmodule τ R where
  toRingHom := (MvPolynomial.rename e).toRingHom
  map_mem := fun {_} {_} hx => (MvPolynomial.mem_homogeneousSubmodule _ _).2
    (((MvPolynomial.mem_homogeneousSubmodule _ _).1 hx).rename_isHomogeneous)

theorem renameGraded_apply {σ τ : Type*} (e : σ ≃ τ) (x : MvPolynomial σ R) :
    renameGraded R e x = MvPolynomial.rename e x :=
  rfl

theorem renameGraded_symm_comp {σ τ : Type*} (e : σ ≃ τ) :
    (renameGraded R e.symm).comp (renameGraded R e) = GradedRingHom.id _ := by
  refine GradedRingHom.ext fun x => ?_
  rw [GradedRingHom.comp_apply, renameGraded_apply, renameGraded_apply, MvPolynomial.rename_rename]
  simp

theorem irrelevant_le_map_renameGraded {σ τ : Type*} (e : σ ≃ τ) :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule τ R) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule σ R)).map
        (renameGraded R e) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi y hy
  have hy' : MvPolynomial.rename e.symm y ∈ MvPolynomial.homogeneousSubmodule σ R i :=
    (renameGraded R e.symm).map_mem hy
  have hmem : MvPolynomial.rename e.symm y ∈
      HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule σ R) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ hi hy'
  have hy_eq : y = renameGraded R e (MvPolynomial.rename e.symm y) := by
    rw [renameGraded_apply, MvPolynomial.rename_rename]
    simp
  rw [hy_eq]
  exact Ideal.mem_map_of_mem _ hmem

theorem proj_map_eq_id {A σ' : Type u} [CommRing A] [SetLike σ' A] [AddSubgroupClass σ' A]
    {𝒜 : ℕ → σ'} [GradedRing 𝒜] (φ : 𝒜 →+*ᵍ 𝒜) (hφ : HomogeneousIdeal.irrelevant 𝒜 ≤
      (HomogeneousIdeal.irrelevant 𝒜).map φ) (h : φ = GradedRingHom.id 𝒜) :
    Proj.map φ hφ = 𝟙 (Proj 𝒜) := by
  subst h
  exact Proj.map_id

variable (N : ℕ)

/-- The coordinate renaming `ULift (Fin (N+1)) ≃ Fin (N+1)`. -/
abbrev ulEquiv : ULift.{u} (Fin (N + 1)) ≃ Fin (N + 1) := Equiv.ulift

/-- The renaming `Proj` map `Proj R[T_Fin] ⟶ Proj R[T_{ULift Fin}]`. -/
noncomputable abbrev renameUp :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) R) :=
  Proj.map (renameGraded R (ulEquiv N)) (irrelevant_le_map_renameGraded R (ulEquiv N))

/-- The inverse renaming `Proj` map. -/
noncomputable abbrev renameDown :
    Proj (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) R) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) :=
  Proj.map (renameGraded R (ulEquiv N).symm) (irrelevant_le_map_renameGraded R (ulEquiv N).symm)

/-- The renaming map is an isomorphism (inverse: renaming back). -/
theorem isIso_renameUp : IsIso (renameUp R N) := by
  refine ⟨⟨renameDown R N, ?_, ?_⟩⟩
  · rw [renameUp, renameDown, ← Proj.map_comp]
    exact proj_map_eq_id _ _ (by simpa using renameGraded_symm_comp R (ulEquiv N).symm)
  · rw [renameUp, renameDown, ← Proj.map_comp]
    exact proj_map_eq_id _ _ (renameGraded_symm_comp R (ulEquiv N))

/-- The degree-one cover condition for the W07 twist pullback along the renaming. -/
theorem renameUp_degreeOneCover
    (point : Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) :
    ∃ element ∈ MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) R 1,
      point ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (renameGraded R (ulEquiv N) element) := by
  obtain ⟨k, hk⟩ := PresChart.exists_mem_basicOpen_X R N point
  refine ⟨MvPolynomial.X (ULift.up k),
    (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X R _), ?_⟩
  rw [renameGraded_apply, MvPolynomial.rename_X]
  exact hk

end G1b

/-- **(G1) proved.** -/
theorem presentationTwistIso : PresentationTwistIso.{u} := by
  intro R _ X f L N 𝔓
  haveI : IsIso (renameUp R N) := isIso_renameUp R N
  refine ⟨𝔓.toProj ≫ renameUp R N, fun h => by haveI := h; infer_instance, ?_⟩
  obtain ⟨iL⟩ := nonempty_iso_pullback_twist 𝔓
  have h01 : (0 : ℤ) + ((1 : ℕ) : ℤ) = 1 := by norm_num
  exact ⟨iL ≪≫ (Scheme.Modules.pullback 𝔓.toProj).mapIso
      (eqToIso (congrArg (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) h01) ≪≫
        (Proj.pullbackTwistIso (renameGraded R (ulEquiv N))
          (irrelevant_le_map_renameGraded R (ulEquiv N)) 1 (renameUp_degreeOneCover R N)).symm) ≪≫
      (Scheme.Modules.pullbackComp 𝔓.toProj (renameUp R N)).app _⟩

end ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationTwist
