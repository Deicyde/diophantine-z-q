/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section GM11 sub-gap (G2) `FiniteBySectionsNativePow`, PROVED. SOURCE ONLY, UNCOMPILED.
Native HELD. No kernel/ABI/admission grade.

Route (no native tensor-of-sections algebra needed):
1. `fbs_twist`: on `ℙ^N_R = Proj R[T₀..T_N]` the W07 twist `𝒪(b)` (`b > 0`) is finite-by-sections
   over `ProjSpace.π`: its sections are the W07 `unitToTwist` GLOBAL sections of the degree-`b`
   monomials `X^w` (`w : Fin b → Fin (N+1)`), free on `D₊(X^w)` (W07 `isFreeGenerator_unitToTwist`);
   the presentation is the proved (G5) `exists_projPresentation_of_iSup_eq_top`; the preimage of each
   standard chart is exactly the affine `D₊(X^w)` (the transition coefficient `X^w / X_i^b` is a unit
   exactly on `D₊(X^w)`), so the map is affine, and proper since `𝒪(b)` lives on proper `ℙ^N_R`;
   hence finite. (Blueprint: FLT `FiniteBySections.tensorPow`, with ring monomials in place of
   tensor words.)
2. `finiteBySectionsNativePow`: for a finite presentation `𝔓` of `L`, (G1a) gives
   `L ≅ toProj^*𝒪(1)`; native powers commute with pullback (`pullbackTensorPowIso`) and W07
   `nonempty_tensorPow_twist_one_iso` gives `𝒪(1)^{⊗n} ≅ 𝒪(n)`, so `L^{⊗n} ≅ toProj^*𝒪(n)`; pulling
   back the presentation of step 1 along `toProj` (proved C3 `projPresentationPullback`) gives map
   `toProj ≫ 𝔔.toProj`, finite as a composite of finite maps; transport along the iso (G7).
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.PresentationTwist
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.ProjOfFrames
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step3Proved

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.NativePowFBS

open PresentationBasics

local notation "Pres" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation
local notation "FBS" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections
local notation "FLTπ" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.π
local notation "FLTXmem" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.X_mem_one
local notation "FLTirrel" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.irrelevant_le_span_X

/-- A presentation over `f` is a presentation over any `f' = f` (same fields). -/
def rebase {R : Type u} [CommRing R] {X : Scheme.{u}} {f f' : X ⟶ Spec (CommRingCat.of R)}
    {M : X.Modules} {N : ℕ} (𝔓 : Pres M f N) (h : f = f') : Pres M f' N where
  σ := 𝔓.σ
  toProj := 𝔓.toProj
  toProj_π := 𝔓.toProj_π.trans h
  frame := 𝔓.frame
  app_ratio_smul := 𝔓.app_ratio_smul

section Twist

variable (R : Type u) [CommRing R] (N : ℕ)

/-- The degree-`b` monomial of a word. -/
abbrev wordMonomial (b : ℕ) (w : Fin b → Fin (N + 1)) : MvPolynomial (Fin (N + 1)) R :=
  ∏ k, MvPolynomial.X (w k)

theorem wordMonomial_mem (b : ℕ) (w : Fin b → Fin (N + 1)) :
    wordMonomial R N b w ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R b := by
  have h := SetLike.prod_mem_graded (A := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
    (F := (Finset.univ : Finset (Fin b))) (i := fun _ => 1)
    (g := fun k => (MvPolynomial.X (w k) : MvPolynomial (Fin (N + 1)) R))
    (fun k _ => FLTXmem R N (w k))
  simpa using h

theorem wordMonomial_mem_one_smul (b : ℕ) (w : Fin b → Fin (N + 1)) :
    wordMonomial R N b w ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R (1 • b) := by
  simpa using wordMonomial_mem R N b w

/-- The constant word gives `D₊(Xᵢ^b) = D₊(Xᵢ)`. -/
theorem basicOpen_wordMonomial_const (b : ℕ) (hb : 0 < b) (i : Fin (N + 1)) :
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (wordMonomial R N b (fun _ => i)) =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) := by
  rw [show wordMonomial R N b (fun _ => i) = MvPolynomial.X i ^ b by
    simp [wordMonomial, Finset.prod_const]]
  exact Proj.basicOpen_pow (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) _ b hb

/-- The GLOBAL section `X^w` of `𝒪(b)` (W07 `unitToTwist`). -/
noncomputable def wordSection (b : ℕ) (w : Fin b → Fin (N + 1)) :
    Γ(Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (0 + ((b : ℕ) : ℤ)), ⊤) :=
  Scheme.Modules.Hom.app (Proj.unitToTwist (wordMonomial_mem R N b w)) ⊤
    (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R), ⊤))

/-- `X^w` freely generates `𝒪(b)` on every open inside `D₊(X^w)`. -/
theorem wordSection_frame (b : ℕ) (w : Fin b → Fin (N + 1))
    (V : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).Opens)
    (hV : V ≤ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (wordMonomial R N b w)) :
    Function.Bijective fun g : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R), V) =>
      g • resTop (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (0 + ((b : ℕ) : ℤ))) V (wordSection R N b w) := by
  have hfree := Proj.isFreeGenerator_unitToTwist (wordMonomial_mem R N b w)
  have he : Scheme.Modules.Hom.app (Proj.unitToTwist (wordMonomial_mem R N b w))
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (wordMonomial R N b w))
      (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (wordMonomial R N b w))) =
      resTop (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (0 + ((b : ℕ) : ℤ)))
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (wordMonomial R N b w))
        (wordSection R N b w) := by
    have h1 : res (Scheme.Modules.unit (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)))
        (le_top : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (wordMonomial R N b w) ≤ ⊤)
        (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R), ⊤)) =
        (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R),
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
            (wordMonomial R N b w))) := by
      change ((Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).ringCatSheaf.obj.map
        (homOfLE le_top).op).hom 1 = 1
      exact map_one _
    rw [← h1, app_res]
    rfl
  have hb := hfree V hV
  rw [he, map_resTop] at hb
  exact hb

/-- The transition rule `X^w = (X^w / X^v) • X^v` on `D₊(X^v)` (W07 `map_unitToTwist_eq_smul`). -/
theorem wordSection_ratio (b : ℕ) (w v : Fin b → Fin (N + 1)) :
    resTop (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (0 + ((b : ℕ) : ℤ)))
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (wordMonomial R N b v))
        (wordSection R N b w) =
      Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (wordMonomial R N b v)
          (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
            (wordMonomial_mem R N b v) 1 (wordMonomial R N b w)
            (wordMonomial_mem_one_smul R N b w)) •
        resTop (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (0 + ((b : ℕ) : ℤ)))
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
            (wordMonomial R N b v)) (wordSection R N b v) :=
  Proj.map_unitToTwist_eq_smul (wordMonomial_mem R N b w) (wordMonomial_mem R N b v)
    (wordMonomial_mem_one_smul R N b w)

/-- The germ of `awayToSection (f / g)` at a point of `D₊(g)` is a unit iff the point is in
`D₊(f)` (generalising `PresChart.isUnit_germ_ratio_iff`). -/
theorem isUnit_germ_awayToSection_iff {f g : MvPolynomial (Fin (N + 1)) R} {d : ℕ}
    (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R d)
    (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R (1 • d))
    (y : Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R))
    (hy : y ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) g) :
    IsUnit ((Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).presheaf.germ
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) g) y hy
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) g
          (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
            hg 1 f hf))) ↔
      y ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) f := by
  have hle : Submonoid.powers g ≤ y.asHomogeneousIdeal.toIdeal.primeCompl :=
    Submonoid.powers_le.mpr ((Proj.mem_basicOpen _ _ y).mp hy)
  have h := ConcreteCategory.congr_hom
    (ProjectiveSpectrum.Proj.awayToSection_germ (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      g y hy)
    (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) hg 1 f hf)
  have h' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).presheaf.germ
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) g) y hy
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) g
        (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          hg 1 f hf)) =
      (Proj.stalkIso' (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) y).symm
        (HomogeneousLocalization.mapId (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) hle
          (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
            hg 1 f hf)) := h
  have e1 : IsUnit ((Proj.stalkIso' (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) y).symm
        (HomogeneousLocalization.mapId (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) hle
          (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
            hg 1 f hf))) ↔
      IsUnit (HomogeneousLocalization.mapId (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) hle
        (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          hg 1 f hf)) :=
    ⟨fun hu => by
      simpa using hu.map (Proj.stalkIso' (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) y),
      fun hu => hu.map _⟩
  rw [h']
  refine e1.trans ?_
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val, HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
    IsLocalization.AtPrime.isUnit_mk'_iff, Proj.mem_basicOpen]
  exact Iff.rfl

/-- If `X^w` generates `𝒪(b)` on an open `W ∋ y`, then `y ∈ D₊(X^w)`. -/
theorem mem_basicOpen_of_frame (b : ℕ) (hb : 0 < b) (w : Fin b → Fin (N + 1))
    (y : Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R))
    (W : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).Opens) (hyW : y ∈ W)
    (hfr : ∀ V : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).Opens, V ≤ W →
      Function.Bijective fun g : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R), V) =>
        g • resTop (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (0 + ((b : ℕ) : ℤ))) V (wordSection R N b w)) :
    y ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (wordMonomial R N b w) := by
  obtain ⟨i, hi⟩ := PresChart.exists_mem_basicOpen_X R N y
  let v : Fin b → Fin (N + 1) := fun _ => i
  let D := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
    (wordMonomial R N b v)
  have hyD : y ∈ D := by
    show y ∈ Proj.basicOpen _ (wordMonomial R N b (fun _ => i))
    rw [basicOpen_wordMonomial_const R N b hb i]
    exact hi
  let V := W ⊓ D
  have hyV : y ∈ V := ⟨hyW, hyD⟩
  have hVW : V ≤ W := inf_le_left
  have hVD : V ≤ D := inf_le_right
  let c := Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
    (wordMonomial R N b v)
    (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (wordMonomial_mem R N b v) 1 (wordMonomial R N b w) (wordMonomial_mem_one_smul R N b w))
  have hrelV : resTop (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (0 + ((b : ℕ) : ℤ))) V (wordSection R N b w) =
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).presheaf.map (homOfLE hVD).op c •
        resTop (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (0 + ((b : ℕ) : ℤ))) V (wordSection R N b v) := by
    have h := congrArg (res _ hVD) (wordSection_ratio R N b w v)
    rw [res_smul, res_resTop, res_resTop] at h
    exact h
  obtain ⟨g', hg'⟩ := (hfr V hVW).2
    (resTop (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (0 + ((b : ℕ) : ℤ)))
      V (wordSection R N b v))
  have hv := wordSection_frame R N b v V hVD
  have h1 : (g' * (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).presheaf.map
        (homOfLE hVD).op c) •
        resTop (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (0 + ((b : ℕ) : ℤ))) V (wordSection R N b v) =
      (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R), V)) •
        resTop (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (0 + ((b : ℕ) : ℤ))) V (wordSection R N b v) := by
    rw [mul_smul, ← hrelV, one_smul]
    exact hg'
  have hunit : IsUnit ((Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).presheaf.map
      (homOfLE hVD).op c) := by
    refine isUnit_iff_exists_inv.mpr ⟨g', ?_⟩
    rw [mul_comm]
    exact hv.1 h1
  have hgerm : IsUnit ((Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).presheaf.germ V
      y hyV ((Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).presheaf.map
        (homOfLE hVD).op c)) := hunit.map _
  rw [TopCat.Presheaf.germ_res_apply] at hgerm
  exact (isUnit_germ_awayToSection_iff R N (wordMonomial_mem R N b v)
    (wordMonomial_mem_one_smul R N b w) y hyD).mp hgerm

/-- **`𝒪(b)` is finite-by-sections over `ℙ^N_R`** for `b > 0`. -/
theorem fbs_twist (b : ℕ) (hb : 0 < b) :
    FBS (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (0 + ((b : ℕ) : ℤ)))
      (FLTπ R N) := by
  classical
  set N' : ℕ := (N + 1) ^ b - 1 with hN'
  have hN'1 : N' + 1 = (N + 1) ^ b := Nat.sub_add_cancel (Nat.one_le_pow _ _ (Nat.succ_pos N))
  let e : Fin (N' + 1) ≃ (Fin b → Fin (N + 1)) := (finCongr hN'1).trans finFunctionFinEquiv.symm
  let U : (Fin b → Fin (N + 1)) → (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).Opens :=
    fun w => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (wordMonomial R N b w)
  have hcov : iSup (fun j => U (e j)) = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨i, hi⟩ := PresChart.exists_mem_basicOpen_X R N y
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨e.symm (fun _ => i), ?_⟩
    show y ∈ U (e (e.symm fun _ => i))
    rw [Equiv.apply_symm_apply]
    show y ∈ Proj.basicOpen _ (wordMonomial R N b (fun _ => i))
    rw [basicOpen_wordMonomial_const R N b hb i]
    exact hi
  obtain ⟨𝔔, hσ, hU⟩ := ProjOfFrames.AlgebraicGeometry.exists_projPresentation_of_iSup_eq_top
    (FLTπ R N) (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (0 + ((b : ℕ) : ℤ)))
    N' (fun j => wordSection R N b (e j)) (fun j => U (e j)) hcov
    (fun j V hV => wordSection_frame R N b (e j) V hV)
  unfold ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections
  refine ⟨N', 𝔔, ?_⟩
  -- the preimage of each standard chart is the affine `D₊(X^w)`
  have hchart : ∀ j : Fin (N' + 1),
      𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)
        (MvPolynomial.X j) = U (e j) := by
    intro j
    refine le_antisymm (fun y hy => ?_) (hU j)
    obtain ⟨W, hyW, hfr⟩ := (PresChart.mem_preimage_basicOpen_iff 𝔔 j y).mp hy
    simp only [hσ] at hfr
    exact mem_basicOpen_of_frame R N b hb (e j) y W hyW hfr
  haveI : IsAffineHom 𝔔.toProj := by
    let Uc : Fin (N' + 1) →
        (Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)).affineOpens := fun j =>
      ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j),
        Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)
          (MvPolynomial.X j) (FLTXmem R N' j) Nat.one_pos⟩
    have hUc : ⨆ j, (Uc j : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)).Opens) =
        ⊤ :=
      Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)
        (fun i => MvPolynomial.X i) (FLTirrel R N')
    refine (HasAffineProperty.iff_of_iSup_eq_top (P := @IsAffineHom) (f := 𝔔.toProj) Uc hUc).mpr
      fun j => ?_
    show IsAffine (𝔔.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j))
    rw [hchart j]
    exact Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (wordMonomial R N b (e j)) (wordMonomial_mem R N b (e j)) hb
  haveI : IsProper (𝔔.toProj ≫ FLTπ R N') := by
    rw [𝔔.toProj_π]
    infer_instance
  haveI : IsProper 𝔔.toProj := IsProper.of_comp 𝔔.toProj (FLTπ R N')
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

end Twist

/-- **(G2) proved.** -/
theorem finiteBySectionsNativePow : FiniteBySectionsNativePow.{u} := by
  intro R _ X f _ L hL n hn
  obtain ⟨N, 𝔓, hfin⟩ := hL
  haveI : IsFinite 𝔓.toProj := hfin
  obtain ⟨iL⟩ := PresentationTwist.nonempty_iso_pullback_twist 𝔓
  obtain ⟨tw⟩ := Proj.nonempty_tensorPow_twist_one_iso
    (grading := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
    (fun point => by
      obtain ⟨j, hj⟩ := PresChart.exists_mem_basicOpen_X R N point
      exact ⟨_, FLTXmem R N j, hj⟩) n
  have h01 : (0 : ℤ) + ((1 : ℕ) : ℤ) = 1 := by norm_num
  have h0n : ((n : ℕ) : ℤ) = 0 + ((n : ℕ) : ℤ) := by norm_num
  let eO1 : PresentationTwist.O1 R N ≅
      Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 1 :=
    eqToIso (congrArg (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) h01)
  let eTw : (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 1).tensorPow n ≅
      Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (0 + ((n : ℕ) : ℤ)) :=
    tw ≪≫ eqToIso (congrArg (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) h0n)
  let E : L.tensorPow n ≅ (Scheme.Modules.pullback 𝔓.toProj).obj
      (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (0 + ((n : ℕ) : ℤ))) :=
    tensorPowIsoOfIso (iL ≪≫ (Scheme.Modules.pullback 𝔓.toProj).mapIso eO1) n ≪≫
      (pullbackTensorPowIso 𝔓.toProj
        (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 1) n).symm ≪≫
      (Scheme.Modules.pullback 𝔓.toProj).mapIso eTw
  obtain ⟨N', 𝔔, hfin'⟩ := fbs_twist R N n hn
  haveI : IsFinite 𝔔.toProj := hfin'
  obtain ⟨𝔔', h𝔔'⟩ := projPresentationPullback (FLTπ R N) 𝔓.toProj
    (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (0 + ((n : ℕ) : ℤ))) N' 𝔔
  unfold ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections
  refine ⟨N', transport (rebase 𝔔' 𝔓.toProj_π) E.symm, ?_⟩
  show IsFinite 𝔔'.toProj
  rw [h𝔔']
  infer_instance

end ZInQ.Contrib.CloudR2NOS.ClosedSection.NativePowFBS
