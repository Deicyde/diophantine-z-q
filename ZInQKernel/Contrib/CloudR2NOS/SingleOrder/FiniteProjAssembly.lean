/-
# H5 / NOS round 2, lane 1: a finite ProjPresentation has a positive Source power with a CLOSED presentation

Newly authored glue (H5 round-2 lane 1, 2026-11-15), additive to cp9–cp12. Inputs read-only: the canonical
Source port (LITERAL `ProjPresentation`, `tensorPow`, `tensorPowSection`, frames, `ProjSpace.π` and its
properness, `ProjSpace.awayι_comp_π`, `ProjSpace.adjoin_range_ratio`, the constructor
`exists_projPresentation_of_iSup_eq_top`; FLT @ 6e837e75…, Apache-2.0, Anthropic, PBC), W07 (twists,
free generators; Jacobian-Challenge @ c4254cce…, Apache-2.0) and Mathlib.

This file: the constants of a chart (pulled back along the presentation map) are the restrictions of the
base constants, and the chart-ring generation of a finite chart algebra by constants, ratios and module
generators.
-/
import ZInQKernel.Contrib.CloudR2NOS.SingleOrder.FiniteProjExtend
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry HomogeneousLocalization
open AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.SingleOrder.FiniteProjPower

section Constants

variable {R : Type u} [CommRing R] {N : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

theorem topIso_hom_ι_appTop {X : Scheme.{u}} (U : X.Opens) (y : Γ(X, ⊤)) :
    U.topIso.hom (U.ι.appTop y) = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op y := by
  rw [Scheme.Opens.ι_appTop]
  change X.presheaf.map (eqToHom U.ι_image_top.symm).op (X.presheaf.map (homOfLE le_top).op y) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem awayToSection_algebraMap (k : Fin (N + 1)) (r : R) :
    Proj.awayToSection 𝒜 (MvPolynomial.X k)
        (algebraMap R (Away 𝒜 (MvPolynomial.X k)) r) =
      (Proj 𝒜).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 (MvPolynomial.X k) ≤ ⊤)).op
        ((ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.π R N).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) := by
  set e := Proj.basicOpenIsoSpec 𝒜 (MvPolynomial.X k) (X_mem_one (R := R) (N := N) k) Nat.one_pos
  set s := (Scheme.ΓSpecIso (CommRingCat.of R)).inv r
  set y := (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.π R N).appTop s
  have key : (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜 (MvPolynomial.X k)))).hom
      ((Proj.awayι 𝒜 (MvPolynomial.X k) (X_mem_one (R := R) (N := N) k) Nat.one_pos).appTop y) =
        algebraMap R _ r := by
    have h := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜 (MvPolynomial.X k)))).hom
      (g.appTop s)) (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.awayι_comp_π R N k)
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
    refine h.trans ?_
    have h' := congrArg (fun g => g.hom s) (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (algebraMap R (Away 𝒜 (MvPolynomial.X k)))))
    simp only [CommRingCat.comp_apply] at h'
    refine h'.trans ?_
    simp [s]
  have hι : (Proj.awayι 𝒜 (MvPolynomial.X k) (X_mem_one (R := R) (N := N) k) Nat.one_pos).appTop =
      (Proj.basicOpen 𝒜 (MvPolynomial.X k)).ι.appTop ≫ e.inv.appTop := by
    rw [← Proj.basicOpenIsoSpec_inv_ι, Scheme.Hom.comp_appTop]
  have hinv : ∀ z, e.hom.appTop (e.inv.appTop z) = z := by
    intro z
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.hom_inv_id]
    simp
  have hhom : e.hom.appTop = (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection 𝒜 (MvPolynomial.X k) ≫
      (Proj.basicOpen 𝒜 (MvPolynomial.X k)).topIso.inv := by
    rw [Proj.basicOpenIsoSpec_hom]
    exact Proj.basicOpenToSpec_app_top 𝒜 (MvPolynomial.X k)
  have hz := hinv ((Proj.basicOpen 𝒜 (MvPolynomial.X k)).ι.appTop y)
  rw [hhom, CommRingCat.comp_apply, CommRingCat.comp_apply] at hz
  rw [hι, CommRingCat.comp_apply] at key
  rw [key] at hz
  have hz' := congrArg (Proj.basicOpen 𝒜 (MvPolynomial.X k)).topIso.hom hz
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] at hz'
  rw [hz', topIso_hom_ι_appTop]


variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {L : X.Modules}
  (𝔓 : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation L f N)

/-- The base constant `r`, restricted to an open of `X`. -/
abbrev baseConst (U : X.Opens) (r : R) : Γ(X, U) :=
  X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))

/-- Pulled back along a presentation map, the chart constant is the base constant. -/
theorem chart_const (k : Fin (N + 1)) (r : R) :
    𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X k))
        (Proj.awayToSection 𝒜 (MvPolynomial.X k) (algebraMap R (Away 𝒜 (MvPolynomial.X k)) r)) =
      baseConst (f := f) (chart 𝔓 k) r := by
  rw [awayToSection_algebraMap, app_map_apply 𝔓.toProj le_top]
  have hf : 𝔓.toProj.appTop ((ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.π R N).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) = f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, 𝔓.toProj_π]
  erw [hf]
  rfl

end Constants

section Generation

variable {R : Type u} [CommRing R] {N : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules}
  (𝔓 : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation M f N)

local notation "TP" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow M

/-- A finite chart algebra is generated as a RING by the base constants, finitely many module
generators and the ratios `X_j / X_i` (Source `ProjSpace.adjoin_range_ratio`, Mathlib `basicOpenIsoAway`). -/
theorem chart_closure_eq_top [IsFinite 𝔓.toProj] (i : Fin (N + 1)) :
    ∃ (k : ℕ) (g : Fin k → Γ(X, chart 𝔓 i)),
      Subring.closure (Set.range (baseConst (f := f) (chart 𝔓 i)) ∪ Set.range g ∪
        Set.range (chartRatio 𝔓 i)) = ⊤ := by
  have hX := X_mem_one (R := R) (N := N) i
  have haff : IsAffineOpen (Proj.basicOpen 𝒜 (MvPolynomial.X i)) :=
    Proj.isAffineOpen_basicOpen 𝒜 _ hX Nat.one_pos
  set φ := 𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X i)) with hφ
  have hfin : φ.hom.Finite := IsFinite.finite_app 𝔓.toProj _ haff
  letI : Algebra Γ(Proj 𝒜, Proj.basicOpen 𝒜 (MvPolynomial.X i)) Γ(X, chart 𝔓 i) := φ.hom.toAlgebra
  haveI : Module.Finite Γ(Proj 𝒜, Proj.basicOpen 𝒜 (MvPolynomial.X i)) Γ(X, chart 𝔓 i) := hfin
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := Γ(Proj 𝒜, Proj.basicOpen 𝒜 (MvPolynomial.X i)))
    (M := Γ(X, chart 𝔓 i))
  refine ⟨k, g, ?_⟩
  set S := Subring.closure (Set.range (baseConst (f := f) (chart 𝔓 i)) ∪ Set.range g ∪
    Set.range (chartRatio 𝔓 i)) with hS
  let ψ : Away 𝒜 (MvPolynomial.X i) →+* Γ(X, chart 𝔓 i) :=
    φ.hom.comp (Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom
  let T : Subalgebra R (Away 𝒜 (MvPolynomial.X i)) :=
    { toSubsemiring := (S.comap ψ).toSubsemiring
      algebraMap_mem' := fun r => by
        change ψ (algebraMap R _ r) ∈ S
        apply Subring.subset_closure
        exact Or.inl (Or.inl ⟨r, (chart_const 𝔓 i r).symm⟩) }
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.adjoin_range_ratio R N i,
      Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    change ψ (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio R N i j) ∈ S
    apply Subring.subset_closure
    exact Or.inr ⟨j, rfl⟩
  have hA : ∀ a : Γ(Proj 𝒜, Proj.basicOpen 𝒜 (MvPolynomial.X i)), φ a ∈ S := by
    intro a
    obtain ⟨α, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (Proj.basicOpenIsoAway 𝒜 (MvPolynomial.X i) hX Nat.one_pos).hom).2 a
    have hα : α ∈ T := hT ▸ Algebra.mem_top
    exact hα
  rw [eq_top_iff]
  rintro z -
  have hz : z ∈ Submodule.span Γ(Proj 𝒜, Proj.basicOpen 𝒜 (MvPolynomial.X i)) (Set.range g) :=
    hg ▸ Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem x hx => exact Subring.subset_closure (Or.inl (Or.inr hx))
  | zero => exact S.zero_mem
  | add x y _ _ hx hy => exact S.add_mem hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def]
    exact S.mul_mem (hA a) hx

/-- The global section `σ_iᵐ`, restricted to the chart of `X_i`, is the chart frame power. -/
theorem tensorPowSection_sigma_restrict (m : ℕ) (i : Fin (N + 1)) {W : X.Opens} (hW : W ≤ chart 𝔓 i) :
    (TP m).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPowSection (𝔓.σ i) m) =
      (TP m).presheaf.map (homOfLE hW).op (chartSigmaPow 𝔓 i m) := by
  rw [ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.map_tensorPowSection, chartSigmaPow,
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.map_tensorPowSection, chartSigma,
    presheaf_map_homOfLE_map_homOfLE]

/-- **Chart comparison.** If a presentation of `M^{⊗m}` (`m > 0`) uses `σ_i^{⊗m}` as its `k`-th section,
then its `k`-th chart lies inside the chart of `X_i`. -/
theorem chart_le_of_sigma_eq {m : ℕ} (hm : 0 < m) {N' : ℕ}
    (𝔓' : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation (TP m) f N')
    (k : Fin (N' + 1)) (i : Fin (N + 1))
    (hσ : 𝔓'.σ k = ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPowSection (𝔓.σ i) m) :
    chart 𝔓' k ≤ chart 𝔓 i := by
  intro x hx
  obtain ⟨j, hj⟩ := chart_cover 𝔓 x
  have hWk : chart 𝔓' k ⊓ chart 𝔓 j ≤ chart 𝔓' k := inf_le_left
  have hWj : chart 𝔓' k ⊓ chart 𝔓 j ≤ chart 𝔓 j := inf_le_right
  set ρ := X.presheaf.map (homOfLE hWj).op (chartRatio 𝔓 j i) with hρ
  have hrel : (TP m).presheaf.map (homOfLE (le_top : chart 𝔓' k ⊓ chart 𝔓 j ≤ ⊤)).op (𝔓'.σ k) =
      ρ ^ m • (TP m).presheaf.map (homOfLE hWj).op (chartSigmaPow 𝔓 j m) := by
    rw [hσ, ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.map_tensorPowSection, chartSigmaPow,
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.map_tensorPowSection,
      ← ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPowSection_smul,
      chartRatio_smul 𝔓 j i hWj]
  obtain ⟨c, hc⟩ := (𝔓'.frame k _ hWk).2 ((TP m).presheaf.map (homOfLE hWj).op (chartSigmaPow 𝔓 j m))
  change c • (TP m).presheaf.map (homOfLE (le_top : chart 𝔓' k ⊓ chart 𝔓 j ≤ ⊤)).op (𝔓'.σ k) = _ at hc
  rw [hrel, smul_smul] at hc
  have h1 : c * ρ ^ m = 1 := by
    apply (((isFrameOn_chartSigma 𝔓 j).tensorPowSection m).bijective hWj hWj).1
    change (c * ρ ^ m) • (TP m).presheaf.map (homOfLE hWj).op (chartSigmaPow 𝔓 j m) =
      (1 : Γ(X, chart 𝔓' k ⊓ chart 𝔓 j)) • (TP m).presheaf.map (homOfLE hWj).op (chartSigmaPow 𝔓 j m)
    rw [one_smul]
    exact hc
  have hu : IsUnit ρ :=
    (isUnit_pow_iff hm.ne').mp (IsUnit.of_mul_eq_one c (by rw [mul_comm]; exact h1))
  have hWD : chart 𝔓' k ⊓ chart 𝔓 j ≤ X.basicOpen (chartRatio 𝔓 j i) := by
    have h2 := X.basicOpen_of_isUnit hu
    rw [hρ, Scheme.basicOpen_res] at h2
    rw [← h2]
    exact inf_le_right
  rw [basicOpen_chartRatio] at hWD
  exact (hWD ⟨hx, hj⟩).2

/-- **Chart surjectivity.** If the `k`-th section of a presentation of `M^{⊗m}` is `σ_i^{⊗m}`, its chart
equals the chart of `X_i`, and the chart ring of `X_i` is generated as a ring by the base constants and
elements `b` each of which is the ratio of some section of the presentation to `σ_i^{⊗m}`, then the
`k`-th chart map of the presentation is surjective. -/
theorem chart_surjective {m : ℕ} {N' : ℕ}
    (𝔓' : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation (TP m) f N')
    (k : Fin (N' + 1)) (i : Fin (N + 1))
    (hσ : 𝔓'.σ k = ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPowSection (𝔓.σ i) m)
    (hchart : chart 𝔓' k = chart 𝔓 i) (G : Set Γ(X, chart 𝔓 i))
    (hG : ∀ b ∈ G, ∃ k' : Fin (N' + 1),
      (TP m).presheaf.map (homOfLE (le_top : chart 𝔓 i ≤ ⊤)).op (𝔓'.σ k') = b • chartSigmaPow 𝔓 i m)
    (hgen : Subring.closure (Set.range (baseConst (f := f) (chart 𝔓 i)) ∪ G) = ⊤) :
    Function.Surjective (𝔓'.toProj.app
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X k))) := by
  have hle : chart 𝔓 i ≤ chart 𝔓' k := hchart.ge
  haveI : IsIso (homOfLE hle) := ⟨homOfLE hchart.le, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hρbij : Function.Bijective (X.presheaf.map (homOfLE hle).op) :=
    ConcreteCategory.bijective_of_isIso _
  let Φ := (X.presheaf.map (homOfLE hle).op).hom.comp
    (𝔓'.toProj.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)
      (MvPolynomial.X k))).hom
  have hσk : (TP m).presheaf.map (homOfLE (le_top : chart 𝔓 i ≤ ⊤)).op (𝔓'.σ k) = chartSigmaPow 𝔓 i m := by
    rw [hσ, tensorPowSection_sigma_restrict 𝔓 m i (le_refl _), presheaf_map_id_apply]
  have hrange : Φ.range = ⊤ := by
    rw [eq_top_iff, ← hgen, Subring.closure_le]
    rintro z (⟨r, rfl⟩ | hb)
    · refine ⟨Proj.awayToSection _ (MvPolynomial.X k) (algebraMap R _ r), ?_⟩
      change X.presheaf.map (homOfLE hle).op (𝔓'.toProj.app _ (Proj.awayToSection _ _ (algebraMap R _ r))) = _
      rw [chart_const 𝔓' k r, baseConst, baseConst, presheaf_map_map]
    · obtain ⟨k', hk'⟩ := hG z hb
      refine ⟨Proj.awayToSection _ (MvPolynomial.X k)
        (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio R N' k k'), ?_⟩
      have hrat := congrArg ((TP m).presheaf.map (homOfLE hle).op) (𝔓'.app_ratio_smul k k')
      rw [Scheme.Modules.map_smul, presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE,
        hσk, hk'] at hrat
      apply (((isFrameOn_chartSigma 𝔓 i).tensorPowSection m).bijective (le_refl _) (le_refl _)).1
      change Φ _ • (TP m).presheaf.map (homOfLE (le_refl _)).op (chartSigmaPow 𝔓 i m) =
        z • (TP m).presheaf.map (homOfLE (le_refl _)).op (chartSigmaPow 𝔓 i m)
      rw [presheaf_map_id_apply]
      exact hrat
  intro z
  obtain ⟨w, hw⟩ := (RingHom.range_eq_top.mp hrange) (X.presheaf.map (homOfLE hle).op z)
  exact ⟨w, hρbij.1 hw⟩

end Generation

section Final

variable {R : Type u} [CommRing R] {N : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules}
  (𝔓 : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation M f N)

local notation "TP" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow M

/-- A finite presentation map makes the structure morphism proper (Source `ProjSpace.isProper_π`). -/
theorem isProper_of_isFinite [IsFinite 𝔓.toProj] : IsProper f := by
  rw [← 𝔓.toProj_π]
  infer_instance

/-- **The finite-by-sections → positive-power closed-immersion upgrade.** For an ACTUAL Source
presentation `𝔓 : M.ProjPresentation f N` whose map `𝔓.toProj` is FINITE (any commutative ring `R`, any
universe), some positive LITERAL Source tensor power `M.tensorPow n` has a Source presentation whose map is a
CLOSED IMMERSION. The new presentation's sections are `σ_i^{⊗n}` and global extensions (Corner C) of
`g • σ_i^{⊗n}` for module generators `g` of the finite chart algebras and of the ratios `X_j / X_i`; its map
is a closed immersion by chart surjectivity and properness (Corner D₁). -/
theorem exists_closedImmersionBySections_tensorPow [IsFinite 𝔓.toProj] :
    ∃ n : ℕ, 0 < n ∧
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections (TP n) f := by
  classical
  choose k g hgen using chart_closure_eq_top 𝔓
  let b : ∀ i : Fin (N + 1), Fin (k i) ⊕ Fin (N + 1) → Γ(X, chart 𝔓 i) :=
    fun i => Sum.elim (g i) (chartRatio 𝔓 i)
  choose m₀ hm₀ using fun p : (Σ i : Fin (N + 1), Fin (k i) ⊕ Fin (N + 1)) =>
    exists_extension 𝔓 p.1 (b p.1 p.2)
  set m := Finset.univ.sup m₀ + 1 with hmdef
  have hm : ∀ p, m₀ p ≤ m := fun p => (Finset.le_sup (Finset.mem_univ p)).trans (Nat.le_succ _)
  have hmpos : 0 < m := Nat.succ_pos _
  choose t ht using fun p => hm₀ p m (hm p)
  let J := Fin (N + 1) ⊕ (Σ i : Fin (N + 1), Fin (k i) ⊕ Fin (N + 1))
  have hcard : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨Sum.inl 0⟩
  set N' := Fintype.card J - 1 with hN'
  let e : Fin (N' + 1) ≃ J := (finCongr (Nat.sub_add_cancel hcard)).trans (Fintype.equivFin J).symm
  let σJ : J → Γ(TP m, ⊤) := Sum.elim
    (fun i => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPowSection (𝔓.σ i) m) t
  let UJ : J → X.Opens := Sum.elim (chart 𝔓) (fun _ => ⊥)
  have hU' : iSup (UJ ∘ e) = ⊤ := by
    refine top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ?_
    obtain ⟨i, hi⟩ := chart_cover 𝔓 x
    exact ⟨e.symm (Sum.inl i), by simpa [UJ] using hi⟩
  have hframe : ∀ (k' : Fin (N' + 1)) (V : X.Opens), V ≤ (UJ ∘ e) k' →
      Function.Bijective fun c : Γ(X, V) => c • (TP m).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ((σJ ∘ e) k') := by
    intro k' V hV
    simp only [Function.comp_apply] at hV ⊢
    rcases hj : e k' with i | q
    · rw [hj] at hV
      simp only [UJ, σJ, Sum.elim_inl] at hV ⊢
      rw [tensorPowSection_sigma_restrict 𝔓 m i hV]
      exact ((isFrameOn_chartSigma 𝔓 i).tensorPowSection m).bijective hV hV
    · rw [hj] at hV
      simp only [UJ, Sum.elim_inr] at hV
      have hVbot : V = ⊥ := le_bot_iff.mp hV
      haveI : Subsingleton Γ(X, V) :=
        CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hVbot)
      haveI : Subsingleton Γ(TP m, V) := Module.subsingleton Γ(X, V) _
      exact ⟨fun a c _ => Subsingleton.elim a c, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  obtain ⟨𝔓', h𝔓σ, h𝔓U⟩ :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top
      f (TP m) N' (σJ ∘ e) (UJ ∘ e) hU' hframe
  have hσk : ∀ i, 𝔓'.σ (e.symm (Sum.inl i)) =
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPowSection (𝔓.σ i) m := by
    intro i
    rw [h𝔓σ]
    simp [σJ]
  have hchart : ∀ i, chart 𝔓' (e.symm (Sum.inl i)) = chart 𝔓 i := by
    intro i
    refine le_antisymm (chart_le_of_sigma_eq 𝔓 hmpos 𝔓' _ i (hσk i)) ?_
    have := h𝔓U (e.symm (Sum.inl i))
    simpa [UJ] using this
  haveI hfP : IsProper f := isProper_of_isFinite 𝔓
  haveI : IsProper (𝔓'.toProj ≫ ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.π R N') := by
    rw [𝔓'.toProj_π]
    exact hfP
  haveI : IsProper 𝔓'.toProj :=
    IsProper.of_comp 𝔓'.toProj (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.π R N')
  refine ⟨m, hmpos, closedImmersionBySections_of_chart_surjective 𝔓'
    (Set.range fun i => e.symm (Sum.inl i)) ?_ ?_ ?_⟩
  · intro x
    obtain ⟨i, hi⟩ := chart_cover 𝔓 x
    exact ⟨e.symm (Sum.inl i), ⟨i, rfl⟩, (hchart i).symm ▸ hi⟩
  · rintro _ ⟨i, rfl⟩
    rw [hchart i]
    exact isAffineOpen_chart 𝔓 i
  · rintro _ ⟨i, rfl⟩
    refine chart_surjective 𝔓 𝔓' _ i (hσk i) (hchart i) (Set.range (b i)) ?_ ?_
    · rintro _ ⟨q, rfl⟩
      refine ⟨e.symm (Sum.inr ⟨i, q⟩), ?_⟩
      rw [h𝔓σ]
      simpa [σJ] using ht ⟨i, q⟩
    · rw [← hgen i, Set.Sum.elim_range, Set.union_assoc]

/-- **FiniteBySections → positive power ClosedImmersionBySections**, in the Source's own predicates. -/
theorem exists_closedImmersionBySections_tensorPow_of_finiteBySections
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules}
    (hM : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections M f) :
    ∃ n : ℕ, 0 < n ∧
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections
        (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow M n) f := by
  obtain ⟨N, 𝔓, h𝔓⟩ := hM
  haveI := h𝔓
  exact exists_closedImmersionBySections_tensorPow 𝔓

end Final

end ZInQ.Contrib.CloudR2NOS.SingleOrder.FiniteProjPower
