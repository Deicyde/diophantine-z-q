import ZInQKernel.Contrib.Mobius.InfraDim
import ZInQKernel.Contrib.Mobius.Glue

/-!
# mobius-contrib: curve-glue (curve facts, C2K/C3K reductions, (CI))

Part of the Contrib port (task mobius-contrib, 2026-11-13) of image-plane's single file
`scratch/image-plane/ImagePlaneFinal.lean` (which is curve-glue's `MobiusFinal.lean` plus
image-plane's (IC), (AD) and C2K proofs). This module is lines 1713-3895 of that file.

Declarations not reachable from `mobiusGlue_of_T5`, `mobiusGlue_of_t5` and
`imagePlaneCurveClosed` were removed (dependency closure computed in Lean by
`scratch/mobius-contrib/Dead.lean`, removal by `trim.py`); everything kept is verbatim
(up to collapsed runs of blank lines). Removed here (namespace `LeafQM.AV` dropped):
`CurveGlue.CMObjects`, `CurveGlue.CMPoints`, `CurveGlue.MobiusGlueNoCM`, `CurveGlue.R1R2fpRep`,
`CurveGlue.R1R2fp_of_rep`, `CurveGlue.R1pi0Props`, `CurveGlue.R2X6PropsIff`,
`CurveGlue.cmExists_of_iff`, `CurveGlue.cm_points_of_R1R2fp`, `CurveGlue.cm_points_of_R1R2fpRep`,
`CurveGlue.cm_points_of_objects`, `CurveGlue.mobiusGlueNoCM_of_L0_AD_IC_T5`,
`CurveGlue.mobiusGlueNoCM_of_L0_CI_AD_IC_T5`, `CurveGlue.mobiusGlueNoCM_of_L0_CI_G1''_T5`,
`CurveGlue.mobiusGlueNoCM_of_L0_G1'_T5`, `CurveGlue.mobiusGlueNoCM_of_L0_G1_T5`,
`CurveGlue.mobiusGlueNoCM_of_L_G1_T5`, `CurveGlue.mobiusGlueNoCM_of_glue`,
`CurveGlue.mobiusGlue_noCM_of`, `CurveGlue.mobiusGlue_noCM_of_rep`,
`CurveGlue.mobiusGlue_of_L0_AD_IC_T5`, `CurveGlue.mobiusGlue_of_L0_CI_AD_IC_T5`,
`CurveGlue.mobiusGlue_of_L0_CI_G1''_T5`, `CurveGlue.mobiusGlue_of_L0_G1'_T5`,
`CurveGlue.mobiusGlue_of_L0_G1_T5`, `CurveGlue.mobiusGlue_of_L_G1_T5`,
`CurveGlue.r2X6Props_of_iff`, `Pin.FiniteGlobalSections`, `Pin.GlobalFunctionsConst`,
`Pin.constOrOntoAlgClosed_of`, `Pin.constant_of_missed`, `Pin.cstHom`, `Pin.cstHom_apply`,
`Pin.curveFacts_of_L0_AD_IC`, `Pin.curveFacts_of_L0_CI_AD_IC`, `Pin.curveFacts_of_L0_CI_G1''`,
`Pin.curveFacts_of_L0_G1`, `Pin.curveFacts_of_L0_G1'`, `Pin.curveFacts_of_L_G1`,
`Pin.curveFacts_of_glue`, `Pin.curveFacts_of_glue'`, `Pin.curveFacts_of_glue''`,
`Pin.curveFacts_of_glue_AD`, `Pin.ev_eq_of_nilpotent`, `Pin.exists_nilpotent_sub_of_finite`,
`Pin.globalFunctionsConst_of`, `Pin.idempotent_trivial_of_isPreconnected`,
`Pin.isUnit_of_ev_ne_zero`, `Pin.mobiusGlue_of_glue`, `Pin.ratFactorAlgClosed_of_AD`,
`Pin.ratFactorAlgClosed_of_closed`, `Pin.ratFactorAlgClosed_of_irr`, `Pin.res_cst`.
-/

/-! # curve-glue: curve-facts (verbatim, without its §0 copies) and the C2K/C3K reductions -/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits
open PkgI3

/-! ## §1 Geometric components (genuine definitions) -/

/-- `S_ℚ̄ = S ×_{Spec ℚ} Spec ℚ̄` (Mathlib's pullback). -/
abbrev bcQbar (S : Over (Spec (CommRingCat.of ℚ))) : Scheme.{0} :=
  pullback S.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))

/-- The `ℚ̄`-point `Spec ℚ̄ → S_ℚ̄` (a section over `Spec ℚ̄`) induced by a `ℚ̄`-point of `S`
over `ℚ`. -/
def bcPt {S : Over (Spec (CommRingCat.of ℚ))} (y : fieldPt Qbar ⟶ S) :
    Spec (CommRingCat.of Qbar) ⟶ bcQbar S :=
  pullback.lift y.left (𝟙 _) ((Over.w y).trans (Category.id_comp _).symm)

/-- **The geometric component of a `ℚ̄`-point `y` of `S`**: the connected component of the
underlying space of `S_ℚ̄` containing the (closed) point of `S_ℚ̄` at which `bcPt y` sits. For
`S` smooth over `ℚ` the connected components of `S_ℚ̄` are its irreducible components (smooth
implies normal implies locally irreducible). -/
def geomComp {S : Over (Spec (CommRingCat.of ℚ))} (y : fieldPt Qbar ⟶ S) : Set (bcQbar S) :=
  connectedComponent (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1

/-! ## §2 The named facts -/

/-- **(C1) A geometric component of a smooth curve has infinitely many `ℚ̄`-points.**
Glue (STANDARD): a connected component `C` of `S_ℚ̄` is a smooth curve over `ℚ̄` (a nonempty
scheme of finite type over `ℚ̄` of dimension 1); its closed points are its `ℚ̄`-points
(Nullstellensatz) and there are infinitely many of them (a Jacobson scheme with finitely many
closed points is a finite discrete set, of dimension 0); a `ℚ̄`-point of `S_ℚ̄` over `ℚ̄` is
`bcPt y` for a unique `ℚ̄`-point `y` of `S` over `ℚ` (universal property of the pullback).
Properness is not needed. Not in Mathlib v4.35 (no dimension theory of smooth morphisms). -/
def GeomCompInfinite : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ y₀ : fieldPt Qbar ⟶ S, {y : fieldPt Qbar ⟶ S | geomComp y = geomComp y₀}.Infinite

/-- **(C2) Constant or onto on a geometric component** (Hartshorne, *Algebraic Geometry*,
Prop. II.6.8: a morphism from a complete nonsingular curve to a curve is constant or
surjective; UNVERIFIED numbering, cited so in mobius-glue). On the geometric component of `y₀`,
`σ` either takes the single value `σ(y₀)` at every `ℚ̄`-point, or takes every value of
`P¹(ℚ̄)`. Textbook leaf (published; applied to the connected component of `S_ℚ̄`, a complete
nonsingular curve over `ℚ̄`, with the dictionary between `ℚ̄`-points of `S` and closed points of
`S_ℚ̄`). Not in Mathlib v4.35 (Mathlib has `IsProper → IsClosedMap`, but no `P¹` as a scheme
and no dimension theory of curves). -/
def GeomCompConstOrOnto : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ (σ : ToP1 S.left) (y₀ : fieldPt Qbar ⟶ S),
      (∀ y : fieldPt Qbar ⟶ S, geomComp y = geomComp y₀ →
        σ.val (K := Qbar) y.left = σ.val (K := Qbar) y₀.left) ∨
      (∀ t : OnePoint Qbar, ∃ y : fieldPt Qbar ⟶ S, geomComp y = geomComp y₀ ∧
        σ.val (K := Qbar) y.left = t)

open Polynomial in
/-- **(C3) Factorization on one geometric component where `σ` is nonconstant.** If `σ` is
nonconstant on the geometric component `C` of `y₀` and `ρ` is constant on the `σ`-fibres in `C`
(on `ℚ̄`-points), then `ρ = [F : G] ∘ σ` on the `ℚ̄`-points of `C` with finite `σ`-value, for
coprime `F, G ∈ ℚ̄[t]`. Textbook (STANDARD): `σ|_C : C → P¹` is finite of some degree `n`, and
`ℚ̄(σ) ⊆ ℚ̄(σ, ρ) ⊆ ℚ̄(C)`; the normalization `D` of the image of `(σ, ρ)` is a smooth complete
curve with `D → P¹` finite of degree `[ℚ̄(σ, ρ) : ℚ̄(σ)]`, separable (char. 0), so its general
fibre has that many points (Hartshorne II.6.9 and IV.2.2, UNVERIFIED numbering); the fibre
condition makes the general fibre a single point, so `ℚ̄(σ, ρ) = ℚ̄(σ)`, `ρ = R(σ)` in `ℚ̄(C)`,
and two morphisms `C → P¹` agreeing generically agree (C reduced, `P¹` separated).
Classified as glue (a standard consequence of textbook theorems, not one printed theorem). Not
in Mathlib v4.35 (no degree of a finite morphism of curves, no fibre count). -/
def GeomCompRatFactor : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ (σ ρ : ToP1 S.left) (y₀ : fieldPt Qbar ⟶ S),
      (∃ y : fieldPt Qbar ⟶ S, geomComp y = geomComp y₀ ∧
        σ.val (K := Qbar) y.left ≠ σ.val (K := Qbar) y₀.left) →
      (∀ y₁ y₂ : fieldPt Qbar ⟶ S, geomComp y₁ = geomComp y₀ → geomComp y₂ = geomComp y₀ →
        σ.val (K := Qbar) y₁.left = σ.val (K := Qbar) y₂.left →
        ρ.val (K := Qbar) y₁.left = ρ.val (K := Qbar) y₂.left) →
      ∃ F G : Qbar[X], IsCoprime F G ∧ ∀ (y : fieldPt Qbar ⟶ S) (t : Qbar),
        geomComp y = geomComp y₀ → σ.val (K := Qbar) y.left = OnePoint.some t →
        ρ.val (K := Qbar) y.left = Mob.ratEval F G t

/-- **(C4) Finitely many geometric components.** Proved below (`geomCompFinite`). -/
def GeomCompFinite : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom →
    (Set.range (geomComp (S := S))).Finite

/-! ## §3 `GeomCompFinite`, from Mathlib -/

theorem geomCompFinite : GeomCompFinite := by
  intro S hP
  have : IsNoetherian (bcQbar S) := { }
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := bcQbar S)
  classical
  refine (hfin.image (fun Z => if h : Z.Nonempty then connectedComponent h.some else ∅)).subset ?_
  rintro _ ⟨y, rfl⟩
  set x := (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1 with hx
  have hne : (irreducibleComponent x).Nonempty := ⟨x, mem_irreducibleComponent⟩
  refine ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x, ?_⟩
  simp only [dite_eq_left hne]
  exact (connectedComponent_eq (irreducibleComponent_subset_connectedComponent hne.some_mem)).symm

/-! ## §4 Rational interpolation by a coprime pair -/

namespace Mob

open Polynomial

variable {K : Type} [Field K]

theorem isCoprime_X_sub_C_of_eval_one {F : K[X]} {a : K} (h : F.eval a = 1) :
    IsCoprime F (X - C a) := by
  have e := modByMonic_add_div F (X - C a)
  rw [modByMonic_X_sub_C_eq_C_eval, h, map_one] at e
  exact ⟨1, -(F /ₘ (X - C a)), by linear_combination (-1 : K[X]) * e⟩

/-- **Rational interpolation.** Any assignment of values in `P¹(K)` to finitely many nodes
`t ∈ T ⊆ K` is realised by `[F : G]` with `F, G` coprime. -/
theorem exists_interp (T : Finset K) (r : K → OnePoint K) :
    ∃ F G : K[X], IsCoprime F G ∧ ∀ t ∈ T, ratEval F G t = r t := by
  classical
  set Tinf := T.filter (fun t => r t = OnePoint.infty) with hTinf
  set G : K[X] := ∏ a ∈ Tinf, (X - C a) with hG
  have hGeval : ∀ t, G.eval t = ∏ a ∈ Tinf, (t - a) := by
    intro t; simp [hG, eval_prod]
  have hG0 : ∀ t ∈ Tinf, G.eval t = 0 := by
    intro t ht; rw [hGeval]; exact Finset.prod_eq_zero ht (sub_self t)
  have hGne : ∀ t, t ∉ Tinf → G.eval t ≠ 0 := by
    intro t ht; rw [hGeval, Finset.prod_ne_zero_iff]
    intro a ha e; exact ht (by rwa [sub_eq_zero.mp e])
  let w : K → K := fun t =>
    if h : ∃ v : K, r t = OnePoint.some v then h.choose * G.eval t else 1
  set F : K[X] := Lagrange.interpolate T id w with hF
  have hFeval : ∀ t ∈ T, F.eval t = w t := fun t ht =>
    Lagrange.eval_interpolate_at_node (v := id) w (Set.injOn_id _) ht
  refine ⟨F, G, ?_, ?_⟩
  · refine IsCoprime.prod_right fun a ha => isCoprime_X_sub_C_of_eval_one ?_
    have haT : a ∈ T := (Finset.mem_filter.mp ha).1
    have hra : r a = OnePoint.infty := (Finset.mem_filter.mp ha).2
    rw [hFeval a haT]
    have : ¬ ∃ v : K, r a = OnePoint.some v := by
      rintro ⟨v, hv⟩; rw [hra] at hv; exact OnePoint.infty_ne_coe v hv
    simp only [w, dite_eq_right this]
  · intro t ht
    by_cases hti : t ∈ Tinf
    · rw [(Finset.mem_filter.mp hti).2]; simp [ratEval, hG0 t hti]
    · have hrt : r t ≠ OnePoint.infty := fun e => hti (Finset.mem_filter.mpr ⟨ht, e⟩)
      have hex : ∃ v : K, r t = OnePoint.some v := by
        induction h : r t using OnePoint.rec with
        | infty => exact absurd h hrt
        | coe v => exact ⟨v, rfl⟩
      have hGt := hGne t hti
      rw [ratEval, ite_eq_right hGt, hFeval t ht]
      simp only [w, dite_eq_left hex]
      rw [mul_div_cancel_right₀ _ hGt]
      exact hex.choose_spec.symm

end Mob

/-! ## §5 The reductions -/

/-- **`CurveSurj` from (C1) and (C2).** -/
theorem curveSurj_of_comp (h1 : GeomCompInfinite) (h2 : GeomCompConstOrOnto) : CurveSurj := by
  intro S hP hS ⟨y₀⟩ σ hfin t
  rcases h2 S hP hS σ y₀ with hc | ho
  · exact absurd ((hfin y₀).subset fun y hy => hc y hy) (h1 S hP hS y₀)
  · obtain ⟨y, -, hy⟩ := ho t
    exact ⟨y, hy⟩

/-- **`CurveRatFactor` from (C2) and (C3)** (with (C4), proved, and rational interpolation). -/
theorem curveRatFactor_of_comp (h2 : GeomCompConstOrOnto) (h3 : GeomCompRatFactor) :
    CurveRatFactor := by
  classical
  intro S hP hS σ ρ hfib
  by_cases hnc : ∃ y₀ y : fieldPt Qbar ⟶ S, geomComp y = geomComp y₀ ∧
      σ.val (K := Qbar) y.left ≠ σ.val (K := Qbar) y₀.left
  · -- a component on which `σ` is nonconstant: it is onto, and carries the rational function
    obtain ⟨y₀, hne⟩ := hnc
    obtain ⟨F, G, hcop, hR⟩ := h3 S hP hS σ ρ y₀ hne (fun y₁ y₂ _ _ h => hfib y₁ y₂ h)
    refine ⟨F, G, hcop, fun y t hy => ?_⟩
    rcases h2 S hP hS σ y₀ with hc | ho
    · obtain ⟨y', hy', hne'⟩ := hne
      exact absurd (hc y' hy') hne'
    · obtain ⟨y', hy'c, hy't⟩ := ho (OnePoint.some t)
      rw [hfib y y' (hy.trans hy't.symm)]
      exact hR y' t hy'c hy't
  · -- `σ` constant on every component: finitely many values; interpolate
    push Not at hnc
    have hV : (Set.range fun y : fieldPt Qbar ⟶ S => σ.val (K := Qbar) y.left).Finite := by
      refine ((geomCompFinite S hP).image (fun c => if h : ∃ y : fieldPt Qbar ⟶ S,
        geomComp y = c then σ.val (K := Qbar) h.choose.left else OnePoint.infty)).subset ?_
      rintro _ ⟨y, rfl⟩
      have h : ∃ y' : fieldPt Qbar ⟶ S, geomComp y' = geomComp y := ⟨y, rfl⟩
      refine ⟨geomComp y, ⟨y, rfl⟩, ?_⟩
      simp only [dite_eq_left h]
      exact (hnc h.choose y h.choose_spec.symm).symm
    have hT : {t : Qbar | (OnePoint.some t) ∈
        Set.range fun y : fieldPt Qbar ⟶ S => σ.val (K := Qbar) y.left}.Finite :=
      hV.preimage (OnePoint.coe_injective.injOn)
    let r : Qbar → OnePoint Qbar := fun t =>
      if h : ∃ y : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y.left = OnePoint.some t then
        ρ.val (K := Qbar) h.choose.left else OnePoint.infty
    obtain ⟨F, G, hcop, hFG⟩ := Mob.exists_interp hT.toFinset r
    refine ⟨F, G, hcop, fun y t hy => ?_⟩
    have hmem : t ∈ hT.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact ⟨y, hy⟩
    have h : ∃ y : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y.left = OnePoint.some t := ⟨y, hy⟩
    rw [hFG t hmem]
    simp only [r, dite_eq_left h]
    exact hfib y h.choose (hy.trans h.choose_spec.symm)

/-- **Both curve facts from (C1), (C2), (C3).** -/
theorem curveFacts_of_comp (h1 : GeomCompInfinite) (h2 : GeomCompConstOrOnto)
    (h3 : GeomCompRatFactor) : CurveRatFactor ∧ CurveSurj :=
  ⟨curveRatFactor_of_comp h2 h3, curveSurj_of_comp h1 h2⟩

/-! ## §6 (C1) from "no isolated points" -/

/-- **(C1a) A scheme smooth of relative dimension 1 over a field has no isolated point.**
Glue (STANDARD): every point of `X` has an open neighbourhood étale over `𝔸¹_K`, so every
irreducible component of `X` has dimension 1 and every nonempty open of `X` is infinite; an open
point would be a nonempty finite open. Stated for any field `K` and any `X` (the use below is
`X = S_ℚ̄`, `K = ℚ̄`). Not in Mathlib v4.35 (no dimension theory of smooth morphisms). -/
def SmoothCurveNoIsolatedPoint : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    SmoothOfRelativeDimension 1 f → ∀ x : X, ¬ IsOpen ({x} : Set X)

/-- In a Noetherian space, connected components are open. -/
theorem isOpen_connectedComponent_of_noetherian {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] (x : α) : IsOpen (connectedComponent x) := by
  classical
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := α)
  have hc : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents α | ¬ Z ⊆ connectedComponent x}, Z := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hz
      exact ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z,
        fun h => hz (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨Z, ⟨hZ, hZC⟩, hzZ⟩ hzC
      apply hZC
      have : Z ⊆ connectedComponent z := hZ.1.isConnected.subset_connectedComponent hzZ
      rwa [← connectedComponent_eq hzC] at this
  rw [← isClosed_compl_iff, hc]
  exact (hfin.subset fun Z hZ => hZ.1).isClosed_biUnion fun Z hZ =>
    isClosed_of_mem_irreducibleComponents Z hZ.1

/-- In a Jacobson space, a nonempty open set with finitely many closed points contains an open
point. -/
theorem exists_isOpen_singleton_of_finite_closedPoints {α : Type*} [TopologicalSpace α]
    [JacobsonSpace α] {U : Set α} (hU : IsOpen U) (hne : U.Nonempty)
    (hfin : (U ∩ closedPoints α).Finite) : ∃ z, IsOpen ({z} : Set α) := by
  classical
  set F := U ∩ closedPoints α with hF
  have hclosed : ∀ G ⊆ F, IsClosed G := by
    intro G hG
    rw [← G.biUnion_of_singleton]
    exact (hfin.subset hG).isClosed_biUnion fun w hw => mem_closedPoints_iff.mp (hG hw).2
  have hFc : IsClosed F := hclosed F le_rfl
  -- `U ⊆ F`: otherwise `U \ F` is a nonempty open with no closed point
  have hUF : U ⊆ F := by
    by_contra hsub
    obtain ⟨z, hzU, hzF⟩ := Set.not_subset.mp hsub
    obtain ⟨w, ⟨hwU, hwF⟩, hwc⟩ := nonempty_inter_closedPoints (Z := U ∩ Fᶜ)
      ⟨z, hzU, hzF⟩ (hU.inter hFc.isOpen_compl).isLocallyClosed
    exact hwF ⟨hwU, hwc⟩
  obtain ⟨z, hz⟩ := hne
  refine ⟨z, ?_⟩
  have hrest : IsClosed (F \ {z}) := hclosed _ Set.sdiff_subset
  have : ({z} : Set α) = U ∩ (F \ {z})ᶜ := by
    ext w
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff,
      not_and, not_not]
    constructor
    · rintro rfl; exact ⟨hz, fun _ => rfl⟩
    · rintro ⟨hwU, h⟩; exact h (hUF hwU)
  rw [this]; exact hU.inter hrest.isOpen_compl

/-- **(C1) from (C1a).** -/
theorem geomCompInfinite_of (h : SmoothCurveNoIsolatedPoint) : GeomCompInfinite := by
  intro S hP hS y₀
  classical
  let f : bcQbar S ⟶ Spec (CommRingCat.of Qbar) :=
    pullback.snd S.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))
  have : IsNoetherian (bcQbar S) := { }
  have : LocallyOfFiniteType f := by
    show LocallyOfFiniteType (pullback.snd _ _); infer_instance
  have hsm : SmoothOfRelativeDimension 1 f := by
    show SmoothOfRelativeDimension 1 (pullback.snd _ _); infer_instance
  have : JacobsonSpace (bcQbar S) := LocallyOfFiniteType.jacobsonSpace f
  set x₀ := (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y₀)).1 with hx₀
  -- the closed points of the component of `x₀` are infinitely many
  have hCinf : (connectedComponent x₀ ∩ closedPoints (bcQbar S)).Infinite := by
    intro hfin
    obtain ⟨z, hz⟩ := exists_isOpen_singleton_of_finite_closedPoints
      (isOpen_connectedComponent_of_noetherian x₀) ⟨x₀, mem_connectedComponent⟩ hfin
    exact h Qbar (bcQbar S) f hsm z hz
  -- each of them comes from a `ℚ̄`-point of `S` in the component
  intro hfin
  apply hCinf
  refine (hfin.image fun y => (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1).subset ?_
  rintro x ⟨hxC, hxc⟩
  let p : Spec (CommRingCat.of Qbar) ⟶ bcQbar S := pointOfClosedPoint f x hxc
  have hp : p ≫ f = 𝟙 _ := pointOfClosedPoint_comp f x hxc
  let y : fieldPt Qbar ⟶ S := Over.homMk (p ≫ pullback.fst _ _) (by
    change (p ≫ pullback.fst _ _) ≫ S.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (p ≫ f) ≫ _ = _
    rw [hp, Category.id_comp])
  have hy : bcPt y = p := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans hp.symm
  have hpt : (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1 = x := by
    rw [hy]; exact pointOfClosedPoint_apply f x hxc _
  refine ⟨y, ?_, hpt⟩
  show geomComp y = geomComp y₀
  unfold geomComp
  rw [hpt, ← hx₀]
  exact (connectedComponent_eq hxC).symm

/-- **Both curve facts from (C1a), (C2), (C3).** -/
theorem curveFacts_of_named (h1 : SmoothCurveNoIsolatedPoint) (h2 : GeomCompConstOrOnto)
    (h3 : GeomCompRatFactor) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_comp (geomCompInfinite_of h1) h2 h3

/-! ## §7 C2 and C3 over an algebraically closed field (Hartshorne's setting)

The leaves C2 and C3 are restated for a proper smooth curve `X` over an arbitrary algebraically
closed field `K`, its `K`-points (sections `p : Spec K → X` of the structure map) and a connected
component of `X`. `GeomCompConstOrOnto` and `GeomCompRatFactor` follow by base change to `ℚ̄`. -/

/-- The point of `X` at which a field point `p : Spec K → X` sits. -/
abbrev ptOf {K : Type} [Field K] {X : Scheme.{0}} (p : Spec (CommRingCat.of K) ⟶ X) : X :=
  (Scheme.SpecToEquivOfField K X p).1

/-- **(C2K) Constant or onto on a connected component** (Hartshorne, *Algebraic Geometry*,
Prop. II.6.8, UNVERIFIED numbering: a morphism from a complete nonsingular curve over an
algebraically closed field to a curve is constant or surjective; here applied to a connected
component of `X`, a complete nonsingular irreducible curve, and the target `P¹`, whose closed
points are its `K`-points). Textbook leaf. -/
def ConstOrOntoAlgClosed : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → σ.val p = σ.val p₀) ∨
      (∀ t : OnePoint K, ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p = t)

open Polynomial in
/-- **(C3K) Factorization on a connected component where `σ` is nonconstant**, over an
algebraically closed field of characteristic 0 (in characteristic `p` the Frobenius
`σ = ρ^p` is a counterexample). Glue (a standard consequence of textbook results, see
`docs/research/curve-facts.md` §3). -/
def RatFactorAlgClosed : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p ≠ σ.val p₀) →
      (∀ p₁ p₂ : Spec (CommRingCat.of K) ⟶ X, p₁ ≫ f = 𝟙 _ → p₂ ≫ f = 𝟙 _ →
        connectedComponent (ptOf p₁) = connectedComponent (ptOf p₀) →
        connectedComponent (ptOf p₂) = connectedComponent (ptOf p₀) →
        σ.val p₁ = σ.val p₂ → ρ.val p₁ = ρ.val p₂) →
      ∃ F G : K[X], IsCoprime F G ∧ ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t : K,
        σ.val p = OnePoint.some t → ρ.val p = Mob.ratEval F G t

section Dictionary

variable {S : Over (Spec (CommRingCat.of ℚ))}

/-- The structure map `S_ℚ̄ → Spec ℚ̄`. -/
abbrev bcSnd (S : Over (Spec (CommRingCat.of ℚ))) : bcQbar S ⟶ Spec (CommRingCat.of Qbar) :=
  pullback.snd S.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))

theorem bcPt_snd (y : fieldPt Qbar ⟶ S) : bcPt y ≫ bcSnd S = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The `ℚ̄`-point of `S` over `ℚ` underlying a section of `S_ℚ̄ → Spec ℚ̄`. -/
def ptOfSection (p : Spec (CommRingCat.of Qbar) ⟶ bcQbar S) (hp : p ≫ bcSnd S = 𝟙 _) :
    fieldPt Qbar ⟶ S :=
  Over.homMk (p ≫ pullback.fst _ _) (by
    change (p ≫ pullback.fst _ _) ≫ S.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (p ≫ bcSnd S) ≫ _ = _
    rw [hp, Category.id_comp])

theorem bcPt_ptOfSection (p : Spec (CommRingCat.of Qbar) ⟶ bcQbar S) (hp : p ≫ bcSnd S = 𝟙 _) :
    bcPt (ptOfSection p hp) = p := by
  apply pullback.hom_ext
  · exact pullback.lift_fst _ _ _
  · exact (pullback.lift_snd _ _ _).trans hp.symm

/-- `σ(y) = (σ ∘ pr₁)(bcPt y)`. -/
theorem val_bcPt (σ : ToP1 S.left) (y : fieldPt Qbar ⟶ S) :
    (σ.comp (pullback.fst _ _)).val (bcPt y) = σ.val (K := Qbar) y.left := by
  rw [ToP1.val_comp_right]
  exact congrArg _ (pullback.lift_fst _ _ _)

end Dictionary

/-- **C2 from C2K.** -/
theorem geomCompConstOrOnto_of (h : ConstOrOntoAlgClosed) : GeomCompConstOrOnto := by
  intro S hP hS σ y₀
  have hPf : IsProper (bcSnd S) := inferInstance
  have hSf : SmoothOfRelativeDimension 1 (bcSnd S) := inferInstance
  rcases h Qbar (bcQbar S) (bcSnd S) hPf hSf (σ.comp (pullback.fst _ _)) (bcPt y₀)
    (bcPt_snd y₀) with hc | ho
  · left
    intro y hy
    rw [← val_bcPt, ← val_bcPt]
    exact hc (bcPt y) (bcPt_snd y) hy
  · right
    intro t
    obtain ⟨p, hp, hcc, hv⟩ := ho t
    refine ⟨ptOfSection p hp, ?_, ?_⟩
    · show connectedComponent (ptOf (bcPt (ptOfSection p hp))) = _
      rw [bcPt_ptOfSection]; exact hcc
    · rw [← val_bcPt, bcPt_ptOfSection]; exact hv

/-- **C3 from C3K.** -/
theorem geomCompRatFactor_of (h : RatFactorAlgClosed) : GeomCompRatFactor := by
  intro S hP hS σ ρ y₀ hne hfib
  have hPf : IsProper (bcSnd S) := inferInstance
  have hSf : SmoothOfRelativeDimension 1 (bcSnd S) := inferInstance
  have hcc : ∀ (p : Spec (CommRingCat.of Qbar) ⟶ bcQbar S) (hp : p ≫ bcSnd S = 𝟙 _),
      geomComp (ptOfSection p hp) = connectedComponent (ptOf p) := by
    intro p hp
    show connectedComponent (ptOf (bcPt (ptOfSection p hp))) = _
    rw [bcPt_ptOfSection]
  obtain ⟨F, G, hcop, hR⟩ := h Qbar (bcQbar S) (bcSnd S) hPf hSf (σ.comp (pullback.fst _ _))
    (ρ.comp (pullback.fst _ _)) (bcPt y₀) (bcPt_snd y₀) (by
      obtain ⟨y, hy, hv⟩ := hne
      refine ⟨bcPt y, bcPt_snd y, hy, ?_⟩
      rw [val_bcPt, val_bcPt]; exact hv) (by
      intro p₁ p₂ hp₁ hp₂ h₁ h₂ hv
      have e₁ := val_bcPt σ (ptOfSection p₁ hp₁)
      have e₂ := val_bcPt σ (ptOfSection p₂ hp₂)
      have f₁ := val_bcPt ρ (ptOfSection p₁ hp₁)
      have f₂ := val_bcPt ρ (ptOfSection p₂ hp₂)
      rw [bcPt_ptOfSection] at e₁ e₂ f₁ f₂
      rw [f₁, f₂]
      refine hfib _ _ ((hcc p₁ hp₁).trans h₁) ((hcc p₂ hp₂).trans h₂) ?_
      rw [← e₁, ← e₂]; exact hv)
  refine ⟨F, G, hcop, fun y t hy ht => ?_⟩
  rw [← val_bcPt] at ht ⊢
  exact hR (bcPt y) (bcPt_snd y) hy t ht

/-- **Both curve facts from C1a, C2K, C3K** (the leaves in Hartshorne's setting). -/
theorem curveFacts_of_algClosed (h1 : SmoothCurveNoIsolatedPoint) (h2 : ConstOrOntoAlgClosed)
    (h3 : RatFactorAlgClosed) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_named h1 (geomCompConstOrOnto_of h2) (geomCompRatFactor_of h3)

/-! ## §8 C1a from the dimension of local rings at closed points -/

/-- **(C1b) Local rings of a smooth curve at closed points have dimension 1.** If `X → Spec K`
is smooth of relative dimension 1 over a field `K` and `x` is a closed point, then
`dim 𝒪_{X,x} = 1` (STANDARD: smooth of relative dimension `n` over a field means `dim_x X = n`
at every point, and at a closed point of a scheme locally of finite type over a field
`dim 𝒪_{X,x} = dim_x X`; e.g. Stacks, *Morphisms*, smooth morphisms and dimension of fibres,
UNVERIFIED tags). Glue (dimension theory), not in Mathlib v4.35; Mathlib has
`ringKrullDim_stalk_eq_coheight` (Stacks 02IZ), used below. -/
def SmoothStalkDimOne : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    SmoothOfRelativeDimension 1 f → ∀ x : X, IsClosed ({x} : Set X) →
      ringKrullDim (X.presheaf.stalk x) = 1

/-- **C1a from C1b.** An open point is closed (Jacobson) and has no proper generalization, so its
local ring has dimension `coheight x = 0`. -/
theorem smoothCurveNoIsolatedPoint_of (h : SmoothStalkDimOne) : SmoothCurveNoIsolatedPoint := by
  intro K _ X f hf x hx
  have : Smooth f := hf.smooth
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hc : IsClosed ({x} : Set X) := isClosed_singleton_of_isLocallyClosed_singleton hx.isLocallyClosed
  have hd := h K X f hf x hc
  rw [ringKrullDim_stalk_eq_coheight] at hd
  have hmax : IsMax x := by
    intro y hxy
    have hyx : y ⤳ x := hxy
    have : y ∈ ({x} : Set X) := hyx.mem_open hx rfl
    rw [Set.mem_singleton_iff.mp this]
  rw [Order.coheight_eq_zero.mpr hmax] at hd
  exact absurd hd (by decide)

/-- **Both curve facts from C1b, C2K, C3K.** -/
theorem curveFacts_of_leaves (h1 : SmoothStalkDimOne) (h2 : ConstOrOntoAlgClosed)
    (h3 : RatFactorAlgClosed) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_algClosed (smoothCurveNoIsolatedPoint_of h1) h2 h3

/-! # curve-glue additions (task curve-glue, 2026-11-13)

Everything above is `scratch/curve-facts/CurveFacts.lean` verbatim (its `#print axioms` lines
dropped). Below: `scratch/curve-glue/C2K.lean` §1-§4 (C2K from the leaf `GlobalFunctionsConst`)
and `scratch/curve-glue/C3K.lean` §1-§2 (C3K from the glue `ImagePlaneCurve`, or from C2K and
`ImagePlaneCurveClosed`, and Lean-proved algebra), then the composites. -/

open Opposite TopologicalSpace

/-! ## §1 Values of sections at `K`-points -/

section Ev

variable {K : Type} [Field K] {X : Scheme.{0}}

/-- Restriction of sections along `O' ≤ O`, as a ring hom. -/
abbrev res {O O' : X.Opens} (h : O' ≤ O) : Γ(X, O) →+* Γ(X, O') :=
  (X.presheaf.map (homOfLE h).op).hom

theorem res_res {O O' O'' : X.Opens} (h : O' ≤ O) (h' : O'' ≤ O') (s : Γ(X, O)) :
    res h' (res h s) = res (h'.trans h) s := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The value `s(p) ∈ K` of a section `s ∈ Γ(X, O)` at a field point `p` whose point lies in `O`
(the image of `s(x) ∈ κ(x)` under the embedding `κ(x) → K` of `p`; this is how `ToP1.val`
evaluates). -/
def ev (p : Spec (CommRingCat.of K) ⟶ X) {O : X.Opens} (hx : ptOf p ∈ O) : Γ(X, O) →+* K :=
  (X.evaluation O (ptOf p) hx ≫ (Scheme.SpecToEquivOfField K X p).2).hom

theorem ev_res (p : Spec (CommRingCat.of K) ⟶ X) {O O' : X.Opens} (h : O' ≤ O)
    (hx : ptOf p ∈ O') (s : Γ(X, O)) : ev p hx (res h s) = ev p (h hx) s := by
  simp only [ev, res, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  congr 1
  simp only [Scheme.evaluation, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← ConcreteCategory.comp_apply (X.presheaf.map _), TopCat.Presheaf.germ_res]

theorem ev_eq_zero_iff (p : Spec (CommRingCat.of K) ⟶ X) {O : X.Opens} (hx : ptOf p ∈ O)
    (s : Γ(X, O)) : ev p hx s = 0 ↔ ptOf p ∉ X.basicOpen s := by
  rw [← X.evaluation_eq_zero_iff_notMem_basicOpen (ptOf p) hx s]
  simp only [ev, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  exact map_eq_zero_iff _ (Scheme.SpecToEquivOfField K X p).2.hom.injective

theorem ev_top (p : Spec (CommRingCat.of K) ⟶ X) (s : Γ(X, ⊤)) :
    ev p (show ptOf p ∈ (⊤ : X.Opens) from trivial) s =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom (p.appTop s) := by
  have e := Scheme.germ_stalkClosedPointTo p ⊤ trivial
  have e' := congrArg (fun φ => φ.hom s) e
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e'
  simp only [ev, Scheme.evaluation, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  change (X.residue _ ≫ X.descResidueField (Scheme.stalkClosedPointTo p)).hom
    ((X.presheaf.germ ⊤ _ trivial).hom s) = _
  rw [Scheme.residue_descResidueField, e']
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, eqToHom_op, eqToHom_map,
    Scheme.Hom.appTop]
  rfl

/-- The constant section `a ∈ K` on `O`, through the structure morphism `f : X → Spec K`. -/
def cst (f : X ⟶ Spec (CommRingCat.of K)) (O : X.Opens) (a : K) : Γ(X, O) :=
  res le_top (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))

theorem ev_cst (f : X ⟶ Spec (CommRingCat.of K)) (p : Spec (CommRingCat.of K) ⟶ X)
    (hp : p ≫ f = 𝟙 _) {O : X.Opens} (hx : ptOf p ∈ O) (a : K) : ev p hx (cst f O a) = a := by
  rw [cst, ev_res, ev_top]
  have h1 : p.appTop (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv a := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hp, Scheme.Hom.id_appTop]; rfl
  rw [h1]; simp

end Ev

/-! ## §2 Closed points are `K`-points; units by values -/

section Units

variable {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))
  [LocallyOfFiniteType f] [JacobsonSpace X]

theorem exists_point_of_isLocallyClosed {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧ ptOf p ∈ Z := by
  obtain ⟨y, hyZ, hyc⟩ := nonempty_inter_closedPoints hne hZ
  have hy : IsClosed ({y} : Set X) := mem_closedPoints_iff.mp hyc
  refine ⟨pointOfClosedPoint f y hy, pointOfClosedPoint_comp f y hy, ?_⟩
  have e : ptOf (pointOfClosedPoint f y hy) = y := pointOfClosedPoint_apply f y hy _
  rw [e]; exact hyZ

end Units

section Main

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem val_of_mem (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (h : ptOf p ∈ σ.U) :
    σ.val p = OnePoint.some (ev p h σ.f) := by
  unfold ToP1.val
  split_ifs with h'
  · rfl
  · exact absurd h h'

theorem val_of_not_mem (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (h : ptOf p ∉ σ.U) :
    σ.val p = OnePoint.infty := by
  unfold ToP1.val
  split_ifs with h'
  · exact absurd h' h
  · rfl

theorem ev_f_mul_g (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (hU : ptOf p ∈ σ.U)
    (hV : ptOf p ∈ σ.V) : ev p hU σ.f * ev p hV σ.g = 1 := by
  have e := congrArg (ev p (show ptOf p ∈ σ.U ⊓ σ.V from ⟨hU, hV⟩)) σ.inv
  rw [map_mul, map_one] at e
  rw [← ev_res p (inf_le_left : σ.U ⊓ σ.V ≤ σ.U) ⟨hU, hV⟩,
    ← ev_res p (inf_le_right : σ.U ⊓ σ.V ≤ σ.V) ⟨hU, hV⟩]
  exact e

theorem ev_g_eq_zero (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (hV : ptOf p ∈ σ.V)
    (hU : ptOf p ∉ σ.U) : ev p hV σ.g = 0 := by
  rw [ev_eq_zero_iff, σ.basicOpen_g]
  exact fun h => hU h.1

theorem mem_V_of_not_mem_U (σ : ToP1 X) {x : X} (hU : x ∉ σ.U) : x ∈ σ.V := by
  have hx : x ∈ (σ.U ⊔ σ.V : X.Opens) := by rw [σ.cover]; trivial
  rcases hx with h | h
  · exact absurd h hU
  · exact h

end Main

/-! ## §4 C2K from the leaf (L) -/

/-! ## §1 Algebra: an irreducible `P(x, y)` of `y`-degree `≥ 2` has a fibre with two roots -/

namespace Alg

open Polynomial

variable {K : Type} [Field K]

/-- `P(t, u)` for `P ∈ K[x][y]` (outer variable `y`, coefficients in `K[x]`). -/
def evalXY (t u : K) (P : K[X][X]) : K := (P.map (evalRingHom t)).eval u

/-- **Two roots in some fibre** (Lean-proved algebra; char. 0 is essential). If `P ∈ K[x][y]` is
irreducible of `y`-degree `d ≥ 2`, `K` algebraically closed of characteristic 0, then for some
`t ∈ K` the polynomial `P(t, y)` has two distinct roots. Proof: `P` is primitive and stays
irreducible over `K(x)` (Gauss), hence separable (char. 0), so the resultant
`r = Res_y(P, ∂P/∂y) ∈ K[x]` is nonzero; at any `t` with `r(t) · lc(P)(t) ≠ 0`, `P(t, y)` has
degree `d` and is separable, so it has `d ≥ 2` distinct roots. -/
theorem exists_two_roots [IsAlgClosed K] [CharZero K] {P : K[X][X]} (hirr : Irreducible P)
    (h2 : 2 ≤ P.natDegree) :
    ∃ t u u' : K, u ≠ u' ∧ evalXY t u P = 0 ∧ evalXY t u' P = 0 := by
  classical
  have hd0 : P.natDegree ≠ 0 := by omega
  have hP0 : P ≠ 0 := fun h => by simp [h] at h2
  set φ := algebraMap K[X] (FractionRing K[X]) with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have hirr' : Irreducible (P.map φ) :=
    ((hirr.isPrimitive hd0).irreducible_iff_irreducible_map_fraction_map).1 hirr
  have hsep : (P.map φ).Separable := hirr'.separable
  have hres := resultant_ne_zero _ _ hsep
  rw [derivative_map, natDegree_map_eq_of_injective hinj,
    natDegree_map_eq_of_injective hinj, resultant_map_map] at hres
  set r := resultant P (derivative P) P.natDegree (derivative P).natDegree with hr
  have hr0 : r ≠ 0 := fun h => hres (by rw [h, map_zero])
  have hlc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  -- a good fibre
  obtain ⟨t, ht⟩ : ∃ t : K, (r * P.leadingCoeff).eval t ≠ 0 := by
    by_contra! h
    exact mul_ne_zero hr0 hlc0 (Polynomial.funext fun t => by rw [h t, eval_zero])
  rw [eval_mul] at ht
  have hrt : r.eval t ≠ 0 := left_ne_zero_of_mul ht
  have hlt : P.leadingCoeff.eval t ≠ 0 := right_ne_zero_of_mul ht
  set ψ := evalRingHom t with hψ
  set Pt := P.map ψ with hPt
  have hdeg : Pt.natDegree = P.natDegree := natDegree_map_of_leadingCoeff_ne_zero ψ hlt
  have hdeg' : ((derivative P).map ψ).natDegree = (derivative P).natDegree := by
    refine natDegree_map_of_leadingCoeff_ne_zero ψ ?_
    rw [leadingCoeff_derivative, map_mul, map_natCast]
    exact mul_ne_zero hlt (by exact_mod_cast hd0)
  have hPt0 : Pt ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; omega
  have hrest : resultant Pt (derivative Pt) ≠ 0 := by
    rw [derivative_map, hdeg, hdeg', resultant_map_map]
    exact hrt
  have hsep' : Pt.Separable := by
    have h := mt resultant_eq_zero_iff.2 hrest
    push Not at h
    exact h (Or.inl hPt0)
  have hcard : Pt.roots.card = P.natDegree := by
    rw [← (IsAlgClosed.splits Pt).natDegree_eq_card_roots, hdeg]
  have hnd : Pt.roots.Nodup := nodup_roots hsep'
  have h1 : 1 < Pt.roots.toFinset.card := by
    rw [Multiset.toFinset_card_of_nodup hnd, hcard]; omega
  obtain ⟨u, hu, u', hu', hne⟩ := Finset.one_lt_card.1 h1
  exact ⟨t, u, u', hne, (mem_roots hPt0).1 (Multiset.mem_toFinset.1 hu),
    (mem_roots hPt0).1 (Multiset.mem_toFinset.1 hu')⟩

/-- An irreducible `P ∈ K[x][y]` of `y`-degree 1 has coprime coefficients. -/
theorem isCoprime_coeff_of_irreducible {P : K[X][X]} (hirr : Irreducible P)
    (h1 : P.natDegree = 1) : IsCoprime (P.coeff 1) (P.coeff 0) := by
  have hP : P = C (P.coeff 1) * X + C (P.coeff 0) := eq_X_add_C_of_natDegree_le_one h1.le
  refine IsRelPrime.isCoprime fun d hdA hdB => ?_
  obtain ⟨a, ha⟩ := hdA
  obtain ⟨b, hb⟩ := hdB
  have hfac : P = C d * (C a * X + C b) := by
    rw [hP, ha, hb, C_mul, C_mul]; ring
  rcases hirr.isUnit_or_isUnit hfac with h | h
  · exact isUnit_C.mp h
  · exfalso
    have h0 := natDegree_eq_zero_of_isUnit h
    have : P.natDegree ≤ 0 := by
      rw [hfac]; exact (natDegree_C_mul_le _ _).trans h0.le
    omega

theorem evalXY_mul (t u : K) (P Q : K[X][X]) :
    evalXY t u (P * Q) = evalXY t u P * evalXY t u Q := by
  simp [evalXY]

/-- An irreducible `P ∈ K[x][y]` of positive `y`-degree does not vanish identically on a vertical
line: `P(t, y) ≠ 0` for every `t` (else `x − t` divides the content). -/
theorem map_eval_ne_zero {P : K[X][X]} (hirr : Irreducible P) (hdeg : 1 ≤ P.natDegree) (t : K) :
    P.map (evalRingHom t) ≠ 0 := by
  intro h0
  have hprim := hirr.isPrimitive (by omega)
  have hdvd : C (X - C t) ∣ P := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [dvd_iff_isRoot]
    have := congrArg (fun q => q.coeff i) h0
    simpa [coeff_map] using this
  exact not_isUnit_X_sub_C t ((isPrimitive_iff_isUnit_of_C_dvd.mp hprim) _ hdvd)

/-- **Bezout-type finiteness** (Lean-proved): if `P ∈ K[x][y]` is irreducible of positive
`y`-degree and does not divide `Q`, then `P = Q = 0` has finitely many solutions in `K²`
(`Res_y(P, Q) ∈ K[x]` is nonzero, and each fibre of `P = 0` is finite). -/
theorem finite_common_zeros {P Q : K[X][X]} (hirr : Irreducible P) (hdeg : 1 ≤ P.natDegree)
    (hPQ : ¬ P ∣ Q) :
    {z : K × K | evalXY z.1 z.2 P = 0 ∧ evalXY z.1 z.2 Q = 0}.Finite := by
  classical
  have hd0 : P.natDegree ≠ 0 := by omega
  set φ := algebraMap K[X] (FractionRing K[X]) with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have hprim := hirr.isPrimitive hd0
  have hirr' : Irreducible (P.map φ) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map).1 hirr
  have hndvd : ¬ P.map φ ∣ Q.map φ := fun h =>
    hPQ ((hprim.dvd_iff_fraction_map_dvd_fraction_map (FractionRing K[X])).2 h)
  have hcop : IsCoprime (P.map φ) (Q.map φ) := hirr'.coprime_iff_not_dvd.2 hndvd
  have hres := resultant_ne_zero _ _ hcop
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj,
    resultant_map_map] at hres
  set r := resultant P Q P.natDegree Q.natDegree with hr
  have hr0 : r ≠ 0 := fun h => hres (by rw [h, map_zero])
  obtain ⟨a, b, -, -, hab⟩ := exists_mul_add_mul_eq_C_resultant P Q le_rfl le_rfl (Or.inl hd0)
  refine ((r.roots.toFinset.finite_toSet).biUnion fun t _ =>
    ((P.map (evalRingHom t)).roots.toFinset.finite_toSet.image fun u => (t, u))).subset ?_
  rintro ⟨t, u⟩ ⟨h1, h2⟩
  have hrt : r.eval t = 0 := by
    have e := congrArg (evalXY t u) hab
    rw [← hr] at e
    simp only [evalXY, Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul,
      Polynomial.map_C, eval_C, coe_evalRingHom] at e h1 h2
    rw [h1, h2] at e
    simpa using e.symm
  simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Multiset.mem_toFinset]
  refine ⟨t, (mem_roots hr0).2 hrt, u, (mem_roots (map_eval_ne_zero hirr hdeg t)).2 h1, rfl⟩

end Alg

/-! ## §2 The geometric glue (G1) and the reduction -/

open Polynomial in
/-- **(G1) The image of a connected component under `(σ, ρ)` is a plane curve.** Setting of C3K
(without characteristic 0): `X → Spec K` proper and smooth of relative dimension 1, `K`
algebraically closed, `σ, ρ : X → P¹`, `W` the connected component of the `K`-point `p₀`, and
`σ` nonconstant on the `K`-points of `W`. Then either `ρ ≡ ∞` on the `K`-points of `W`, or there
is an irreducible `P ∈ K[x][y]` of `y`-degree `≥ 1` such that
(a) `P(σ(p), ρ(p)) = 0` at every `K`-point `p` of `W` with both values finite;
(b) every `(t, u) ∈ K²` with `P(t, u) = 0` is `(σ(p), ρ(p))` for a `K`-point `p` of `W`;
(c) a `K`-point `p` of `W` with `σ(p) = t` finite and `ρ(p) = ∞` has `lc_y(P)(t) = 0`.

Why true (STANDARD; references UNVERIFIED): `W` is a complete nonsingular irreducible curve
(smooth ⇒ normal, so connected components are irreducible), so its image `D` under
`(σ, ρ) : W → P¹ × P¹` is closed (properness) and irreducible, and not a point (σ nonconstant).
If `ρ ≢ ∞`, `D ∩ 𝔸²` is a nonempty open, hence dense, subset of `D`, an irreducible closed curve
in `𝔸²`, so `D ∩ 𝔸² = V(P)` with `P` irreducible (`K[x, y]` is a UFD and height-one primes are
principal: Hartshorne I.1.12 / Ex. I.1.1-type facts); `P ∉ K[x]` because `σ` is nonconstant on
the dense set `W ∩ (σ, ρ)⁻¹(𝔸²)`. (a) is `D ∩ 𝔸² ⊆ V(P)`. (b): `V(P) ⊆ D`, and every closed point
of `D` is the image of a closed point of `W` (the fibre is a nonempty closed subset of a scheme of
finite type over `K`), i.e. of a `K`-point (Nullstellensatz). (c): `D` lies in the closure of
`V(P)` in `𝔸¹ × P¹`, which lies in `V(P^h)`, `P^h(x; y₀ : y₁) = Σ a_i(x) y₁^i y₀^{d−i}`, whose
points over `y = ∞` (`y₀ = 0`) have `a_d(x) = 0`.

Classified as **glue** (several textbook facts: image of a proper curve, plane curves as
hypersurfaces, closure and homogenization). Characteristic 0 is not used here; it enters only
through the Lean-proved `Alg.exists_two_roots`. Not in Mathlib v4.35 (no `P¹ × P¹`, no plane
curves). -/
def ImagePlaneCurve : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p ≠ σ.val p₀) →
      (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) →
        ρ.val p = OnePoint.infty) ∨
      ∃ P : K[X][X], Irreducible P ∧ 1 ≤ P.natDegree ∧
        (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t u : K,
          σ.val p = OnePoint.some t → ρ.val p = OnePoint.some u → Alg.evalXY t u P = 0) ∧
        (∀ t u : K, Alg.evalXY t u P = 0 → ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧
          σ.val p = OnePoint.some t ∧ ρ.val p = OnePoint.some u) ∧
        (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t : K,
          σ.val p = OnePoint.some t → ρ.val p = OnePoint.infty → P.leadingCoeff.eval t = 0)

open Polynomial in
/-- **C3K from (G1) and the Lean-proved algebra.** The fibre condition and
`Alg.exists_two_roots` force `deg_y P = 1`, `P = A y + B` with `A, B` coprime, and then
`ρ = [−B : A] ∘ σ` at every `K`-point of `W` with finite `σ`-value (clause (c) for `ρ = ∞`). -/
theorem ratFactorAlgClosed_of (hG : ImagePlaneCurve) : RatFactorAlgClosed := by
  intro K _ _ _ X f hP hS σ ρ p₀ hp₀ hne hfib
  rcases hG K X f hP hS σ ρ p₀ hp₀ hne with hinf | ⟨P, hirr, hdeg, ha, hb, hc⟩
  · refine ⟨1, 0, isCoprime_one_left, fun p hp hpc t _ => ?_⟩
    rw [hinf p hp hpc]
    simp [Mob.ratEval]
  · have hd1 : P.natDegree = 1 := by
      by_contra h
      obtain ⟨t, u, u', hne', hu, hu'⟩ := Alg.exists_two_roots hirr (by omega)
      obtain ⟨p, hp, hpc, hpt, hpu⟩ := hb t u hu
      obtain ⟨p', hp', hpc', hpt', hpu'⟩ := hb t u' hu'
      have e := hfib p p' hp hp' hpc hpc' (hpt.trans hpt'.symm)
      rw [hpu, hpu'] at e
      exact hne' (OnePoint.coe_injective e)
    have hcop := Alg.isCoprime_coeff_of_irreducible hirr hd1
    have hPe : P = C (P.coeff 1) * Polynomial.X + C (P.coeff 0) :=
      eq_X_add_C_of_natDegree_le_one hd1.le
    have hev : ∀ t u : K, Alg.evalXY t u P = (P.coeff 1).eval t * u + (P.coeff 0).eval t := by
      intro t u
      rw [Alg.evalXY]
      conv_lhs => rw [hPe]
      simp
    have hlc : P.leadingCoeff = P.coeff 1 := by rw [leadingCoeff, hd1]
    have hnotboth : ∀ t : K, (P.coeff 1).eval t = 0 → (P.coeff 0).eval t ≠ 0 := by
      intro t h1 h0
      obtain ⟨a, b, hab⟩ := hcop
      have e := congrArg (eval t) hab
      simp [eval_add, eval_mul, h1, h0] at e
    refine ⟨-(P.coeff 0), P.coeff 1, hcop.symm.neg_left, fun p hp hpc t ht => ?_⟩
    induction hρ : ρ.val p using OnePoint.rec with
    | infty =>
      have e := hc p hp hpc t ht hρ
      rw [hlc] at e
      unfold Mob.ratEval
      split_ifs
      rfl
    | coe u =>
      have e := ha p hp hpc t u ht hρ
      rw [hev] at e
      by_cases hA : (P.coeff 1).eval t = 0
      · exfalso
        rw [hA, zero_mul, zero_add] at e
        exact hnotboth t hA e
      · unfold Mob.ratEval
        split_ifs
        rw [eval_neg]
        refine congrArg _ ?_
        field_simp
        linear_combination e

open Polynomial in
/-- **(G1') The affine image is Zariski closed, and `P` cuts out the image curve.** As
`ImagePlaneCurve`, with clause (b) ("every point of `V(P)` is hit") replaced by (b''): the set of
pairs `(σ(p), ρ(p)) ∈ K²` over the `K`-points `p` of `W` with both values finite is Zariski
closed, i.e. the common zero set of some family `S ⊆ K[x][y]`.

Why true (STANDARD): the image `D` of `W` under `(σ, ρ)` is closed in `P¹ × P¹` (properness), so
`D ∩ 𝔸²` is closed in `𝔸²`, and its closed points are exactly the images of `K`-points of `W`
(fibres of `W → D` over closed points contain closed points, which are `K`-points). Clauses (a)
and (c) are those of `ImagePlaneCurve` (§6 of the report). (b) of `ImagePlaneCurve` follows in Lean
(`imagePlaneCurve_of`) from (b''), C2K (`σ` onto, so the affine image is infinite) and
Bezout-type finiteness (`Alg.finite_common_zeros`). Glue. -/
def ImagePlaneCurveClosed : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p ≠ σ.val p₀) →
      (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) →
        ρ.val p = OnePoint.infty) ∨
      ∃ P : K[X][X], Irreducible P ∧ 1 ≤ P.natDegree ∧
        (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t u : K,
          σ.val p = OnePoint.some t → ρ.val p = OnePoint.some u → Alg.evalXY t u P = 0) ∧
        (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t : K,
          σ.val p = OnePoint.some t → ρ.val p = OnePoint.infty → P.leadingCoeff.eval t = 0) ∧
        ∃ S : Set K[X][X], ∀ t u : K,
          (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
            connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧
            σ.val p = OnePoint.some t ∧ ρ.val p = OnePoint.some u) ↔
          ∀ Q ∈ S, Alg.evalXY t u Q = 0

open Polynomial in
/-- **(G1) from C2K and (G1').** -/
theorem imagePlaneCurve_of (h2 : ConstOrOntoAlgClosed) (hG : ImagePlaneCurveClosed) :
    ImagePlaneCurve := by
  classical
  intro K _ _ X f hP hS σ ρ p₀ hp₀ hne
  rcases hG K X f hP hS σ ρ p₀ hp₀ hne with hinf | ⟨P, hirr, hdeg, ha, hc, S, hSc⟩
  · exact Or.inl hinf
  refine Or.inr ⟨P, hirr, hdeg, ha, ?_, hc⟩
  have honto : ∀ t : OnePoint K, ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
      connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p = t := by
    rcases h2 K X f hP hS σ p₀ hp₀ with hcst | ho
    · obtain ⟨p, hp, hpc, hv⟩ := hne
      exact absurd (hcst p hp hpc) hv
    · exact ho
  let Im : Set (K × K) := {z | ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
    connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧
    σ.val p = OnePoint.some z.1 ∧ ρ.val p = OnePoint.some z.2}
  have hImInf : Im.Infinite := by
    have hlc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hirr.ne_zero
    have hsub : {t : K | P.leadingCoeff.eval t ≠ 0} ⊆ Prod.fst '' Im := by
      intro t ht
      obtain ⟨p, hp, hpc, hpt⟩ := honto (OnePoint.some t)
      induction hρ : ρ.val p using OnePoint.rec with
      | infty => exact absurd (hc p hp hpc t hpt hρ) ht
      | coe u => exact ⟨(t, u), ⟨p, hp, hpc, hpt, hρ⟩, rfl⟩
    have hinfK : {t : K | P.leadingCoeff.eval t ≠ 0}.Infinite := by
      have e : {t : K | P.leadingCoeff.eval t ≠ 0} =
          ((P.leadingCoeff.roots.toFinset : Finset K) : Set K)ᶜ := by
        ext t
        simp [mem_roots hlc0]
      rw [e]
      exact (Finset.finite_toSet _).infinite_compl
    exact fun hfin => hinfK ((hfin.image Prod.fst).subset hsub)
  intro t u htu
  refine (hSc t u).2 fun Q hQ => ?_
  by_cases hPQ : P ∣ Q
  · obtain ⟨R, rfl⟩ := hPQ
    rw [Alg.evalXY_mul, htu, zero_mul]
  · exfalso
    apply hImInf
    refine (Alg.finite_common_zeros hirr hdeg hPQ).subset ?_
    rintro ⟨t', u'⟩ ⟨p, hp, hpc, hpt, hpu⟩
    exact ⟨ha p hp hpc t' u' hpt hpu, (hSc t' u').1 ⟨p, hp, hpc, hpt, hpu⟩ Q hQ⟩

/-! ## §5 Clause (c) of (G1') from irreducibility of the component (task curve-glue) -/

/-- **(CI) Connected components of a proper smooth curve over a field are irreducible.** If
`X → Spec K` is proper and smooth of relative dimension 1 over a field, every connected component of
`X` is irreducible (properness is not needed, but is kept: it is where (CI) is used, and it makes
the Lean proof `componentIrreducible` in `MobiusFinal.lean` a Noetherian argument).

Why true (STANDARD; references UNVERIFIED): smooth over a field implies regular, hence normal
(Stacks, *Varieties*, smooth ⇒ normal; Hartshorne II.8 for regular local rings being domains);
a locally Noetherian normal scheme is a disjoint union of integral open subschemes (its local rings
are domains, so irreducible components are disjoint and open), so its connected components are
its irreducible components. Glue (standard commutative algebra and topology). Not in Mathlib
v4.35 as stated (task infra-smooth-dim proved that the local rings at closed points are regular of
dimension 1, `stalk_dim_of_smoothOfRelativeDimension`, which is the main input; with it, (CI) is
proved in `MobiusFinal.lean`, `componentIrreducible`). -/
def ComponentIrreducible : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)), IsProper f →
    SmoothOfRelativeDimension 1 f → ∀ x : X, IsIrreducible (connectedComponent x)

open Polynomial in
/-- **(G1'') `ImagePlaneCurveClosed` without clause (c).** Either `ρ ≡ ∞` on the `K`-points of
the component `W` of `p₀`, or there is an irreducible `P ∈ K[x][y]` of `y`-degree `≥ 1` with
(a) `P(σ(p), ρ(p)) = 0` at the `K`-points of `W` with both values finite, and (b'') the affine
image `{(σ(p), ρ(p))}` is Zariski closed in `K²`. Why true: §6 of the report (clauses (a), (b'')
of (G1')). Glue. -/
def ImagePlaneCurveIrr : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p ≠ σ.val p₀) →
      (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) →
        ρ.val p = OnePoint.infty) ∨
      ∃ P : K[X][X], Irreducible P ∧ 1 ≤ P.natDegree ∧
        (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t u : K,
          σ.val p = OnePoint.some t → ρ.val p = OnePoint.some u → Alg.evalXY t u P = 0) ∧
        ∃ S : Set K[X][X], ∀ t u : K,
          (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
            connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧
            σ.val p = OnePoint.some t ∧ ρ.val p = OnePoint.some u) ↔
          ∀ Q ∈ S, Alg.evalXY t u Q = 0

section ClauseC

variable {K : Type} [Field K] {X : Scheme.{0}}

/-- `cst f O` as a ring hom. -/
def cstRH (f : X ⟶ Spec (CommRingCat.of K)) (O : X.Opens) : K →+* Γ(X, O) :=
  (res le_top).comp ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

open Polynomial in
/-- `P(F, G) ∈ Γ(X, O)` for `P ∈ K[x][y]` and sections `F, G`. -/
def polySec (f : X ⟶ Spec (CommRingCat.of K)) {O : X.Opens} (P : K[X][X]) (F G : Γ(X, O)) :
    Γ(X, O) :=
  P.eval₂ (eval₂RingHom (cstRH f O) F) G

open Polynomial in
theorem ev_polySec (f : X ⟶ Spec (CommRingCat.of K)) (p : Spec (CommRingCat.of K) ⟶ X)
    (hp : p ≫ f = 𝟙 _) {O : X.Opens} (hx : ptOf p ∈ O) (P : K[X][X]) (F G : Γ(X, O)) :
    ev p hx (polySec f P F G) = P.eval₂ (evalRingHom (ev p hx F)) (ev p hx G) := by
  unfold polySec
  rw [hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_C,
      coe_evalRingHom, eval_C]
    exact ev_cst f p hp hx a
  · simp

open Polynomial in
/-- **Clause (c) from (a) and irreducibility** (Lean-proved). On a preirreducible open `W` with a
`K`-point where `σ` is finite and `ρ ∈ K^×`, if `P(σ, ρ) = 0` at the finite points of `W`, then
`lc_y(P)(σ(p₁)) = 0` at every `K`-point `p₁` of `W` with `σ(p₁)` finite and `ρ(p₁) = ∞`: the
section `P^rev(σ, 1/ρ)` on `W ∩ {σ ≠ ∞} ∩ {ρ ≠ 0}` vanishes on the dense open `{ρ ≠ ∞}`, hence
at `p₁`, where it equals `lc_y(P)(σ(p₁))`. -/
theorem lc_eval_eq_zero_of_irreducible [IsAlgClosed K] (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] [JacobsonSpace X] (σ ρ : ToP1 X) (W : X.Opens)
    (hW : IsPreirreducible (W : Set X)) (P : K[X][X])
    (ha : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ptOf p ∈ W → ∀ t u : K,
      σ.val p = OnePoint.some t → ρ.val p = OnePoint.some u → Alg.evalXY t u P = 0)
    (hne : ((W : Set X) ∩ ((σ.U : Set X) ∩ ((ρ.U : Set X) ∩ ρ.V))).Nonempty)
    (p₁ : Spec (CommRingCat.of K) ⟶ X) (hp₁ : p₁ ≫ f = 𝟙 _) (hW₁ : ptOf p₁ ∈ W) (t : K)
    (ht : σ.val p₁ = OnePoint.some t) (hρ : ρ.val p₁ = OnePoint.infty) :
    P.leadingCoeff.eval t = 0 := by
  have hσU : ptOf p₁ ∈ σ.U := by
    by_contra h
    rw [val_of_not_mem σ p₁ h] at ht
    exact OnePoint.infty_ne_coe t ht
  have hρU : ptOf p₁ ∉ ρ.U := fun h => by
    rw [val_of_mem ρ p₁ h] at hρ
    exact OnePoint.coe_ne_infty _ hρ
  have hρV : ptOf p₁ ∈ ρ.V := mem_V_of_not_mem_U ρ hρU
  let O' : X.Opens := W ⊓ σ.U ⊓ ρ.V
  have hle1 : O' ≤ σ.U := fun x hx => hx.1.2
  have hle2 : O' ≤ ρ.V := fun x hx => hx.2
  let h' : Γ(X, O') := polySec f P.reverse (res hle1 σ.f) (res hle2 ρ.g)
  have hev : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O',
      ev p hx h' = P.reverse.eval₂ (evalRingHom (ev p (hle1 hx) σ.f)) (ev p (hle2 hx) ρ.g) := by
    intro p hp hx
    simp only [h']
    rw [ev_polySec f p hp, ev_res, ev_res]
  have hvan : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O',
      ptOf p ∈ ρ.U → ev p hx h' = 0 := by
    intro p hp hx hU
    rw [hev p hp hx]
    have hu : ev p hU ρ.f * ev p (hle2 hx) ρ.g = 1 := ev_f_mul_g ρ p hU (hle2 hx)
    have hu0 : ev p hU ρ.f ≠ 0 := left_ne_zero_of_mul_eq_one hu
    have hg : ev p (hle2 hx) ρ.g = (ev p hU ρ.f)⁻¹ := eq_inv_of_mul_eq_one_right hu
    have hPa : Alg.evalXY (ev p (hle1 hx) σ.f) (ev p hU ρ.f) P = 0 :=
      ha p hp hx.1.1 _ _ (val_of_mem σ p (hle1 hx)) (val_of_mem ρ p hU)
    let _ : Invertible (ev p hU ρ.f) := invertibleOfNonzero hu0
    have key := eval₂_reverse_mul_pow (evalRingHom (ev p (hle1 hx) σ.f)) (ev p hU ρ.f) P
    have e2 : P.eval₂ (evalRingHom (ev p (hle1 hx) σ.f)) (ev p hU ρ.f) =
        Alg.evalXY (ev p (hle1 hx) σ.f) (ev p hU ρ.f) P := (Polynomial.eval_map _ _).symm
    rw [invOf_eq_inv, e2, hPa] at key
    rw [hg]
    exact (mul_eq_zero.mp key).resolve_right (pow_ne_zero _ hu0)
  have hsub : ((O' : Set X) ∩ ρ.U) ⊆ ((X.basicOpen h' : X.Opens) : Set X)ᶜ := by
    rintro x ⟨hxO, hxU⟩ hxb
    obtain ⟨p, hp, ⟨hpO, hpU⟩, hpb⟩ := exists_point_of_isLocallyClosed f
      (Z := ((O' : Set X) ∩ ρ.U) ∩ X.basicOpen h')
      ((O'.isOpen.inter ρ.U.isOpen).inter (X.basicOpen h').isOpen).isLocallyClosed
      ⟨x, ⟨hxO, hxU⟩, hxb⟩
    exact (ev_eq_zero_iff p hpO h').1 (hvan p hp hpO hpU) hpb
  have hcl : ptOf p₁ ∈ closure ((O' : Set X) ∩ ρ.U) := by
    have hopen : IsOpen ((σ.U : Set X) ∩ ((ρ.U : Set X) ∩ ρ.V)) :=
      σ.U.isOpen.inter (ρ.U.isOpen.inter ρ.V.isOpen)
    have h := subset_closure_inter_of_isPreirreducible_of_isOpen hW hopen hne hW₁
    have e : (W : Set X) ∩ ((σ.U : Set X) ∩ ((ρ.U : Set X) ∩ ρ.V)) = (O' : Set X) ∩ ρ.U := by
      ext x
      simp only [O', Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
      tauto
    rwa [e] at h
  have hnot : ptOf p₁ ∉ X.basicOpen h' :=
    closure_minimal hsub (X.basicOpen h').isOpen.isClosed_compl hcl
  have hx₁ : ptOf p₁ ∈ O' := ⟨⟨hW₁, hσU⟩, hρV⟩
  have h0 := (ev_eq_zero_iff p₁ hx₁ h').2 hnot
  rw [hev p₁ hp₁ hx₁, ev_g_eq_zero ρ p₁ (hle2 hx₁) hρU, eval₂_at_zero, coeff_zero_reverse] at h0
  have hs : ev p₁ (hle1 hx₁) σ.f = t := by
    have e := val_of_mem σ p₁ hσU
    rw [ht] at e
    exact (OnePoint.coe_injective e).symm
  rw [hs] at h0
  simpa using h0

end ClauseC

open Polynomial in
/-- **(G1') from (CI) and (G1'').** -/
theorem imagePlaneCurveClosed_of (hI : ComponentIrreducible) (hG : ImagePlaneCurveIrr) :
    ImagePlaneCurveClosed := by
  intro K _ _ X f hP hS σ ρ p₀ hp₀ hne
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := { }
  set x₀ := ptOf p₀ with hx₀
  let W : X.Opens := ⟨connectedComponent x₀, isOpen_connectedComponent_of_noetherian x₀⟩
  have memW : ∀ p : Spec (CommRingCat.of K) ⟶ X, ptOf p ∈ W ↔
      connectedComponent (ptOf p) = connectedComponent x₀ :=
    fun p => ⟨fun h => (connectedComponent_eq h).symm,
      fun h => by
        show ptOf p ∈ connectedComponent x₀
        rw [← h]; exact mem_connectedComponent⟩
  have hWi : IsPreirreducible (W : Set X) := (hI K X f hP hS x₀).isPreirreducible
  by_cases hinf : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
      connectedComponent (ptOf p) = connectedComponent x₀ → ρ.val p = OnePoint.infty
  · exact Or.inl hinf
  rcases hG K X f hP hS σ ρ p₀ hp₀ hne with hinf' | ⟨P, hirr, hdeg, ha, hclo⟩
  · exact absurd hinf' hinf
  refine Or.inr ⟨P, hirr, hdeg, ha, ?_, hclo⟩
  intro p₁ hp₁ hpc₁ t ht hρ
  refine lc_eval_eq_zero_of_irreducible f σ ρ W hWi P
    (fun p hp hpW => ha p hp ((memW p).1 hpW)) ?_ p₁ hp₁ ((memW p₁).2 hpc₁) t ht hρ
  have h1 : ((W : Set X) ∩ σ.U).Nonempty := by
    obtain ⟨p, hp, hpc, hv⟩ := hne
    by_cases h : ptOf p₀ ∈ σ.U
    · exact ⟨_, (mem_connectedComponent : x₀ ∈ connectedComponent x₀), h⟩
    · have hpU : ptOf p ∈ σ.U := by
        by_contra h'
        exact hv (by rw [val_of_not_mem σ p h', val_of_not_mem σ p₀ h])
      exact ⟨_, (memW p).2 hpc, hpU⟩
  have h2 : ((W : Set X) ∩ ρ.U).Nonempty := by
    push Not at hinf
    obtain ⟨p, hp, hpc, hv⟩ := hinf
    have hpU : ptOf p ∈ ρ.U := by
      by_contra h'
      exact hv (val_of_not_mem ρ p h')
    exact ⟨_, (memW p).2 hpc, hpU⟩
  have h3 : ((W : Set X) ∩ ρ.V).Nonempty := by
    refine ⟨_, (memW p₁).2 hpc₁, mem_V_of_not_mem_U ρ fun h => ?_⟩
    rw [val_of_mem ρ p₁ h] at hρ
    exact OnePoint.coe_ne_infty _ hρ
  have h23 := hWi _ _ ρ.U.isOpen ρ.V.isOpen h2 h3
  exact hWi _ _ σ.U.isOpen (ρ.U.isOpen.inter ρ.V.isOpen) h1 h23

/-! ## §6 (G1'') from algebraic dependence, a closed image, irreducibility and C2K (task curve-glue) -/

open Polynomial in
/-- **(AD) `σ` and `ρ` are algebraically dependent on a connected component.** For `X → Spec K`
proper and smooth of relative dimension 1 over `K = K̄`, `σ, ρ : X → P¹` and a `K`-point `p₀`,
some nonzero `P ∈ K[x][y]` has `P(σ(p), ρ(p)) = 0` at every `K`-point `p` of the connected
component of `p₀` where both values are finite.

Why true (STANDARD; numbering UNVERIFIED): the component `W` is an integral curve, its function
field `K(W)` has transcendence degree `dim W = 1` over `K` (Hartshorne I.1.8A and I.6), so the
rational functions `σ, ρ` satisfy a nonzero polynomial relation `P(σ, ρ) = 0` in `K(W)`; the
regular function `P(σ, ρ)` on the open set where both are finite is then zero (`W` reduced), so it
vanishes at those `K`-points. Glue. -/
def AlgDep : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      ∃ P : K[X][X], P ≠ 0 ∧
        ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t u : K,
          σ.val p = OnePoint.some t → ρ.val p = OnePoint.some u → Alg.evalXY t u P = 0

open Polynomial in
/-- **(IC) The affine image of a connected component under `(σ, ρ)` is Zariski closed.** In the
same setting, the set of `(σ(p), ρ(p)) ∈ K²` over the `K`-points `p` of the connected component of
`p₀` with both values finite is the common zero set of some `S ⊆ K[x][y]`.

Why true (STANDARD): the component `W` is proper over `K` (open and closed in `X`), so its image
`D` under `(σ, ρ) : W → P¹ × P¹` is closed (`P¹ × P¹` separated); `D ∩ 𝔸²` is closed in `𝔸²`,
hence `V(I)` for an ideal `I` (take `S = I`), and its `K`-points are exactly the images of the
`K`-points of `W` (a fibre over a closed point is a nonempty closed set of finite type over `K`,
so it contains a closed point, a `K`-point by the Nullstellensatz). Glue (properness). -/
def ImageClosed : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      ∃ S : Set K[X][X], ∀ t u : K,
        (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧
          σ.val p = OnePoint.some t ∧ ρ.val p = OnePoint.some u) ↔
        ∀ Q ∈ S, Alg.evalXY t u Q = 0

section FactorSel

variable {K : Type} [Field K] {X : Scheme.{0}}

open Polynomial in
/-- `evalXY t u` as a ring hom. -/
def evalXYHom (t u : K) : K[X][X] →+* K := (evalRingHom u).comp (mapRingHom (evalRingHom t))

open Polynomial in
theorem evalXYHom_apply (t u : K) (P : K[X][X]) : evalXYHom t u P = Alg.evalXY t u P := rfl

open Polynomial in
/-- **Choosing an irreducible factor** (Lean-proved). On an irreducible open `O` of a Jacobson
scheme of finite type over `K = K̄`, if `P(F, G)` vanishes at every `K`-point of `O`, then so does
`q(F, G)` for some irreducible factor `q` of `P` (the zero loci of the factors are closed and
cover `O`). -/
theorem exists_factor_vanishing [IsAlgClosed K] (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] [JacobsonSpace X] {O : X.Opens} (hO : IsIrreducible (O : Set X))
    (F G : Γ(X, O)) (P : K[X][X]) (hP0 : P ≠ 0)
    (hvan : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O,
      Alg.evalXY (ev p hx F) (ev p hx G) P = 0) :
    ∃ q ∈ UniqueFactorizationMonoid.factors P, ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
      ∀ hx : ptOf p ∈ O, Alg.evalXY (ev p hx F) (ev p hx G) q = 0 := by
  classical
  set fs := UniqueFactorizationMonoid.factors P with hfs
  let C : K[X][X] → Set X := fun q => ((X.basicOpen (polySec f q F G) : X.Opens) : Set X)ᶜ
  have hev : ∀ (q : K[X][X]) (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
      (hx : ptOf p ∈ O), ev p hx (polySec f q F G) = Alg.evalXY (ev p hx F) (ev p hx G) q := by
    intro q p hp hx
    rw [ev_polySec f p hp]
    exact (Polynomial.eval_map _ _).symm
  have hpt : ∀ (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) (hx : ptOf p ∈ O),
      ∃ q ∈ fs, Alg.evalXY (ev p hx F) (ev p hx G) q = 0 := by
    intro p hp hx
    obtain ⟨v, hv⟩ := UniqueFactorizationMonoid.factors_prod hP0
    have h0 := hvan p hp hx
    rw [← hv, Alg.evalXY_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · rw [← evalXYHom_apply, map_multiset_prod, Multiset.prod_eq_zero_iff] at h
      obtain ⟨q, hq, hq0⟩ := Multiset.mem_map.1 h
      exact ⟨q, hq, hq0⟩
    · exact absurd h ((v.isUnit.map (evalXYHom (ev p hx F) (ev p hx G))).ne_zero)
  have hcov : (O : Set X) ⊆ ⋃₀ ↑(fs.toFinset.image C) := by
    intro x hx
    by_contra hnot
    let Z : Set X := (O : Set X) ∩ ⋂ q ∈ fs.toFinset, ((X.basicOpen (polySec f q F G) : X.Opens) : Set X)
    have hZo : IsOpen Z :=
      O.isOpen.inter (isOpen_biInter_finset fun q _ => (X.basicOpen (polySec f q F G)).isOpen)
    have hxZ : x ∈ Z := by
      refine ⟨hx, Set.mem_iInter₂.2 fun q hq => ?_⟩
      by_contra hxq
      exact hnot ⟨C q, Finset.mem_coe.2 (Finset.mem_image_of_mem C hq), hxq⟩
    obtain ⟨p, hp, hpO, hpall⟩ := exists_point_of_isLocallyClosed f hZo.isLocallyClosed ⟨x, hxZ⟩
    obtain ⟨q, hq, hq0⟩ := hpt p hp hpO
    have hb : ptOf p ∈ X.basicOpen (polySec f q F G) :=
      Set.mem_iInter₂.1 hpall q (Multiset.mem_toFinset.2 hq)
    exact (ev_eq_zero_iff p hpO _).1 ((hev q p hp hpO).trans hq0) hb
  have hcl : ∀ z ∈ fs.toFinset.image C, IsClosed z := by
    intro z hz
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hz
    exact (X.basicOpen (polySec f q F G)).isOpen.isClosed_compl
  obtain ⟨z, hz, hOz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hO) _ hcl hcov
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hz
  refine ⟨q, Multiset.mem_toFinset.1 hq, fun p hp hx => ?_⟩
  rw [← hev q p hp hx]
  exact (ev_eq_zero_iff p hx _).2 (hOz hx)

end FactorSel

open Polynomial in
/-- **(G1'') from C2K, (CI), (AD) and (IC).** -/
theorem imagePlaneCurveIrr_of (h2 : ConstOrOntoAlgClosed) (hI : ComponentIrreducible)
    (hA : AlgDep) (hC : ImageClosed) : ImagePlaneCurveIrr := by
  classical
  intro K _ _ X f hP hS σ ρ p₀ hp₀ hne
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := { }
  set x₀ := ptOf p₀ with hx₀
  let W : X.Opens := ⟨connectedComponent x₀, isOpen_connectedComponent_of_noetherian x₀⟩
  have memW : ∀ p : Spec (CommRingCat.of K) ⟶ X, ptOf p ∈ W ↔
      connectedComponent (ptOf p) = connectedComponent x₀ :=
    fun p => ⟨fun h => (connectedComponent_eq h).symm,
      fun h => by
        show ptOf p ∈ connectedComponent x₀
        rw [← h]; exact mem_connectedComponent⟩
  have hWi : IsPreirreducible (W : Set X) := (hI K X f hP hS x₀).isPreirreducible
  by_cases hinf : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
      connectedComponent (ptOf p) = connectedComponent x₀ → ρ.val p = OnePoint.infty
  · exact Or.inl hinf
  right
  obtain ⟨P, hP0, hPa⟩ := hA K X f hP hS σ ρ p₀ hp₀
  obtain ⟨S, hSc⟩ := hC K X f hP hS σ ρ p₀ hp₀
  have memU : ∀ (τ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (t : K),
      τ.val p = OnePoint.some t → ptOf p ∈ τ.U := by
    intro τ p t h
    by_contra h'
    rw [val_of_not_mem τ p h'] at h
    exact OnePoint.infty_ne_coe t h
  have honto : ∀ t : OnePoint K, ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
      connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p = t := by
    rcases h2 K X f hP hS σ p₀ hp₀ with hcst | ho
    · obtain ⟨p, hp, hpc, hv⟩ := hne
      exact absurd (hcst p hp hpc) hv
    · exact ho
  -- the irreducible open `O = W ∩ {σ ≠ ∞} ∩ {ρ ≠ ∞}`
  let O : X.Opens := W ⊓ σ.U ⊓ ρ.U
  have hle1 : O ≤ σ.U := fun x hx => hx.1.2
  have hle2 : O ≤ ρ.U := fun x hx => hx.2
  have h1 : ((W : Set X) ∩ σ.U).Nonempty := by
    obtain ⟨p, hp, hpc, hpt⟩ := honto (OnePoint.some 0)
    exact ⟨_, (memW p).2 hpc, memU σ p 0 hpt⟩
  have h2' : ((W : Set X) ∩ ρ.U).Nonempty := by
    push Not at hinf
    obtain ⟨p, hp, hpc, hv⟩ := hinf
    have hpU : ptOf p ∈ ρ.U := by
      by_contra h'
      exact hv (val_of_not_mem ρ p h')
    exact ⟨_, (memW p).2 hpc, hpU⟩
  have hOne : (O : Set X).Nonempty := by
    obtain ⟨x, hxW, hx1, hx2⟩ := hWi _ _ σ.U.isOpen ρ.U.isOpen h1 h2'
    exact ⟨x, ⟨hxW, hx1⟩, hx2⟩
  have hOirr : IsIrreducible (O : Set X) :=
    ⟨hOne, hWi.open_subset O.isOpen fun x hx => hx.1.1⟩
  have hvan : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O,
      Alg.evalXY (ev p hx (res hle1 σ.f)) (ev p hx (res hle2 ρ.f)) P = 0 := by
    intro p hp hx
    rw [ev_res, ev_res]
    exact hPa p hp ((memW p).1 hx.1.1) _ _ (val_of_mem σ p _) (val_of_mem ρ p _)
  obtain ⟨q, hq, hqv⟩ := exists_factor_vanishing f hOirr (res hle1 σ.f) (res hle2 ρ.f) P hP0 hvan
  have hqirr : Irreducible q := UniqueFactorizationMonoid.irreducible_of_factor q hq
  have hqa : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
      connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t u : K,
      σ.val p = OnePoint.some t → ρ.val p = OnePoint.some u → Alg.evalXY t u q = 0 := by
    intro p hp hpc t u ht hu
    have hσ : ptOf p ∈ σ.U := memU σ p t ht
    have hρ : ptOf p ∈ ρ.U := memU ρ p u hu
    have hx : ptOf p ∈ O := ⟨⟨(memW p).2 hpc, hσ⟩, hρ⟩
    have e := hqv p hp hx
    rw [ev_res, ev_res] at e
    rw [val_of_mem σ p hσ] at ht
    rw [val_of_mem ρ p hρ] at hu
    rwa [OnePoint.coe_injective ht, OnePoint.coe_injective hu] at e
  have hdeg : 1 ≤ q.natDegree := by
    by_contra hd
    have hq0 : q.natDegree = 0 := by omega
    have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero hq0
    set a := q.coeff 0 with ha
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hqC
      exact hqirr.ne_zero hqC
    let O₁ : X.Opens := W ⊓ σ.U
    have hle3 : O₁ ≤ σ.U := fun x hx => hx.2
    let hs : Γ(X, O₁) := polySec f (C a) (res hle3 σ.f) 0
    have hev1 : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O₁,
        ev p hx hs = a.eval (ev p (hle3 hx) σ.f) := by
      intro p hp hx
      simp only [hs]
      rw [ev_polySec f p hp, ev_res]
      simp
    have hsub : (O : Set X) ⊆ ((X.basicOpen hs : X.Opens) : Set X)ᶜ := by
      intro x hxO hxb
      obtain ⟨p, hp, hpO, hpb⟩ := exists_point_of_isLocallyClosed f
        (Z := (O : Set X) ∩ X.basicOpen hs)
        (O.isOpen.inter (X.basicOpen hs).isOpen).isLocallyClosed ⟨x, hxO, hxb⟩
      have hpO₁ : ptOf p ∈ O₁ := hpO.1
      have e := hqv p hp hpO
      rw [ev_res, ev_res, hqC] at e
      have e' : ev p hpO₁ hs = 0 := by
        rw [hev1 p hp hpO₁]
        simpa [Alg.evalXY] using e
      exact (ev_eq_zero_iff p hpO₁ hs).1 e' hpb
    have hWcl : (W : Set X) ⊆ closure (O : Set X) := by
      have hne' : ((W : Set X) ∩ ((σ.U : Set X) ∩ ρ.U)).Nonempty := by
        obtain ⟨x, hx⟩ := hOne
        exact ⟨x, hx.1.1, hx.1.2, hx.2⟩
      have h := subset_closure_inter_of_isPreirreducible_of_isOpen hWi
        (σ.U.isOpen.inter ρ.U.isOpen) hne'
      have e : (W : Set X) ∩ ((σ.U : Set X) ∩ ρ.U) = (O : Set X) := by
        ext x
        simp only [O, Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
        tauto
      rwa [e] at h
    obtain ⟨t, ht⟩ : ∃ t : K, a.eval t ≠ 0 := by
      by_contra! h
      exact ha0 (by
        have := Polynomial.funext (p := a) (q := 0) fun t => by rw [h t, eval_zero]
        exact this)
    obtain ⟨p, hp, hpc, hpt⟩ := honto (OnePoint.some t)
    have hσ : ptOf p ∈ σ.U := memU σ p t hpt
    have hx : ptOf p ∈ O₁ := ⟨(memW p).2 hpc, hσ⟩
    have hnot : ptOf p ∉ X.basicOpen hs :=
      closure_minimal hsub (X.basicOpen hs).isOpen.isClosed_compl (hWcl hx.1)
    have e := (ev_eq_zero_iff p hx hs).2 hnot
    rw [hev1 p hp hx] at e
    rw [val_of_mem σ p hσ] at hpt
    rw [OnePoint.coe_injective hpt] at e
    exact ht e
  exact ⟨q, hqirr, hdeg, hqa, S, hSc⟩

/-! ## The leaf (L0) and the reduction -/

section L0

variable {K : Type} [Field K] {X : Scheme.{0}}

end L0

/-- **`SmoothStalkDimOne` holds** (task infra-smooth-dim). -/
theorem smoothStalkDimOne : SmoothStalkDimOne := by
  intro K _ X f hf x hx
  have := (InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension f 1 x hx).1
  rw [this, Nat.cast_one]

/-! ## (CI) proved: components of a proper smooth curve are irreducible (task curve-glue)

Uses task infra-smooth-dim's `InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension` (local rings
at closed points have Krull dimension 1 and principal maximal ideal). -/

namespace CurveGlueCI

open CategoryTheory AlgebraicGeometry IsLocalRing

/-- **A Noetherian local ring of Krull dimension 1 with principal maximal ideal is a domain.**
(Krull intersection theorem: every nonzero element is `π^n · unit`; `π` is not nilpotent since the
dimension is positive.) -/
theorem isDomain_of_dim_one {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) (hspan : (maximalIdeal R).spanFinrank = 1) : IsDomain R := by
  classical
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan'⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank hfg
  rw [hspan] at hs
  obtain ⟨π, rfl⟩ := Set.encard_eq_one.1 (by exact_mod_cast hs)
  -- `π` is not nilpotent
  have hπ : ∀ n : ℕ, π ^ n ≠ 0 := by
    intro n hn
    have hsub : ∀ p : PrimeSpectrum R, p.asIdeal = maximalIdeal R := by
      intro p
      refine le_antisymm (le_maximalIdeal p.2.ne_top) ?_
      rw [← hspan', Ideal.span_le, Set.singleton_subset_iff]
      exact p.2.mem_of_pow_mem n (by rw [hn]; exact p.asIdeal.zero_mem)
    have : Subsingleton (PrimeSpectrum R) :=
      ⟨fun p q => PrimeSpectrum.ext ((hsub p).trans (hsub q).symm)⟩
    have h0 : ringKrullDim R = 0 := Order.krullDim_eq_zero
    rw [hdim] at h0
    norm_num at h0
  -- every nonzero element is `π ^ n * unit`
  have hdec : ∀ a : R, a ≠ 0 → ∃ (n : ℕ) (u : R), IsUnit u ∧ a = π ^ n * u := by
    intro a ha
    have hex : ∃ k : ℕ, a ∉ maximalIdeal R ^ k := by
      by_contra! h
      apply ha
      have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
      rw [← Submodule.mem_bot R, ← this, Submodule.mem_iInf]
      exact h
    let k := Nat.find hex
    have hk : a ∉ maximalIdeal R ^ k := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      apply hk
      rw [h0, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    obtain ⟨n, hn⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero hk0
    have hmem : a ∈ maximalIdeal R ^ n := by
      have := Nat.find_min hex (show n < k by omega)
      push Not at this
      exact this
    rw [← hspan', Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
    obtain ⟨u, hu⟩ := hmem
    refine ⟨n, u, ?_, by rw [← hu, mul_comm]⟩
    by_contra hu'
    have hum : u ∈ maximalIdeal R := (mem_maximalIdeal u).2 hu'
    rw [← hspan', Ideal.mem_span_singleton'] at hum
    obtain ⟨w, hw⟩ := hum
    apply hk
    rw [hn, ← hspan', Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨w, by rw [← hu, ← hw]; ring⟩
  have : NoZeroDivisors R := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨n, u, hu, rfl⟩ := hdec a hne.1
    obtain ⟨m, v, hv, rfl⟩ := hdec b hne.2
    have : π ^ (n + m) * (u * v) = 0 := by rw [← hab]; ring
    exact hπ (n + m) ((hu.mul hv).mul_left_eq_zero.mp this)
  exact NoZeroDivisors.to_isDomain R

/-- **Two irreducible components meeting at a point with a domain stalk coincide.** -/
theorem irreducibleComponent_eq_of_isDomain_stalk {X : Scheme} {Z₁ Z₂ : Set X}
    (h₁ : Z₁ ∈ irreducibleComponents X) (h₂ : Z₂ ∈ irreducibleComponents X) {y : X}
    (hy₁ : y ∈ Z₁) (hy₂ : y ∈ Z₂) (hdom : IsDomain (X.presheaf.stalk y)) : Z₁ = Z₂ := by
  let G : Set X := Set.range (X.fromSpecStalk y)
  have hG : IsIrreducible G := by
    have : IrreducibleSpace (Spec (X.presheaf.stalk y)) := PrimeSpectrum.irreducibleSpace
    show IsIrreducible (Set.range (X.fromSpecStalk y))
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (X.fromSpecStalk y).continuous.continuousOn
  have key : ∀ Z ∈ irreducibleComponents X, y ∈ Z → Z = closure G := by
    intro Z hZ hyZ
    have hcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
    have hgen := hZ.1.isGenericPoint_genericPoint hcl
    have hspec : hZ.1.genericPoint ⤳ y := by
      rw [specializes_iff_mem_closure, hgen.def]; exact hyZ
    have hmem : hZ.1.genericPoint ∈ G := by
      show _ ∈ Set.range (X.fromSpecStalk y)
      rw [Scheme.range_fromSpecStalk]; exact hspec
    have hsub : Z ⊆ closure G := by
      rw [← hgen.def]
      exact closure_mono (Set.singleton_subset_iff.2 hmem)
    exact (hZ.eq_of_subset hG.closure hsub)
  rw [key Z₁ h₁ hy₁, key Z₂ h₂ hy₂]

end CurveGlueCI

/-- **(CI), proved** (from infra-smooth-dim's stalk dimensions). -/
theorem componentIrreducible : ComponentIrreducible := by
  intro K _ X f hP hS x
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := { }
  have : SmoothOfRelativeDimension 1 f := hS
  -- stalks at closed points are domains
  have hdom : ∀ y : X, IsClosed ({y} : Set X) → IsDomain (X.presheaf.stalk y) := by
    intro y hy
    obtain ⟨h1, h2⟩ := InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension f 1 y hy
    exact CurveGlueCI.isDomain_of_dim_one (by exact_mod_cast h1) h2
  -- irreducible components are pairwise disjoint
  have hdisj : ∀ Z₁ ∈ irreducibleComponents X, ∀ Z₂ ∈ irreducibleComponents X,
      (Z₁ ∩ Z₂).Nonempty → Z₁ = Z₂ := by
    intro Z₁ h₁ Z₂ h₂ hne
    have hcl : IsClosed (Z₁ ∩ Z₂) :=
      (isClosed_of_mem_irreducibleComponents Z₁ h₁).inter (isClosed_of_mem_irreducibleComponents Z₂ h₂)
    obtain ⟨y, ⟨hy₁, hy₂⟩, hyc⟩ := nonempty_inter_closedPoints hne hcl.isLocallyClosed
    exact CurveGlueCI.irreducibleComponent_eq_of_isDomain_stalk h₁ h₂ hy₁ hy₂
      (hdom y (mem_closedPoints_iff.mp hyc))
  -- the irreducible component of `x` is clopen
  set Z := irreducibleComponent x with hZ
  have hZc : IsClosed Z := isClosed_irreducibleComponent
  have hZmem := irreducibleComponent_mem_irreducibleComponents x
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have hcompl : Zᶜ = ⋃ Z' ∈ {Z' ∈ irreducibleComponents X | Z' ≠ Z}, Z' := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hz
      refine ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z, ?_⟩,
        mem_irreducibleComponent⟩
      intro h
      exact hz (h ▸ mem_irreducibleComponent)
    · rintro ⟨Z', ⟨hZ', hne⟩, hzZ'⟩ hzZ
      exact hne (hdisj Z' hZ' Z hZmem ⟨z, hzZ', hzZ⟩)
  have hZo : IsOpen Z := by
    rw [← isClosed_compl_iff, hcompl]
    exact (hfin.subset fun Z' hZ' => hZ'.1).isClosed_biUnion fun Z' hZ' =>
      isClosed_of_mem_irreducibleComponents Z' hZ'.1
  have h1 : connectedComponent x ⊆ Z :=
    (IsClopen.connectedComponent_subset ⟨hZc, hZo⟩ mem_irreducibleComponent)
  have h2 : Z ⊆ connectedComponent x :=
    isIrreducible_irreducibleComponent.isConnected.subset_connectedComponent mem_irreducibleComponent
  rw [Set.Subset.antisymm h1 h2]
  exact isIrreducible_irreducibleComponent

end Pin

namespace CurveGlue

open CategoryTheory AlgebraicGeometry Limits
open PkgI3 Pin

/-! ## Copied verbatim from `scratch/h-decomposition/Leaves.lean` (namespace `LeafAdopt`) -/

variable {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
  {π₆ : ToP1 X.left}

/-! ## New: CM points on any triple -/

end CurveGlue

namespace CurveGlue

open CategoryTheory AlgebraicGeometry Limits Pin

end CurveGlue

namespace CurveGlue

open CategoryTheory AlgebraicGeometry Limits Pin

end CurveGlue

end AV

end LeafQM

end
