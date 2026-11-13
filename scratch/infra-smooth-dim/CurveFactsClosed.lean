import Mathlib
import ZInQKernel.HDecomp.QM.Pairs
import Mathlib.LinearAlgebra.Lagrange

/-! # curve-facts with C1b proved (task infra-smooth-dim)

Part 1: `scratch/curve-facts/CurveFacts.lean` verbatim (without its imports and `#print` lines).
Part 2: `SmoothStalk.lean` §0-§4 verbatim. Part 3 (§6): C1b, C1a, C1 proved. -/

/-!
# curve-facts: `CurveRatFactor` and `CurveSurj` reduced to per-component curve facts

Task curve-facts (2026-11-13). See `docs/research/curve-facts.md`.

`CurveRatFactor` and `CurveSurj` are copied verbatim from `scratch/mobius-glue/MobiusGlue.lean`
(§2), together with `Mob.ratEval` (§1 there). Everything else they use (`ToP1`, `ToP1.val`,
`fieldPt`, `Qbar`) is imported from `ZInQKernel.HDecomp.QM.Pairs`, where mobius-glue took it from.

**Main results.**
* `curveSurj_of_comp : GeomCompInfinite → GeomCompConstOrOnto → CurveSurj`;
* `curveRatFactor_of_comp : GeomCompConstOrOnto → GeomCompRatFactor → CurveRatFactor`, using
  `geomCompFinite` (proved here from Mathlib: `S_ℚ̄` is a Noetherian scheme, so it has finitely
  many irreducible, hence connected, components) and `Mob.exists_interp` (proved here: rational
  interpolation of values in `P¹` at finitely many nodes by a coprime pair).

The named facts are stated over genuine definitions only: the base change
`S_ℚ̄ = S ×_{Spec ℚ} Spec ℚ̄` (Mathlib's `pullback`), the `ℚ̄`-point of `S_ℚ̄` induced by a
`ℚ̄`-point of `S` (`pullback.lift`), its point (`Scheme.SpecToEquivOfField`), and Mathlib's
`connectedComponent` in the underlying space of `S_ℚ̄`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits
open PkgI3

/-! ## §0 Copied verbatim from `scratch/mobius-glue/MobiusGlue.lean` -/

namespace Mob

open Polynomial

variable {K : Type} [Field K]


open scoped Classical in
/-- The value at a finite point `t` of the rational map `[F : G] : P¹ → P¹`. -/
def ratEval (F G : K[X]) (t : K) : OnePoint K :=
  if G.eval t = 0 then OnePoint.infty else OnePoint.some (F.eval t / G.eval t)

end Mob

open Polynomial in
/-- **Curve fact 1 (factorization through a rational function).** On a proper smooth curve
`S/ℚ`, if `ρ : S → P¹` is constant on the fibres of `σ : S → P¹` (on `ℚ̄`-points), then
`ρ = R ∘ σ` on `ℚ̄`-points with finite `σ`-value, for a rational function `R = [F : G]`,
`F, G ∈ ℚ̄[t]` coprime. (On a geometric component `C` where `σ` is nonconstant: the image of
`(σ, ρ) : C → P¹ × P¹` projects bijectively, hence birationally (char. 0), onto the normal
curve `P¹`, so its inverse is a morphism and `R = pr₂ ∘ pr₁⁻¹`; components where `σ` is
constant are absorbed by the fibre condition, or by Lagrange interpolation if every component
is. STANDARD; not in Mathlib.) -/
def CurveRatFactor : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ σ ρ : ToP1 S.left,
      (∀ y₁ y₂ : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y₁.left = σ.val (K := Qbar) y₂.left →
        ρ.val (K := Qbar) y₁.left = ρ.val (K := Qbar) y₂.left) →
      ∃ F G : Qbar[X], IsCoprime F G ∧ ∀ (y : fieldPt Qbar ⟶ S) (t : Qbar),
        σ.val (K := Qbar) y.left = OnePoint.some t → ρ.val (K := Qbar) y.left = Mob.ratEval F G t

/-- **Curve fact 2 (surjectivity).** A morphism `σ : S → P¹` from a proper smooth curve `S/ℚ`
with a `ℚ̄`-point, whose fibres on `ℚ̄`-points are finite, is onto `P¹(ℚ̄)`. (The geometric
component through the given point has infinitely many `ℚ̄`-points, so `σ` is nonconstant on
it; its image is closed and irreducible, hence `P¹`; closed points of `P¹_ℚ̄` lift to
`ℚ̄`-points. STANDARD, e.g. Hartshorne II.6.8; not in Mathlib.) -/
def CurveSurj : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    Nonempty (fieldPt Qbar ⟶ S) → ∀ σ : ToP1 S.left,
      (∀ y : fieldPt Qbar ⟶ S, {y' : fieldPt Qbar ⟶ S |
        σ.val (K := Qbar) y'.left = σ.val (K := Qbar) y.left}.Finite) →
      ∀ t : OnePoint Qbar, ∃ y : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y.left = t

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

end Pin

end AV

end LeafQM

end



/-! # Local rings of a standard smooth algebra over a field

Task infra-smooth-dim. Mathlib-only. (Lemmas from `MaxHeight.lean` and `CotQuot.lean` are copied
verbatim in §0, since scratch files cannot import each other.)

**Main result.** If `S` is a standard smooth algebra of relative dimension `n` over a field `k` and
`𝔪` is a maximal ideal of `S`, then `S_𝔪` has Krull dimension `n` and its maximal ideal is spanned by
`n` elements (so `S_𝔪` is regular, and `dim_κ 𝔪/𝔪² = n`).

Proof: write `S = k[x_ι]/(f_σ)` with invertible Jacobian, `M` the preimage of `𝔪`. Krull's height
theorem and `ht M = |ι|` give `dim S_𝔪 ≥ |ι| - |σ|`; the derivatives `∂f_i/∂x_{map j}` show that
the `f_i` have linearly independent classes in `M A_M / M² A_M`, so killing them lowers the embedding
dimension `|ι|` of the regular local ring `k[x]_M` by `|σ|`; and `dim ≤ edim`. -/

open Ideal IsLocalRing

namespace InfraSmoothDim

/-! ## §0 Copied from `MaxHeight.lean` and `CotQuot.lean` -/

theorem height_isMaximal_mvPolynomial (k : Type*) [Field k] :
    ∀ (ι : Type) [Finite ι] (M : Ideal (MvPolynomial ι k)) [M.IsMaximal],
      M.height = Nat.card ι := by
  intro ι _
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
    intro M _
    have e' := (MvPolynomial.renameEquiv k e).toRingEquiv
    have : (M.map e'.symm).IsMaximal := map_isMaximal_of_equiv e'.symm
    rw [← e'.symm.height_map M, H, Nat.card_congr e]
  | h_empty =>
    intro M _
    have h1 := Ideal.height_le_ringKrullDim_of_ne_top (I := M) IsPrime.ne_top'
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
      at h1
    simp only [Nat.card_of_isEmpty, CharP.cast_eq_zero, add_zero] at h1
    simp only [Nat.card_of_isEmpty, CharP.cast_eq_zero]
    exact_mod_cast nonpos_iff_eq_zero.mp (by exact_mod_cast h1)
  | @h_option α _ IH =>
    intro M _
    let e := (MvPolynomial.optionEquivLeft k α).toRingEquiv
    let P := M.map e
    have : P.IsMaximal := map_isMaximal_of_equiv e
    let p := P.comap (Polynomial.C : MvPolynomial α k →+* _)
    have : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have : P.LiesOver p := ⟨rfl⟩
    rw [← e.height_map M, Polynomial.height_eq_height_add_one p P, IH p]
    simp [Nat.card_eq_fintype_card, Fintype.card_option]

theorem spanFinrank_add_card_le {B C : Type*} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [CommRing C] [IsLocalRing C] (ψ : B →+* C)
    (hmap : (maximalIdeal B).map ψ = maximalIdeal C)
    {σ : Type*} [Fintype σ] (f : σ → maximalIdeal B)
    (hf : LinearIndependent (ResidueField B) (fun i => (maximalIdeal B).toCotangent (f i)))
    (hker : ∀ i, ψ (f i) = 0) :
    (maximalIdeal C).spanFinrank + Fintype.card σ ≤ (maximalIdeal B).spanFinrank := by
  classical
  set κ := ResidueField B
  set V := CotangentSpace B
  let v : σ → V := fun i => (maximalIdeal B).toCotangent (f i)
  let W : Submodule κ V := Submodule.span κ (Set.range v)
  have hW : Module.finrank κ W = Fintype.card σ := finrank_span_eq_card hf
  have hVW := Submodule.finrank_quotient_add_finrank W
  set d := Module.finrank κ (V ⧸ W)
  let b := Module.finBasis κ (V ⧸ W)
  have hsurj : Function.Surjective
      (fun x : maximalIdeal B => W.mkQ ((maximalIdeal B).toCotangent x)) :=
    (Submodule.mkQ_surjective W).comp (Ideal.toCotangent_surjective _)
  choose g hg using fun j : Fin d => hsurj (b j)
  -- the classes of `f` and `g` span `V`
  let s : Set (maximalIdeal B) := Set.range f ∪ Set.range g
  have hspan : Submodule.span κ ((maximalIdeal B).toCotangent '' s) = ⊤ := by
    have h1 : W ≤ Submodule.span κ ((maximalIdeal B).toCotangent '' s) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨f i, Or.inl ⟨i, rfl⟩, rfl⟩
    have h2 : (Submodule.span κ ((maximalIdeal B).toCotangent '' s)).map W.mkQ = ⊤ := by
      rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [← hg j]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨g j, Or.inr ⟨j, rfl⟩, rfl⟩)
    have := Submodule.comap_map_mkQ W (Submodule.span κ ((maximalIdeal B).toCotangent '' s))
    rw [h2, Submodule.comap_top, sup_eq_right.mpr h1] at this
    exact this.symm
  have hspanB : Submodule.span B s = ⊤ := (CotangentSpace.span_image_eq_top_iff).mp hspan
  have hmB : maximalIdeal B = Ideal.span (((↑) : maximalIdeal B → B) '' s) := by
    have := congrArg (Submodule.map (maximalIdeal B).subtype) hspanB
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at this
    exact this.symm
  have hmC : maximalIdeal C = Ideal.span (Set.range fun j => ψ (g j)) := by
    rw [← hmap, congrArg (Ideal.map ψ) hmB, Ideal.map_span]
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro _ ⟨_, ⟨x, hx | hx, rfl⟩, rfl⟩
      · obtain ⟨i, rfl⟩ := hx
        simp [hker i]
      · obtain ⟨j, rfl⟩ := hx
        exact Ideal.subset_span ⟨j, rfl⟩
    · rintro _ ⟨j, rfl⟩
      exact Ideal.subset_span ⟨_, ⟨g j, Or.inr ⟨j, rfl⟩, rfl⟩, rfl⟩
  have hle : (maximalIdeal C).spanFinrank ≤ d := by
    rw [hmC]
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := C)
      (Set.finite_range fun j => ψ (g j))
    refine this.trans ?_
    have h3 : (Set.range fun j => ψ (g j)).ncard ≤ Nat.card (Fin d) := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (Set.ncard_univ _).le
    rw [Nat.card_fin] at h3
    exact h3
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace B]
  change _ ≤ Module.finrank κ V
  omega

/-! ## §1 Derivatives vanish modulo `M` on `M²` -/

theorem derivation_mem_of_mem_sq {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) {M : Ideal A} {x : A} (hx : x ∈ M ^ 2) : D x ∈ M := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (M.mul_mem_right _ ha) (M.mul_mem_right _ hb)
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

/-! ## §2 The main theorem -/

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S]
variable {ι σ : Type} [Finite ι] [Finite σ]

/-- The class of a relation in the cotangent space of `k[x]_M`. -/
noncomputable def relCot (P : Algebra.SubmersivePresentation k S ι σ) (M : Ideal P.Ring)
    [M.IsMaximal] (hker : P.ker ≤ M) (i : σ) : maximalIdeal (Localization.AtPrime M) :=
  ⟨algebraMap P.Ring (Localization.AtPrime M) (P.relation i), by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (hker (P.relation_mem_ker i))⟩

theorem exists_residue_algebraMap_eq {R : Type*} [CommRing R] (M : Ideal R) [M.IsMaximal]
    (x : ResidueField (Localization.AtPrime M)) :
    ∃ a : R, residue _ (algebraMap R (Localization.AtPrime M) a) = x := by
  obtain ⟨y, hy⟩ :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal M (Localization.AtPrime M)).surjective x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk] at hy
  exact ⟨a, hy⟩

omit [Finite ι] in
theorem jacobiMatrix_det_notMem [Fintype σ] [DecidableEq σ]
    (P : Algebra.SubmersivePresentation k S ι σ) (M : Ideal P.Ring)
    [M.IsMaximal] (hker : P.ker ≤ M) : P.jacobiMatrix.det ∉ M := by
  intro hdet
  have hu := P.jacobian_isUnit
  rw [P.jacobian_eq_jacobiMatrix_det] at hu
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  obtain ⟨a', rfl⟩ := P.algebraMap_surjective u
  have h1 : P.jacobiMatrix.det * a' - 1 ∈ M := hker (by
    show _ ∈ RingHom.ker (algebraMap P.Ring S)
    rw [RingHom.mem_ker, map_sub, map_mul, hu, map_one, sub_self])
  have h2 : P.jacobiMatrix.det * a' ∈ M := M.mul_mem_right _ hdet
  have : (1 : P.Ring) ∈ M := by simpa using M.sub_mem h2 h1
  exact (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one M).mpr this)

omit [Finite ι] in
/-- If `∑ aᵢ fᵢ ∈ M²` then every `aᵢ ∈ M` (differentiate and invert the Jacobian mod `M`). -/
theorem coeffs_mem_of_sum_mem_sq [Fintype σ] [DecidableEq σ]
    (P : Algebra.SubmersivePresentation k S ι σ) (M : Ideal P.Ring) [M.IsMaximal]
    (hker : P.ker ≤ M) (a : σ → P.Ring) (hy2 : ∑ i, a i * P.relation i ∈ M ^ 2) :
    ∀ i, a i ∈ M := by
  have hrM : ∀ i, P.relation i ∈ M := fun i => hker (P.relation_mem_ker i)
  have hder : ∀ j : σ, ∑ i, a i * MvPolynomial.pderiv (P.map j) (P.relation i) ∈ M := by
    intro j
    have h1 := derivation_mem_of_mem_sq (MvPolynomial.pderiv (P.map j)) hy2
    have h2 : MvPolynomial.pderiv (P.map j) (∑ i, a i * P.relation i) =
        ∑ i, a i * MvPolynomial.pderiv (P.map j) (P.relation i)
        + ∑ i, P.relation i * MvPolynomial.pderiv (P.map j) (a i) := by
      simp only [map_sum, Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
    rw [h2] at h1
    have h3 : ∑ i, P.relation i * MvPolynomial.pderiv (P.map j) (a i) ∈ M :=
      Ideal.sum_mem _ fun i _ => M.mul_mem_right _ (hrM i)
    have := M.sub_mem h1 h3
    rwa [add_sub_cancel_right] at this
  let _ : Field (P.Ring ⧸ M) := Ideal.Quotient.field M
  let J := P.jacobiMatrix.map (Ideal.Quotient.mk M)
  have hJ : J.det ≠ 0 := by
    rw [show J.det = Ideal.Quotient.mk M P.jacobiMatrix.det from (RingHom.map_det _ _).symm,
      Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact jacobiMatrix_det_notMem P M hker
  have hv : Matrix.mulVec J (fun i => Ideal.Quotient.mk M (a i)) = 0 := by
    ext j
    simp only [Matrix.mulVec, dotProduct, J, Matrix.map_apply, Pi.zero_apply]
    rw [← Ideal.Quotient.eq_zero_iff_mem.mpr (hder j), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [P.jacobiMatrix_apply, map_mul, mul_comm]
  have := Matrix.eq_zero_of_mulVec_eq_zero hJ hv
  intro i
  have hi := congrFun this i
  rwa [Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at hi

omit [Finite ι] in
/-- A relation among the cotangent classes, with coefficients lifted to `k[x]`, gives an element
`∑ aᵢ fᵢ` of `M²`. -/
theorem sum_mem_sq_of_cotangent [Fintype σ]
    (P : Algebra.SubmersivePresentation k S ι σ) (M : Ideal P.Ring) [M.IsMaximal]
    (hker : P.ker ≤ M) (a : σ → P.Ring)
    (hc : ∑ i, algebraMap P.Ring (Localization.AtPrime M) (a i) •
      (maximalIdeal (Localization.AtPrime M)).toCotangent (relCot P M hker i) = 0) :
    ∑ i, a i * P.relation i ∈ M ^ 2 := by
  rw [← IsLocalization.AtPrime.under_maximalIdeal_pow M (Localization.AtPrime M) 2,
    Ideal.mem_comap]
  simp_rw [← map_smul, ← map_sum, Ideal.toCotangent_eq_zero] at hc
  convert hc using 1
  rw [Submodule.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, smul_eq_mul, map_mul]
  rfl

omit [Finite ι] in
/-- The relations of a submersive presentation have linearly independent classes in the cotangent
space of `k[x]_M`, for any maximal ideal `M ⊇ ker (k[x] → S)`. -/
theorem linearIndependent_relCot (P : Algebra.SubmersivePresentation k S ι σ) (M : Ideal P.Ring)
    [M.IsMaximal] (hker : P.ker ≤ M) :
    LinearIndependent (ResidueField (Localization.AtPrime M))
      (fun i => (maximalIdeal (Localization.AtPrime M)).toCotangent (relCot P M hker i)) := by
  classical
  have := Fintype.ofFinite σ
  rw [Fintype.linearIndependent_iff]
  intro c hc
  choose a ha using exists_residue_algebraMap_eq M
  have hc' : ∑ i, algebraMap P.Ring (Localization.AtPrime M) (a (c i)) •
      (maximalIdeal (Localization.AtPrime M)).toCotangent (relCot P M hker i) = 0 := by
    rw [← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul (ResidueField (Localization.AtPrime M)), ResidueField.algebraMap_eq,
      ha (c i)]
  have hmem := coeffs_mem_of_sum_mem_sq P M hker (fun i => a (c i))
    (sum_mem_sq_of_cotangent P M hker _ hc')
  intro i
  rw [← ha (c i), residue_eq_zero_iff, ← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.mem_map_of_mem _ (hmem i)

/-! ## §3 Dimension and embedding dimension of `S_𝔪` -/

/-- **Main algebraic theorem.** For a submersive presentation `P` of `S` over a field `k` and a
maximal ideal `𝔪` of `S`: `dim S_𝔪 = P.dimension` and `𝔪 S_𝔪` is spanned by `P.dimension`
elements (and no fewer). -/
theorem ringKrullDim_and_spanFinrank_localization (P : Algebra.SubmersivePresentation k S ι σ)
    (m : Ideal S) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = P.dimension ∧
      (maximalIdeal (Localization.AtPrime m)).spanFinrank = P.dimension := by
  classical
  have := Fintype.ofFinite σ
  have hφs : Function.Surjective (algebraMap P.Ring S) := P.algebraMap_surjective
  have hkerφ : ∀ x ∈ P.ker, algebraMap P.Ring S x = 0 := fun x hx => hx
  obtain ⟨M, hMdef⟩ : ∃ M, M = m.comap (algebraMap P.Ring S) := ⟨_, rfl⟩
  have : M.IsMaximal := hMdef ▸ Ideal.comap_isMaximal_of_surjective _ hφs
  have hker : P.ker ≤ M := fun x hx => by
    rw [hMdef, Ideal.mem_comap, hkerφ x hx]
    exact m.zero_mem
  have : IsNoetherianRing S := isNoetherianRing_of_surjective _ _ _ hφs
  -- lower bound (Krull's height theorem)
  have hM : M.height = Nat.card ι := height_isMaximal_mvPolynomial k ι M
  have hK := Ideal.height_le_height_add_spanFinrank_of_le hker
  have hspan : P.ker.spanFinrank ≤ Nat.card σ := by
    rw [← P.span_range_relation_eq_ker]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
    rw [← Set.image_univ]
    exact (Set.ncard_image_le Set.finite_univ).trans (Set.ncard_univ _).le
  have hquot : (M.map (Ideal.Quotient.mk P.ker)).height = m.height := by
    let e : (P.Ring ⧸ P.ker) ≃+* S := RingHom.quotientKerEquivOfSurjective hφs
    refine (e.height_map _).symm.trans (congrArg Ideal.height ?_)
    change Ideal.map (e : P.Ring ⧸ P.ker →+* S) _ = m
    rw [Ideal.map_map]
    have : (e : P.Ring ⧸ P.ker →+* S).comp (Ideal.Quotient.mk P.ker) = algebraMap P.Ring S :=
      RingHom.ext fun x => RingHom.quotientKerEquivOfSurjective_apply_mk hφs x
    rw [this, hMdef, Ideal.map_comap_of_surjective _ hφs]
  rw [hquot, hM] at hK
  have hdimC : ringKrullDim (Localization.AtPrime m) = m.height :=
    IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)
  -- upper bound (embedding dimension)
  let ψ := Localization.localRingHom M m (algebraMap P.Ring S) hMdef
  have hcomp : ψ.comp (algebraMap P.Ring (Localization.AtPrime M)) =
      (algebraMap S (Localization.AtPrime m)).comp (algebraMap P.Ring S) := by
    ext x
    · exact Localization.localRingHom_to_map M m _ hMdef _
    · exact Localization.localRingHom_to_map M m _ hMdef _
  have hmap : (maximalIdeal (Localization.AtPrime M)).map ψ =
      maximalIdeal (Localization.AtPrime m) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_map, hcomp, ← Ideal.map_map, hMdef, Ideal.map_comap_of_surjective _ hφs]
  have hkill : ∀ i, ψ (relCot P M hker i) = 0 := by
    intro i
    change ψ (algebraMap P.Ring (Localization.AtPrime M) (P.relation i)) = 0
    rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply, hkerφ _ (P.relation_mem_ker i), map_zero]
  have hU := spanFinrank_add_card_le ψ hmap (relCot P M hker) (linearIndependent_relCot P M hker)
    hkill
  have hB : ((maximalIdeal (Localization.AtPrime M)).spanFinrank : WithBot ℕ∞) = Nat.card ι := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal,
      IsLocalization.AtPrime.ringKrullDim_eq_height M (Localization.AtPrime M), hM]
    rfl
  have hB' : (maximalIdeal (Localization.AtPrime M)).spanFinrank = Nat.card ι := by
    exact_mod_cast hB
  have hle := ringKrullDim_le_spanFinrank_maximalIdeal (Localization.AtPrime m)
  rw [hdimC] at hle
  have hle' : m.height ≤ ((maximalIdeal (Localization.AtPrime m)).spanFinrank : ℕ∞) := by
    exact_mod_cast hle
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle')
  rw [← hh] at hle' hK
  rw [hB', Fintype.card_eq_nat_card] at hU
  rw [hdimC, ← hh]
  simp only [Algebra.Presentation.dimension]
  have hK' : Nat.card ι ≤ h + P.ker.spanFinrank := by exact_mod_cast hK
  have hle'' : h ≤ (maximalIdeal (Localization.AtPrime m)).spanFinrank := by exact_mod_cast hle'
  constructor
  · have : h = Nat.card ι - Nat.card σ := by omega
    rw [this]; rfl
  · omega

end InfraSmoothDim


/-! ## §4 Scheme stalks (task infra-smooth-dim) -/

namespace InfraSmoothDim

open CategoryTheory AlgebraicGeometry

/-- The algebraic theorem over a base ring that is a field (without a `Field` instance). -/
theorem ringKrullDim_and_spanFinrank_of_isField {R S : Type*} [CommRing R] [CommRing S]
    (hR : IsField R) (φ : R →+* S) (n : ℕ) (h : φ.IsStandardSmoothOfRelativeDimension n)
    (m : Ideal S) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = n ∧
      (maximalIdeal (Localization.AtPrime m)).spanFinrank = n := by
  let _ := hR.toField
  let _ := φ.toAlgebra
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    (h : @Algebra.IsStandardSmoothOfRelativeDimension n R S _ _ φ.toAlgebra).out
  rw [← hP]
  exact ringKrullDim_and_spanFinrank_localization P m

/-- Sections of `Spec K` over a nonempty open form a field. -/
theorem isField_sections_spec (K : Type*) [Field K] (U : (Spec (CommRingCat.of K)).Opens)
    (hU : (U : Set (Spec (CommRingCat.of K))).Nonempty) :
    IsField Γ(Spec (CommRingCat.of K), U) := by
  have hUt : U = ⊤ := by
    obtain ⟨z, hz⟩ := hU
    refine eq_top_iff.mpr fun y _ => ?_
    have : Subsingleton (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rwa [Subsingleton.elim y z]
  subst hUt
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)

/-- **Local form.** If `f : X → Spec K` is standard smooth of relative dimension `n` on an affine
chart `V → U` containing a closed point `x`, then `dim 𝒪_{X,x} = n` and `𝔪_x` is spanned by `n`
elements (so `dim_{κ(x)} 𝔪_x/𝔪_x² = n`). -/
theorem stalk_dim_of_chart {K : Type*} [Field K] {X : Scheme} (f : X ⟶ Spec (CommRingCat.of K))
    {U : (Spec (CommRingCat.of K)).Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) (n : ℕ)
    (h : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom)
    (x : X) (hxV : x ∈ V) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = n ∧
      (maximalIdeal (X.presheaf.stalk x)).spanFinrank = n := by
  have hR := isField_sections_spec K U ⟨f.base x, e hxV⟩
  have hmax := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  obtain ⟨h1, h2⟩ := ringKrullDim_and_spanFinrank_of_isField hR _ n h
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  let eq : Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal ≃+* X.presheaf.stalk x :=
    (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl _ _).toRingEquiv
  constructor
  · rw [← ringKrullDim_eq_of_ringEquiv eq, h1]
  · rw [← map_ringEquiv_maximalIdeal eq, Ideal.spanFinrank_map_eq_of_ringEquiv, h2]

/-- **Smooth of relative dimension `n` over a field.** At every closed point, the local ring has
Krull dimension `n` and embedding dimension `n` (it is a regular local ring of dimension `n`). -/
theorem stalk_dim_of_smoothOfRelativeDimension {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = n ∧
      (maximalIdeal (X.presheaf.stalk x)).spanFinrank = n := by
  obtain ⟨U, hU, V, hV, hxV, e, h⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  exact stalk_dim_of_chart f hU hV e n h x hxV hx

/-- **Smooth over a field.** At every closed point, the local ring is regular: its Krull dimension
equals its embedding dimension, and both equal the relative dimension of a standard smooth chart
around the point. -/
theorem exists_stalk_dim_of_smooth {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ n : ℕ, ringKrullDim (X.presheaf.stalk x) = n ∧
      (maximalIdeal (X.presheaf.stalk x)).spanFinrank = n := by
  obtain ⟨U, hU, V, hV, hxV, e, h⟩ := Smooth.exists_isStandardSmooth f x
  let _ := (f.appLE U V e).hom.toAlgebra
  have h' : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of K), U) Γ(X, V) := h
  have := h'.out
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := this
  exact ⟨P.dimension, stalk_dim_of_chart f hU hV e P.dimension
    (P.isStandardSmoothOfRelativeDimension rfl) x hxV hx⟩

/-- **Chart form.** Around every point of a smooth `K`-scheme there is an open set `V` and an
`n` such that every closed point of `V` has local ring of dimension and embedding dimension `n`. -/
theorem exists_nbhd_stalk_dim {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] (x : X) :
    ∃ (V : X.Opens) (n : ℕ), x ∈ V ∧ ∀ y ∈ V, IsClosed ({y} : Set X) →
      ringKrullDim (X.presheaf.stalk y) = n ∧
        (maximalIdeal (X.presheaf.stalk y)).spanFinrank = n := by
  obtain ⟨U, hU, V, hV, hxV, e, h⟩ := Smooth.exists_isStandardSmooth f x
  let _ := (f.appLE U V e).hom.toAlgebra
  have h' : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of K), U) Γ(X, V) := h
  have := h'.out
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := this
  exact ⟨V, P.dimension, hxV, fun y hy hyc => stalk_dim_of_chart f hU hV e P.dimension
    (P.isStandardSmoothOfRelativeDimension rfl) y hy hyc⟩

/-- On an irreducible smooth `K`-scheme all closed points have local rings of the same
dimension. -/
theorem stalk_dim_eq_of_closed {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] [IrreducibleSpace X]
    (z w : X) (hz : IsClosed ({z} : Set X)) (hw : IsClosed ({w} : Set X)) :
    ringKrullDim (X.presheaf.stalk z) = ringKrullDim (X.presheaf.stalk w) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨Vz, nz, hzV, hz'⟩ := exists_nbhd_stalk_dim f z
  obtain ⟨Vw, nw, hwV, hw'⟩ := exists_nbhd_stalk_dim f w
  have hne : ((Vz : Set X) ∩ Vw).Nonempty :=
    nonempty_preirreducible_inter Vz.2 Vw.2 ⟨z, hzV⟩ ⟨w, hwV⟩
  obtain ⟨u, ⟨huz, huw⟩, hu⟩ :=
    nonempty_inter_closedPoints hne (Vz.2.inter Vw.2).isLocallyClosed
  rw [(hz' z hzV hz).1, (hw' w hwV hw).1, ← (hz' u huz hu).1, (hw' u huw hu).1]

/-- **Dimension of an irreducible smooth `K`-scheme.** Its dimension equals the Krull dimension of
the local ring at any closed point, which equals the embedding dimension there. -/
theorem topologicalKrullDim_eq_of_smooth {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] [IrreducibleSpace X]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    topologicalKrullDim X = ringKrullDim (X.presheaf.stalk x) ∧
      ((maximalIdeal (X.presheaf.stalk x)).spanFinrank : WithBot ℕ∞) =
        ringKrullDim (X.presheaf.stalk x) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨n, hn1, hn2⟩ := exists_stalk_dim_of_smooth f x hx
  refine ⟨?_, by rw [hn1, hn2]⟩
  have hdim : topologicalKrullDim X = Order.krullDim X :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
  rw [hdim]
  refine le_antisymm ?_ ?_
  · rw [Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun y => ?_
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := closure ({y} : Set X))
      ⟨y, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    have hyz : z ≤ y := specializes_iff_mem_closure.mpr hz
    calc (Order.coheight y : WithBot ℕ∞) ≤ Order.coheight z := by
          exact_mod_cast Order.coheight_anti hyz
      _ = ringKrullDim (X.presheaf.stalk z) := (ringKrullDim_stalk_eq_coheight z).symm
      _ = ringKrullDim (X.presheaf.stalk x) := stalk_dim_eq_of_closed f z x hzc hx
      _ = ringKrullDim (X.presheaf.stalk x) := rfl
  · rw [ringKrullDim_stalk_eq_coheight]
    exact Order.coheight_le_krullDim x


/-! ### Corollaries: regularity, cotangent dimension, rational points, dimension of `X` -/

/-- **Smooth over a field ⇒ regular at closed points.** -/
theorem isRegularLocalRing_stalk_of_smooth {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] (x : X) (hx : IsClosed ({x} : Set X)) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨n, h1, h2⟩ := exists_stalk_dim_of_smooth f x hx
  exact (isRegularLocalRing_iff _).mpr (by rw [h1, h2])

/-- **Cotangent space at a closed point.** If `X → Spec K` is smooth of relative dimension `n`
and `x` is a closed point, then `dim_{κ(x)} 𝔪_x/𝔪_x² = n`. -/
theorem finrank_cotangentSpace_of_smoothOfRelativeDimension {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    Module.finrank (ResidueField (X.presheaf.stalk x)) (CotangentSpace (X.presheaf.stalk x)) =
      n := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact (stalk_dim_of_smoothOfRelativeDimension f n x hx).2

/-- The image of a `K`-point (a section of `X → Spec K`) is a closed point. -/
theorem isClosed_of_section {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (p : Spec (CommRingCat.of K)) : IsClosed ({s.base p} : Set X) := by
  have := isClosedImmersion_of_comp_eq_id (Y := Spec (CommRingCat.of K)) f s hs
  have hr : Set.range s.base = {s.base p} := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      have : Subsingleton (PrimeSpectrum K) := inferInstance
      exact congrArg _ (Subsingleton.elim (α := PrimeSpectrum K) a p)
    · rintro rfl
      exact ⟨_, rfl⟩
  rw [← hr]
  exact s.isClosedEmbedding.isClosed_range

/-- **Cotangent space at a rational point.** If `X → Spec K` is smooth of relative dimension `n`
and `s` is a `K`-point, then the local ring at `s` has dimension `n` and its cotangent space
`𝔪/𝔪²` has dimension `n` over the residue field. -/
theorem stalk_dims_of_section {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _) (p : Spec (CommRingCat.of K)) :
    ringKrullDim (X.presheaf.stalk (s.base p)) = n ∧
      Module.finrank (ResidueField (X.presheaf.stalk (s.base p)))
        (CotangentSpace (X.presheaf.stalk (s.base p))) = n :=
  ⟨(stalk_dim_of_smoothOfRelativeDimension f n _ (isClosed_of_section f s hs p)).1,
    finrank_cotangentSpace_of_smoothOfRelativeDimension f n _ (isClosed_of_section f s hs p)⟩

/-- **Dimension of an irreducible smooth `K`-scheme of relative dimension `n`** is `n`. -/
theorem topologicalKrullDim_eq_of_smoothOfRelativeDimension {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    [IrreducibleSpace X] : topologicalKrullDim X = n := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : Nonempty X := IrreducibleSpace.toNonempty
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set X))
    Set.univ_nonempty isClosed_univ.isLocallyClosed
  rw [(topologicalKrullDim_eq_of_smooth f x hx).1,
    (stalk_dim_of_smoothOfRelativeDimension f n x hx).1]

end InfraSmoothDim


/-! ## §6 curve-facts with C1b discharged (task infra-smooth-dim) -/

namespace LeafQM.AV.Pin
open CategoryTheory AlgebraicGeometry

/-- **`SmoothStalkDimOne` (C1b) holds** (curve-facts' statement, defined above). -/
theorem smoothStalkDimOne : SmoothStalkDimOne := by
  intro K _ X f hf x hx
  have := (InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension f 1 x hx).1
  rw [this, Nat.cast_one]

/-- **C1a holds**: a smooth curve over a field has no isolated point. -/
theorem smoothCurveNoIsolatedPoint : SmoothCurveNoIsolatedPoint :=
  smoothCurveNoIsolatedPoint_of smoothStalkDimOne

/-- **C1 holds**: each geometric component of a proper smooth curve over `ℚ` has infinitely many
`ℚ̄`-points. -/
theorem geomCompInfinite : GeomCompInfinite :=
  geomCompInfinite_of smoothCurveNoIsolatedPoint

/-- **Both curve facts from C2K and C3K alone.** -/
theorem curveFacts_of_C2K_C3K (h2 : ConstOrOntoAlgClosed) (h3 : RatFactorAlgClosed) :
    CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_leaves smoothStalkDimOne h2 h3

end LeafQM.AV.Pin

#print axioms LeafQM.AV.Pin.smoothStalkDimOne
#print axioms LeafQM.AV.Pin.smoothCurveNoIsolatedPoint
#print axioms LeafQM.AV.Pin.geomCompInfinite
#print axioms LeafQM.AV.Pin.curveFacts_of_C2K_C3K
