import ZInQKernel.HDecomp.QM.Pairs
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic

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


/-! # curve-glue additions (task curve-glue, 2026-11-13)

Everything above is `scratch/curve-facts/CurveFacts.lean` verbatim (its `#print axioms` lines
dropped). Below: `scratch/curve-glue/C2K.lean` §1-§4 (C2K from the leaf `GlobalFunctionsConst`)
and `scratch/curve-glue/C3K.lean` §1-§2 (C3K from the glue `ImagePlaneCurve` and Lean-proved
algebra), then the composite `curveFacts_of_glue`. -/

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

/-- A section whose value at every `K`-point of its domain is nonzero is a unit (Jacobson). -/
theorem isUnit_of_ev_ne_zero {O : X.Opens} (s : Γ(X, O))
    (h : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O, ev p hx s ≠ 0) :
    IsUnit s := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ O s fun x hx => ?_
  rw [← X.mem_basicOpen s x hx]
  by_contra hb
  obtain ⟨p, hp, hpO, hpb⟩ := exists_point_of_isLocallyClosed f
    (Z := (O : Set X) ∩ (X.basicOpen s : Set X)ᶜ)
    (O.isOpen.isLocallyClosed.inter (X.basicOpen s).isOpen.isClosed_compl.isLocallyClosed)
    ⟨x, hx, hb⟩
  exact h p hp hpO ((ev_eq_zero_iff p hpO s).2 hpb)

end Units

/-! ## §3 The leaf: global functions on a connected component are constant -/

/-- **(L) "Liouville": regular functions on a connected component of a proper smooth curve over
an algebraically closed field are constant** (up to nilpotents, which is weaker than the printed
statement). `X → Spec K` proper and smooth of relative dimension 1, `K` algebraically closed,
`W ⊆ X` open, closed and (pre)connected, `s ∈ Γ(W, 𝒪_X)`: then `s − c` is nilpotent for some
constant `c ∈ K` (the image of `c` under `K = Γ(Spec K) → Γ(X) → Γ(W)`).

Source (textbook leaf, STANDARD; numbering UNVERIFIED, recalled without network): `W` is a
proper connected `K`-scheme (an open and closed subscheme of a proper one), so `Γ(W, 𝒪_W)` is a
finite-dimensional `K`-algebra (finiteness of coherent cohomology for proper morphisms, EGA III
3.2.1; Hartshorne III.5.2 in the projective case) without nontrivial idempotents (`W`
connected), hence local Artinian with residue field `K` (`K` algebraically closed): every element
is a constant plus a nilpotent. With `W` reduced (smooth ⇒ reduced) this is the printed form
"`Γ(W, 𝒪_W) = K` for `W` proper, connected and reduced over `K = K̄`" (Stacks, Varieties, lemma
on `Γ` of a proper reduced connected scheme; Hartshorne Ex. II.4.5(d) for integral `W`; I.3.4
for projective varieties). Smoothness and dimension 1 are not needed; they are kept so that the
leaf is applied exactly where C2K is. Not in Mathlib v4.35 (no finiteness theorem for proper
morphisms). -/
def GlobalFunctionsConst : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ W : X.Opens, IsClopen (W : Set X) → _root_.IsPreconnected (W : Set X) →
      ∀ s : Γ(X, W), ∃ c : K, IsNilpotent (s - cst f W c)

section Main

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem ev_eq_of_nilpotent (f : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {s : Γ(X, W)} {c : K}
    (hN : IsNilpotent (s - cst f W c)) (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (hx : ptOf p ∈ W) : ev p hx s = c := by
  have h0 := (hN.map (ev p hx)).eq_zero
  rw [map_sub, ev_cst f p hp] at h0
  exact sub_eq_zero.mp h0

theorem res_cst (f : X ⟶ Spec (CommRingCat.of K)) {O O' : X.Opens} (h : O' ≤ O) (a : K) :
    res h (cst f O a) = cst f O' a := by
  rw [cst, cst, res_res]

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

/-- **The missed-value lemma.** If `σ` misses a value `t ∈ P¹(K)` on the `K`-points of a
connected component `W`, it is constant on them. For `t = ∞`, `W ⊆ U` (Jacobson) and `f|_W` is
constant by (L). For `t = a ∈ K`, `f − a` is a unit on `W ∩ U` and `1 − a g` on `W ∩ V`, and
`1/(f − a)`, `g/(1 − a g)` glue to `h ∈ Γ(W)`, constant `= c` by (L); `c ≠ 0` if `W ∩ U` has a
`K`-point, which forces `W ⊆ U` (`g = 0` off `U`) and `σ = a + 1/c` on `W`. -/
theorem constant_of_missed (hL : GlobalFunctionsConst) {K : Type} [Field K] [IsAlgClosed K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (hP : IsProper f)
    (hS : SmoothOfRelativeDimension 1 f) [JacobsonSpace X] (σ : ToP1 X) (W : X.Opens)
    (hWc : IsClopen (W : Set X)) (hWp : _root_.IsPreconnected (W : Set X)) (t : OnePoint K)
    (ht : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ptOf p ∈ W → σ.val p ≠ t) :
    ∃ v : OnePoint K, ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ptOf p ∈ W →
      σ.val p = v := by
  have : LocallyOfFiniteType f := inferInstance
  induction t using OnePoint.rec with
  | infty =>
    have hWU : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ptOf p ∈ W → ptOf p ∈ σ.U :=
      fun p hp hW => by
        by_contra h
        exact ht p hp hW (val_of_not_mem σ p h)
    have hle : W ≤ σ.U := by
      intro x hx
      by_contra hxU
      obtain ⟨p, hp, hpW, hpU⟩ := exists_point_of_isLocallyClosed f
        (Z := (W : Set X) ∩ (σ.U : Set X)ᶜ)
        (W.isOpen.isLocallyClosed.inter σ.U.isOpen.isClosed_compl.isLocallyClosed) ⟨x, hx, hxU⟩
      exact hpU (hWU p hp hpW)
    obtain ⟨c, hc⟩ := hL K X f hP hS W hWc hWp (res hle σ.f)
    refine ⟨OnePoint.some c, fun p hp hpW => ?_⟩
    rw [val_of_mem σ p (hle hpW), ← ev_res p hle hpW, ev_eq_of_nilpotent f hc p hp hpW]
  | coe a =>
    have hmiss : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ (hW : ptOf p ∈ W)
        (hU : ptOf p ∈ σ.U), ev p hU σ.f ≠ a := fun p hp hW hU e =>
      ht p hp hW (by rw [val_of_mem σ p hU, e])
    let O₁ : X.Opens := W ⊓ σ.U
    let O₂ : X.Opens := W ⊓ σ.V
    let u₁ : Γ(X, O₁) := res inf_le_right σ.f - cst f O₁ a
    let u₂ : Γ(X, O₂) := 1 - cst f O₂ a * res inf_le_right σ.g
    have hu₁ev : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O₁,
        ev p hx u₁ = ev p hx.2 σ.f - a := by
      intro p hp hx
      simp only [u₁, map_sub, ev_res, ev_cst f p hp]
    have hu₂ev : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O₂,
        ev p hx u₂ = 1 - a * ev p hx.2 σ.g := by
      intro p hp hx
      simp only [u₂, map_sub, map_one, map_mul, ev_res, ev_cst f p hp]
    have hu₁ : IsUnit u₁ := isUnit_of_ev_ne_zero f u₁ fun p hp hx => by
      rw [hu₁ev p hp hx]
      exact sub_ne_zero.mpr (hmiss p hp hx.1 hx.2)
    have hu₂ : IsUnit u₂ := isUnit_of_ev_ne_zero f u₂ fun p hp hx => by
      rw [hu₂ev p hp hx]
      by_cases hU : ptOf p ∈ σ.U
      · have e := ev_f_mul_g σ p hU hx.2
        have hne := hmiss p hp hx.1 hU
        intro h0
        have h1 : ev p hx.2 σ.g * (ev p hU σ.f - a) = 0 := by linear_combination h0 + e
        rcases mul_eq_zero.mp h1 with h | h
        · rw [h, mul_zero] at e; exact zero_ne_one e
        · exact hne (sub_eq_zero.mp h)
      · rw [ev_g_eq_zero σ p hx.2 hU, mul_zero, sub_zero]; exact one_ne_zero
    obtain ⟨i₁, hi₁⟩ := hu₁.exists_left_inv
    obtain ⟨i₂, hi₂⟩ := hu₂.exists_left_inv
    let s₂ : Γ(X, O₂) := res inf_le_right σ.g * i₂
    have hfg : res (show O₁ ⊓ O₂ ≤ σ.U from fun x hx => hx.1.2) σ.f *
        res (show O₁ ⊓ O₂ ≤ σ.V from fun x hx => hx.2.2) σ.g = 1 := by
      have e := congrArg (res (show O₁ ⊓ O₂ ≤ σ.U ⊓ σ.V from fun x hx => ⟨hx.1.2, hx.2.2⟩)) σ.inv
      rw [map_mul, map_one] at e
      rw [← e]
      simp only [res_res]
    have hcomp : res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) i₁ = res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) s₂ := by
      have A : res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) i₁ * res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) u₁ = 1 := by
        rw [← map_mul, hi₁, map_one]
      have C : res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) i₂ * res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) u₂ = 1 := by
        rw [← map_mul, hi₂, map_one]
      have B : res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) s₂ * res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) u₁ = 1 := by
        simp only [s₂, u₁, u₂, map_mul, map_sub, map_one, res_res, res_cst] at C hfg ⊢
        linear_combination C + res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) i₂ * hfg
      calc res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) i₁
          = res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) i₁ *
              (res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) s₂ * res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) u₁) := by
            rw [B, mul_one]
        _ = res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) s₂ *
              (res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) i₁ * res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) u₁) := by
            ring
        _ = res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) s₂ := by rw [A, mul_one]
    -- glue `i₁` and `s₂` to a section on `O₁ ⊔ O₂`
    let h : Γ(X, O₁ ⊔ O₂) := (X.sheaf.objSupIsoProdEqLocus O₁ O₂).inv ⟨(i₁, s₂), hcomp⟩
    have hh₁ : res (le_sup_left : O₁ ≤ O₁ ⊔ O₂) h = i₁ :=
      X.sheaf.objSupIsoProdEqLocus_inv_fst O₁ O₂ _
    have hh₂ : res (le_sup_right : O₂ ≤ O₁ ⊔ O₂) h = s₂ :=
      X.sheaf.objSupIsoProdEqLocus_inv_snd O₁ O₂ _
    have hW'eq : ((O₁ ⊔ O₂ : X.Opens) : Set X) = W := by
      ext x
      simp only [O₁, O₂, Opens.coe_sup, Opens.coe_inf, Set.mem_union, Set.mem_inter_iff,
        SetLike.mem_coe]
      constructor
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
      · intro hx
        by_cases hU : x ∈ σ.U
        · exact Or.inl ⟨hx, hU⟩
        · exact Or.inr ⟨hx, mem_V_of_not_mem_U σ hU⟩
    obtain ⟨c, hc⟩ := hL K X f hP hS (O₁ ⊔ O₂) (hW'eq ▸ hWc) (hW'eq ▸ hWp) h
    have hv₁ : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O₁,
        ev p hx i₁ = c := by
      intro p hp hx
      rw [← hh₁, ev_res]; exact ev_eq_of_nilpotent f hc p hp _
    have hv₂ : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O₂,
        ev p hx s₂ = c := by
      intro p hp hx
      rw [← hh₂, ev_res]; exact ev_eq_of_nilpotent f hc p hp _
    by_cases hex : ∃ q : Spec (CommRingCat.of K) ⟶ X, q ≫ f = 𝟙 _ ∧ ptOf q ∈ W ∧ ptOf q ∈ σ.U
    · obtain ⟨q, hq, hqW, hqU⟩ := hex
      have hc0 : c ≠ 0 := by
        intro hc0
        have e := congrArg (ev q (show ptOf q ∈ O₁ from ⟨hqW, hqU⟩)) hi₁
        rw [map_mul, map_one, hv₁ q hq, hc0, zero_mul] at e
        exact zero_ne_one e
      refine ⟨OnePoint.some (a + c⁻¹), fun p hp hpW => ?_⟩
      have hpU : ptOf p ∈ σ.U := by
        by_contra hpU
        have hpV := mem_V_of_not_mem_U σ hpU
        have e := hv₂ p hp (show ptOf p ∈ O₂ from ⟨hpW, hpV⟩)
        simp only [s₂, map_mul] at e
        rw [ev_res, ev_g_eq_zero σ p hpV hpU, zero_mul] at e
        exact hc0 e.symm
      rw [val_of_mem σ p hpU]
      congr 1
      have e1 := congrArg (ev p (show ptOf p ∈ O₁ from ⟨hpW, hpU⟩)) hi₁
      rw [map_mul, map_one, hv₁ p hp, hu₁ev p hp] at e1
      have e2 := eq_inv_of_mul_eq_one_right e1
      linear_combination e2
    · push Not at hex
      exact ⟨OnePoint.infty, fun p hp hpW => val_of_not_mem σ p (hex p hp hpW)⟩

/-- **C2K from the leaf (L).** -/
theorem constOrOntoAlgClosed_of (hL : GlobalFunctionsConst) : ConstOrOntoAlgClosed := by
  intro K _ _ X f hP hS σ p₀ hp₀
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := { }
  set x₀ := ptOf p₀ with hx₀
  let W : X.Opens := ⟨connectedComponent x₀, isOpen_connectedComponent_of_noetherian x₀⟩
  have hWc : IsClopen (W : Set X) := ⟨isClosed_connectedComponent, W.isOpen⟩
  have hWp : _root_.IsPreconnected (W : Set X) := isPreconnected_connectedComponent
  have memW : ∀ p : Spec (CommRingCat.of K) ⟶ X, ptOf p ∈ W ↔
      connectedComponent (ptOf p) = connectedComponent x₀ :=
    fun p => ⟨fun h => (connectedComponent_eq h).symm,
      fun h => by
        show ptOf p ∈ connectedComponent x₀
        rw [← h]; exact mem_connectedComponent⟩
  by_cases ho : ∀ t : OnePoint K, ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
      connectedComponent (ptOf p) = connectedComponent x₀ ∧ σ.val p = t
  · exact Or.inr ho
  · left
    push Not at ho
    obtain ⟨t, ht⟩ := ho
    obtain ⟨v, hv⟩ := constant_of_missed hL f hP hS σ W hWc hWp t
      (fun p hp hpW => ht p hp ((memW p).1 hpW))
    intro p hp hpc
    rw [hv p hp ((memW p).2 hpc), hv p₀ hp₀ (mem_connectedComponent : x₀ ∈ connectedComponent x₀)]

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


/-- **Both curve facts of mobius-glue from C1b (`SmoothStalkDimOne`, glue, task
infra-smooth-dim), the textbook leaf (L) `GlobalFunctionsConst` and the glue (G1)
`ImagePlaneCurve`.** -/
theorem curveFacts_of_glue (h1 : SmoothStalkDimOne) (hL : GlobalFunctionsConst)
    (hG : ImagePlaneCurve) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_leaves h1 (constOrOntoAlgClosed_of hL) (ratFactorAlgClosed_of hG)

end Pin

end AV

end LeafQM

end

#print axioms LeafQM.AV.Pin.constOrOntoAlgClosed_of
#print axioms LeafQM.AV.Pin.ratFactorAlgClosed_of
#print axioms LeafQM.AV.Pin.curveFacts_of_glue
