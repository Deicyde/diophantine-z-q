import ZInQKernel.OneProof.H.TailY
import ZInQKernel.Contrib.OneProof.GR14Narrow.Chain

/-! # gr14-narrow, leaf helper: Gaudron-Rémond's isogeny theorem, forward direction

Task gr14-narrow (docs/research/gr14-narrow.md). The research field `gaudronRemondThm14` (bundle
`HDec.HSyn.OpenResearchLeaves22`, row R19, statement `ZInQ.HeightSplit.GaudronRemondThm14`, TailY L834) gives
isogenies of degree `≤ κ` in both directions. The chain uses the reverse direction only for the existence of an
isogeny `B → A` (`isogenyReverseExists_of_r19`, TailA L945), which `GapGR.isogenyReverseExists_of_weil` (Chain.lean)
supplies from the quasi-inverse leaf. This module states the forward direction alone:

* `GapGR.GaudronRemondThm14Fwd` (LEAF, the weaker statement that replaces the field);
* `GapGR.gaudronRemondThm14Fwd_of_field : ZInQ.HeightSplit.GaudronRemondThm14 → GaudronRemondThm14Fwd` (proved);
* `GapGR.r19Fwd_of_leaves`: `R19Fwd` (kernel height) from the leaf and the identification leaves N1, SS1, SS2, as
  `ZInQ.HeightSplit.r19_of_leaves` (TailY L842) does for R19.

It imports only `TailY` and `Chain`, so that the bundle files (`TailZ4` and later, which import both) can import it.
-/

set_option linter.all false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace GapGR

open ZInQ.HeightSplit

/-- **LEAF (R19-GR, forward direction; published form).** Gaudron–Rémond, *Polarisations et isogénies*, Duke Math.
J. 163 (2014), no. 11, Théorème 1.4 (p. 2060; `κ(A)` and `α(g) = 1024g³` defined p. 2058; locators as read by the
locator audit and recorded in the field's docstring, TailY L828-L833; the title and issue are UNVERIFIED, from
memory): for abelian varieties `A`, `B` over a number field `K`, with `A` of dimension `g` and stable Faltings
height `h(A) = x` (Faltings' original normalization, `IsStableFaltingsHeight`), if `A` and `B` are isogenous then
there is an isogeny `A → B` of degree `≤ κ(A) = ((14g)^{64g²}·[K:ℚ]·max(h(A), log[K:ℚ], 1)²)^{1024g³}`
(`grKappa`, HDecomp/Faltings/Leaves.lean L52).

**Never stronger than the printed theorem, nor than the field it replaces.** It is, verbatim, the first conjunct of
the current field `ZInQ.HeightSplit.GaudronRemondThm14` (`gaudronRemondThm14Fwd_of_field`, proved below), whose
statement is the printed one with the kernel's objects. It drops the second conjunct (an isogeny `B → A` of degree
`≤ κ(A)`), which is the only part of the field subject to the reading question whether the printed reverse bound is
`κ(A)` or `κ(B)`: the forward bound `deg(A → B) ≤ κ(A)` is the theorem's main assertion under either reading. -/
def GaudronRemondThm14Fwd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ),
    A.dim = (g : WithBot ℕ∞) → IsStableFaltingsHeight A x →
    (∃ φ : A.X ⟶ B.X, ZInQ.DefFaltings.IsIsogeny φ) →
    ∃ φ : A.X ⟶ B.X, ZInQ.DefFaltings.IsIsogeny φ ∧
      (ZInQ.DefFaltings.isogDeg φ : ℝ) ≤ ZInQ.DefFaltings.grKappa g (Module.finrank ℚ K) x

/-- **The current field implies the forward leaf (proved).** -/
theorem gaudronRemondThm14Fwd_of_field (h : ZInQ.HeightSplit.GaudronRemondThm14) : GaudronRemondThm14Fwd :=
  fun K _ _ A B g x hg hx hiso => (h K A B g x hg hx hiso).1

/-- **`R19Fwd` from the forward leaf and N1, SS1, SS2 (proved)**: `ZInQ.HeightSplit.r19_of_leaves` (TailY L842),
the same proof, for the forward half. -/
theorem r19Fwd_of_leaves (hGR : GaudronRemondThm14Fwd) (hN1 : ZInQ.H5Neron.NeronModelExists)
    (hSS1 : SemistableReductionThm) (hSS2 : SemistableNeronBaseChange) : R19Fwd :=
  fun K _ _ A B g x hg hx hiso =>
    hGR K A B g x hg ((isStableFaltingsHeight_iff hN1 hSS1 hSS2 A x).mpr hx) hiso

/-- **Consistency check (proved):** the old route and the new route agree: `r19_of_leaves` followed by
`r19Fwd_of_r19` is `r19Fwd_of_leaves` after `gaudronRemondThm14Fwd_of_field` (both are proofs of a `Prop`). -/
theorem r19Fwd_of_leaves_of_field (hGR : ZInQ.HeightSplit.GaudronRemondThm14)
    (hN1 : ZInQ.H5Neron.NeronModelExists) (hSS1 : SemistableReductionThm)
    (hSS2 : SemistableNeronBaseChange) :
    r19Fwd_of_r19 (r19_of_leaves hGR hN1 hSS1 hSS2) =
      r19Fwd_of_leaves (gaudronRemondThm14Fwd_of_field hGR) hN1 hSS1 hSS2 := rfl

end GapGR
