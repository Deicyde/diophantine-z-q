import ZInQKernel.OneProof.H.TailZ35
import ZInQKernel.Contrib.OneProof.GR14Narrow.Leaf

/-! # gr14-narrow: Gaudron-Rémond (R19, `gaudronRemondThm14`) narrowed to the forward direction

Task gr14-narrow (docs/research/gr14-narrow.md; re-triage triage2 §1, Task 6). No field is removed. The research
field `gaudronRemondThm14 : ZInQ.HeightSplit.GaudronRemondThm14` of `HDec.HSyn.OpenResearchLeaves22` (row R19)
asserts isogenies of degree `≤ κ(A)` in **both** directions. On the live path of `ZInQ.OneProof.frozenTarget`
(probe `scratch/gr14-narrow/Live.lean`) its second conjunct is read only for the **existence** of an isogeny
`B → A` (`HDec.HSyn.G0RevIsog.isogenyReverseExists_of_r19`, TailA L945, through `reverseIsogeny_of_leaves3`,
TailD L117, in `gluePieces_of_open4`, TailK L308). That existence follows from the quasi-inverse leaf
`milneIsogenyQuasiInverse` (`OpenAddedLeaves17`), so the field can be replaced by its first conjunct.

Exports (namespace `GapGR`):
* `GaudronRemondThm14Fwd` (LEAF; Leaf.lean): Gaudron–Rémond Thm 1.4, forward direction `A → B`, degree `≤ κ(A)`.
* `gaudronRemondThm14Fwd_of_field : ZInQ.HeightSplit.GaudronRemondThm14 → GaudronRemondThm14Fwd` (Leaf.lean), and
  `gaudronRemondThm14Fwd_of_open` below (from the bundle field).
* `isogenyReverseExists_of_milne : AvSplit.MilneIsogenyQuasiInverse → HDec.HSyn.G0RevIsog.IsogenyReverseExists`
  (below), and `isogenyReverseExists_of_open` (from the bundle field).
* For the fold (Chain.lean, Leaf.lean): `R19Fwd`, `r19Fwd_of_r19`, `r19Fwd_of_leaves`, `transfer_core_fwd`,
  `isogenyReverseExists_of_weil`, `reverseIsogeny_of_weil`; and below `reverseIsogeny_of_milne`,
  `isogenyReverseExists_of_milne_eq_weil` (the fold's route through `isogenyQuasiInverse_lf7` is this theorem).

Hypotheses: only the two bundle fields named above, and the chain's proved `HDec.HSyn.mulIsogeny_proved`.
-/

set_option linter.all false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace GapGR

/-- **Reverse isogenies from Milne's quasi-inverse (proved).** Over a number field, an isogeny `φ : A → B` of
abelian varieties has an isogeny `B → A` in the other direction: Milne's leaf gives `g : B → A` (a homomorphism)
and `d ≥ 1` with `φ ≫ g = [d]_A`, `g ≫ φ = [d]_B`; `[d]` is finite and surjective in characteristic `0`
(`HDec.HSyn.mulIsogeny_proved`, TailE L6376), hence so is `g` (`isIsogenyMor_of_comp_eq_mul`, Chain.lean; the end
of `end0Division_of_homFree`, TailA L1290-1327). The two copies `ZInQ.DefFaltings.AbVar` and `PkgI3.AbVar` are
identified by `HDec.LeafAdopt.abVarEquiv` (LPrefix L5286, the identity on `.X`). -/
theorem isogenyReverseExists_of_milne (hM : AvSplit.MilneIsogenyQuasiInverse) :
    HDec.HSyn.G0RevIsog.IsogenyReverseExists := by
  intro K _ _ A B φ hφ
  obtain ⟨hmon, hfin, hsurj⟩ := hφ
  let A' := HDec.LeafAdopt.abVarEquiv K A
  let B' := HDec.LeafAdopt.abVarEquiv K B
  let f : PkgI3.AbVar.Hom A' B' := @PkgI3.AbVar.Hom.mk' K _ A' B' φ hmon
  obtain ⟨d, hd, g, hfg, hgf⟩ := hM K A' B' f ⟨hfin, hsurj⟩
  rw [natCast_hom] at hfg hgf
  have hg := isIsogenyMor_of_comp_eq_mul HDec.HSyn.mulIsogeny_proved f.hom g.hom d hd hfg hgf
  exact ⟨g.hom, inferInstanceAs (IsMonHom g.hom), hg.1, hg.2⟩

/-- **`ReverseIsogeny` (G17 after Poincaré) from Milne's quasi-inverse (proved).** -/
theorem reverseIsogeny_of_milne (hM : AvSplit.MilneIsogenyQuasiInverse) : HDec.HSyn.G0Split.ReverseIsogeny :=
  HDec.HSyn.G0RevIsog.reverseIsogeny_of_exists (isogenyReverseExists_of_milne hM)

/-- **The fold's route (proved).** The fold reroutes `gluePieces_of_open4` (TailK L308), where only the `K̄`-point
form `l.isogenyQuasiInverse` is in scope; at the top it is `HDec.HSyn.isogenyQuasiInverse_lf7
l.milneIsogenyQuasiInverse` (TailX L255). This theorem records that the route gives the same statement from
Milne's leaf (both sides are proofs of a `Prop`). -/
theorem isogenyReverseExists_of_milne_eq_weil (hM : AvSplit.MilneIsogenyQuasiInverse) :
    isogenyReverseExists_of_milne hM =
      isogenyReverseExists_of_weil HDec.HSyn.mulIsogeny_proved (HDec.HSyn.isogenyQuasiInverse_lf7 hM) := rfl

/-! ## From the bundle fields -/

/-- **The forward leaf from the bundle field `gaudronRemondThm14` (proved).** -/
theorem gaudronRemondThm14Fwd_of_open (r : HDec.HSyn.OpenResearchLeaves22) : GaudronRemondThm14Fwd :=
  gaudronRemondThm14Fwd_of_field r.gaudronRemondThm14

/-- **Reverse isogenies from the bundle field `milneIsogenyQuasiInverse` (proved).** -/
theorem isogenyReverseExists_of_open (l : HDec.HSyn.OpenAddedLeaves17) :
    HDec.HSyn.G0RevIsog.IsogenyReverseExists :=
  isogenyReverseExists_of_milne l.milneIsogenyQuasiInverse

end GapGR
