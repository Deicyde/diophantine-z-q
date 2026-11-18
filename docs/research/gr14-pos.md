# Gaudron–Rémond Theorem 1.4 as printed: dimension at least one

The open hypothesis `OpenResearchLeaves65.gaudronRemondThm14AnSS`
(`ZInQ.SemistabAssembly.GaudronRemondThm14AnSS`) states Gaudron–Rémond, *Polarisations et isogénies*,
Duke Math. J. 163 (2014), 2057–2108, Théorème 1.4 (p. 2060), for every dimension `g : ℕ`. The paper assumes
`g ≥ 1` throughout (p. 2058), so for `g = 0` the leaf says something the print does not.

`ZInQKernel/Contrib/OneProof/GaudronRemondThm14Pos.lean` adds the leaf

* `ZInQ.SemistabAssembly.GaudronRemondThm14AnSSPos`: the statement of `GaudronRemondThm14AnSS` verbatim,
  with the extra hypothesis `1 ≤ g` (checked by `Iff.rfl` against the old statement with that hypothesis
  inserted),

and proves

* `ZInQ.SemistabAssembly.gaudronRemondThm14AnSS_of_pos : GaudronRemondThm14AnSSPos → GaudronRemondThm14AnSS`.

For `g ≥ 1` the new leaf applies. For `g = 0` the conclusion is proved outright: `grKappa 0 d x = 1`; an
abelian variety of dimension 0 is integral and locally Artinian, so its underlying space is one point; an
isogeny is surjective, so the target is one point too; the unit section then shows that both structure
morphisms are isomorphisms; the trivial homomorphisms in both directions are isomorphisms, hence isogenies,
and their kernels on geometric points are subsingletons, so their degrees are at most 1.

## Checks

* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  +ZInQKernel.Contrib.OneProof.GaudronRemondThm14Pos`: built (16545 jobs).
* `#print axioms ZInQ.SemistabAssembly.gaudronRemondThm14AnSS_of_pos`: `[propext, Classical.choice, Quot.sound]`.
* `#discharges` (35 open hypotheses, 15016 theorems checked):

```
DISCHARGES [OpenResearchLeaves65.gaudronRemondThm14AnSS] by ZInQ.SemistabAssembly.gaudronRemondThm14AnSS_of_pos
  still assumes: [ZInQ.SemistabAssembly.GaudronRemondThm14AnSSPos]
  axioms: [propext, Classical.choice, Quot.sound]
```

## Reading behind the leaf

An independent reading of the typeset journal copy (AI-READ, 2026-11-18): for `g ≥ 1` the Lean statement is
Théorème 1.4 with the base field `k = K` (quantifiers, a pair of isogenies one in each direction each of degree
at most `κ(A)` (p. 2059), the definitions of isogeny and degree (p. 2062), and
`κ(A) = ((14g)^{64g²}[k:ℚ]·max(h_F(A), log[k:ℚ], 1)²)^{2^{10} g³}` (p. 2058) all match). The height is the stable
Faltings height with Faltings' original normalization, which is the metric of the Lean statement. The
semistability hypothesis of the Lean statement implies the paper's semi-abelian reduction, so it cannot make the
leaf stronger than the print.

The new leaf enters kinds.tsv flagged unread (locator row "R19 (g ≥ 1)" in `docs/research/locators.md`).
