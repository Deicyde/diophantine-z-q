# GR14Printed: the printed form of Gaudron–Rémond Thm 1.4 and its bridges

Add-only contribution for the row `gaudronRemondThm14AnSS`
(`ZInQ.SemistabAssembly.GaudronRemondThm14AnSS`, bundle `HDec.HSyn.OpenResearchLeaves78`). It proves
the two bridges the lane B readiness report lists between that field and a reading against
É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), Thm 1.4 (p. 2060).

## Files

| File | Content |
|---|---|
| `DimZero.lean` | **B1.** The field at `g = 0`, proved (`gr14_dim_zero`). A dimension-0 abelian variety is `Spec K`; an isogenous `B` is too; both isogenies have degree `≤ 1 = κ`. |
| `FiniteKernel.lean` | **B2.** `IsIsogenyPrinted` (homomorphism, surjective, kernel `A ×_{φ,B,e} Spec K` finite over `K`) and `isIsogenyPrinted_iff : IsIsogenyPrinted φ ↔ IsIsogeny φ`. |
| `Printed.lean` | `GaudronRemondThm14AnSSPos` (field with `1 ≤ g`), `GaudronRemondThm14Printed` (field with `1 ≤ g` and `IsIsogenyPrinted`), `gaudronRemondThm14AnSS_of_printed`, and the converse `gaudronRemondThm14Printed_iff`. |
| `Check.lean` | `#print axioms` for the main theorems. |

## What the printed form changes, and what it keeps

`GaudronRemondThm14Printed` is the field verbatim with two changes:

* `1 ≤ g` as a hypothesis (Duke p. 2058: "de dimension g ≥ 1"). This makes the statement weaker.
  The dropped case `g = 0` is proved in Lean (B1).
* `IsIsogeny` is replaced by `IsIsogenyPrinted` in the hypothesis and in both conclusions
  (p. 2062: "surjectif de noyau fini"). The kernel is read as a group scheme, finite over `K`, as in
  the standard definition. In characteristic 0 it is étale, so this is the same as having finitely
  many `K̄`-points. The two notions are proved equal (B2): Lean ⇒ print by base change, print ⇒ Lean
  because `A ×_B A ≅ A × ker φ` makes the fibres of `φ` finite, and proper plus locally
  quasi-finite gives finite (Mathlib, `IsFinite.of_isProper_of_locallyQuasiFinite`).

The form keeps the field's height (`IsAnStableHeightSS`), `κ = grKappa`, the degree
`isogDeg = #ker(K̄)`, the specialization `K′ = k`, and the split of the couple into two separate
isogenies, each of degree `≤ κ`. The split is weaker than the printed couple.

`gaudronRemondThm14Printed_iff` shows that the printed form and the field are equivalent. So the
restatement neither gains nor loses strength. As a displayed statement it is weaker only through
`1 ≤ g`.

## Fold plan (same-count restatement)

In the next fold, replace the field in a new bundle (`OpenResearchLeaves79`):

```lean
  gaudronRemondThm14Printed : _root_.ZInQ.GR14Printed.GaudronRemondThm14Printed
```

This replaces `gaudronRemondThm14AnSS : _root_.ZInQ.SemistabAssembly.GaudronRemondThm14AnSS`. The
other sixteen fields stay the same, so the bundle keeps 17 fields. The conversion theorem to
`OpenResearchLeaves78` copies every other field and sets

```lean
  gaudronRemondThm14AnSS :=
    _root_.ZInQ.GR14Printed.gaudronRemondThm14AnSS_of_printed n.gaudronRemondThm14Printed
```

The new top theorem composes it with `sixContactMin_of_open98`. No consumer changes: everything
downstream still reads `OpenResearchLeaves78`. The fold file imports
`ZInQKernel.Contrib.OneProof.GR14Printed.Printed`.

Suggested field docstring: Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4 (p. 2060), as
printed: `A` of dimension `g ≥ 1` (p. 2058), with κ(A) as on p. 2058. Isogenies are "surjectif de
noyau fini" (p. 2062), with the degree the order of the kernel. The height is the field's
`IsAnStableHeightSS`. The form implies the replaced field
(`ZInQ.GR14Printed.gaudronRemondThm14AnSS_of_printed`, with the proved `g = 0` case and
`isIsogenyPrinted_iff`), and the converse holds (`gaudronRemondThm14Printed_iff`).

## Flag edit

Remove the SGA 7 IX 2.1.5 / no-𝔾_a (ga-rigidity) sentence from the row's flag. It does not apply.
GR1 (Gaudron–Rémond, Comment. Math. Helv. 89 (2014), §2.3, p. 351) prints semi-abelian reduction
directly ("admet réduction semi-abélienne", "un modèle semi-abélien"). Semistability is a hypothesis,
so only Lean ⇒ print is needed, and `IsSemistablePrinted` already states that `G⁰` is semi-abelian.
The open point is the model: the Néron model with semi-abelian identity components against GR1's
semi-abelian model (item M of the report). This contribution does not address it, so a reading
should disclose it.
