# Fowler's Proposition 2·7 as printed

The open hypothesis `OpenResearchLeaves65.fowlerProp27` (`HDec.CMBranch.FowlerProp27`) states Fowler's class-number
bound with the project's encodings of the order discriminant, `orderDisc R = conductor(R)² · d_k`, and of the class
number, `Nat.card (CommRing.Pic R)`. An independent reading (AI-READ, 2026-11-18) rated it a consequence of the print
through exactly these two identifications.

`ZInQKernel/Contrib/OneProof/FowlerProp27Printed.lean` adds the leaf

* `HDec.CMBranch.FowlerProp27Printed`: G. Fowler, Math. Proc. Cambridge Philos. Soc. 180 (2026), Proposition 2·7,
  p. 615 (h(Δ) on p. 613), re-indexed by orders: for an imaginary quadratic order `R` (`IsImagQuadOrder`), every
  ℤ-basis `b` of `R`, `Δ = Algebra.discr ℤ b` and `h = Nat.card (ClassGroup R)`, and every `k' ≥ 1` with `h ≤ k'`,
  `√|Δ| ≤ 2k'² exp(21000k'²)`;

and proves

* `HDec.CMBranch.fowlerProp27_of_printed : FowlerProp27Printed → FowlerProp27`,

with the identifications as theorems: an order of this kind has a ℤ-basis of size two; the index used by the order
construction is `LeafQM.AV.conductor`; `orderDisc R = Algebra.discr ℤ b` for every ℤ-basis `b`; the discriminant is
negative and congruent to 0 or 1 modulo 4 (so the print's hypotheses on Δ hold); and
`Nat.card (CommRing.Pic R) = Nat.card (ClassGroup R)` (Mathlib's `ClassGroup.equivPic`).

## Checks

* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  +ZInQKernel.Contrib.OneProof.FowlerProp27Printed`: built (16545 jobs).
* `#print axioms HDec.CMBranch.fowlerProp27_of_printed`: `[propext, Classical.choice, Quot.sound]`.
* `#discharges` (35 open hypotheses, 15020 theorems checked):

```
DISCHARGES [OpenResearchLeaves65.fowlerProp27] by HDec.CMBranch.fowlerProp27_of_printed
  still assumes: [HDec.CMBranch.FowlerProp27Printed]
  axioms: [propext, Classical.choice, Quot.sound]
```

The new leaf enters kinds.tsv flagged unread (locator row "Fowler 2·7" in `docs/research/locators.md`).
