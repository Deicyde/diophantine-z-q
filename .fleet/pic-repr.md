# pic-repr (fleet note)

**Verdict.** I could not prove `picRepresentableAbVar` (`T09Pic.PicRepresentableAbVar`, Picard representability for
abelian varieties) outright. Nothing in the tree constructs a representing scheme in dimension ≥ 2: the Hilbert
schemes cover finite flat subschemes only, and there are no Quot schemes, no quotients by finite flat group schemes
and no dual abelian variety. Jacobian-Challenge represents the full Pic only for smooth proper curves over
separably closed fields. The only consumer (t09SymmIsogenyExists → DetTate / G12Det) applies the field over number
fields to abelian surfaces (`A.dim = 2`), so no provable narrowing reaches it.

**Deliverable.** `ZInQKernel/Contrib/OneProof/PicRepresentableAbVar.lean` (imports TailZ24 only) discharges the
field from the printed Murre–Oort / FGA 232 / Kleiman 9.4.8 / BLR 8.2 Thm 3 form:
* new leaf `PicRepr.PicRepresentableLFTAbVar`: representable by a scheme locally of finite type. LEAF, printed
  form; locators UNVERIFIED;
* the same leaf also proves pic-dict's leaf `PicDict.PicLocFinType` (verbatim copy, `picLocFinType_of_lft`);
* conversely, the field together with PicLocFinType implies the leaf.

Count: 0 on main (dry run 34/11 → 34/11, the fold compiles). −1 once pic-dict / pic-smooth's `picZeroAbVar`
reduction, which adds PicLocFinType, is folded. The −1 target with no new leaf is not reached.

**Compiles** (all standard axioms):
* `Statement.lean`: the verbatim copy, checked by `rfl`;
* `Narrow.lean`: the field for `A.dim = 1` over separably closed fields, plus `smoothOfRelativeDimension_of_dim`;
* `Chart.lean`: for proper geometrically integral `X` with a rational point over any field, the chart hypothesis of
  the vendored group criterion is equivalent to representability. The chart Prop is therefore not strictly
  smaller; every other ingredient is proved;
* the Contrib file;
* `#discharges`: picRepresentableAbVar is discharged, still assuming `PicRepresentableLFTAbVar`;
* `autofold.json`, with its dry run.

**Remains.**
* Readings of the locators (Murre 1964, Oort 1962, FGA 232 Thm 3.1, Kleiman 9.4.8 / 9.2.5, BLR 8.2 Thm 3).
* The `rfl` check of PicLocFinType against pic-dict once both are in the tree.
* Representability itself in Lean: it needs a concrete chart, i.e. Hilbert schemes of divisors or Mumford's
  `A/K(L)`. Report: docs/research/pic-repr.md.
