# Sizing log

**VERIFIED (pinned source).** Base `fd9fbbe271577c7882e4ac79fb05c19694dceca2`.
The exact field `Prints.kolyvagin : KolyvaginThm1Printed`, at
`ZInQKernel/Contrib/CloudB3RC53/Prints.lean:44,78`:

```lean
def KolyvaginThm1Printed : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsModular E → ∀ r : ℕ, r ≤ 1 → AnalyticRank E r →
    Module.rank ℤ E.toAffine.Point = r ∧ Finite (sha E)
```

`IsModular` is the existence, at some positive level, of a weight-two
coefficient-matching cusp form on Γ₀. `AnalyticRank` is the order at 1 of an
entire continuation of the curve L-series. `sha` is the all-place local
kernel on full Galois H¹ (`OneProof/SelmerTwoPower.lean:120` under
`ZInQKernel/Contrib/`); it is the full Sha, rather than its 2-primary
component. `Module.rank ℤ` is cardinal-valued. In applications `r` is 0 or 1.

`ZInQKernel/Contrib/CloudB3RC53/Prints/Kolyvagin.lean:75` has the exact
variant `KolyvaginThm1WeilParam`: substitute `HasWeakWeilParametrization E`
for `IsModular E` in the display. This is an analytic stand-in for a weak
Weil parametrization at the conductor: a matching cusp form at `newformLevel E`,
a period lattice, and a nonzero rational scale for its differential.
`ModularToWeakWeil` is an open implication from ellipticity and
`IsModular E` to that stand-in. It is used by the alternative
`kolyvaginThm1Printed_of_weilParam`, rather than an extra premise of the
direct field. The algebraic comparison in the stand-in is also open.
MPI/90-69 is classified as GLUE under the task's source rule even where the
base's docstrings call it a print.

**VERIFIED (call audit).** Ran `git grep` for `kolyvagin`,
`KolyvaginThm1Printed` and `KolyvaginThm1WeilParam`, also
case-insensitively to separate the distinct pole hypothesis. The companion
[consumer list](consumers.md) records all direct reads and the adapters.
The PR #163 head and merge are not ancestors of the base, and no corresponding
`_mw` read occurs in the call scan.

**VERIFIED (manuscript).** The paper's own starting point is
`diophantine_zq.tex:1086–1108`: modularity, the preprint's two analytic
ranks, the auxiliary field and Sha restriction, and the Kummer consequence.
The separate Kato rank-zero alternative is at L1104–1108.
