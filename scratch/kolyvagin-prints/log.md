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

## Stop check

- **VERIFIED (base source).** `RCLeaves.modularNewform` uses
  `modularNewform_of_printed` with two GLUE readings already shared by the
  Theorem 5.3 lane. This route does not construct the algebraic parametrization
  or the CM image of the specific point in the trace.
- **VERIFIED (base source).** `PoleCMTraceDictionary` is restricted to the
  positive squarefree pole family at 11 mod 12. `IsHeegnerTrace` requires a
  non-CM lattice. Neither restriction is a premise of the unrestricted
  rank-zero consumer or the field. The existing draft cannot be used as a
  universal dictionary by changing quantifiers.
- **VERIFIED (base source).** `QuadraticDescent.lean` provides local
  triviality for restriction and twist, and the index-two cohomology
  identities. The available Selmer maps concern the 2-primary Selmer group.
  The proposed output requires full Sha and a finite restriction kernel;
  the mathematical fact that the kernel is killed by two alone does not
  give finiteness. The specialization and comparison at the selected field
  are not furnished by the stage-two route.
- **SPECULATIVE (page readings).** At most four candidate print dependencies
  in the proposed auxiliary-field route, including BFH already stated on
  the base. The count fails on GLUE: two additional open obligations at
  minimum even counting newform extraction as shared. No candidate was
  rated LEAF, no new Prop was added, and no consumer was rewired.
- **Verification.** Source audit and `git diff --check` only. The scoped stop
  adds no Lean file or declaration. No Lake command or build ran, so no jobs
  option was used and no import build or Lean process was started.
