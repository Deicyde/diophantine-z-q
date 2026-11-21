# Gross–Zagier’s rational point in the p. 310 formulation

`hkConsumed_of_gz73` proves the pole argument’s consumed rank-one statement
from Gross–Zagier, Invent. Math. 84 (1986), Thm (7.3)(1), p. 231, as restated
p. 310, and the existing BCDT newform route. The p. 310 premise accepts a
matching weight-two newform at any positive level. This removes
`PoleNewformLevelIsConductor`. The application adds zero project GLUE.
The two existing newform GLUE readings remain dependencies. The fold waits
for Theorem 5.3.

The manuscript’s Milne citation at L1784 supplies modularity and a
parametrization at the conductor. Newness calls for Milne’s Proposition
11.21, and the Hecke equivariance at L1788 needs a separate justification.
The source cited at L1093 is an unrefereed preprint and takes a stronger
modularity premise than `PoleS12.IsModular`. These are the existing citation
and application gaps. [Pole hypothesis audit](audit-pole-hypotheses.md)

## Lean result

All four theorems are in `ZInQ.Manuscript.HKGZ73`.
[Reduction.lean](../../ZInQKernel/Contrib/OneProof/HKGZ73/Reduction.lean)

- `hkConsumed_of_gz73` is the revised consumer. The existing adapters
  `bcdtThmA_of_printed` and `modularNewform_of_printed` give `f : Newform N 2`
  with `IsNewformOf E f` for some `N > 0`. The analytic-rank witness supplies
  the two central conditions, and `GZ73Print` supplies the infinite-order
  point used at L1111–1115.
- `analyticRankOne_iff_exists_value_deriv` retains the proof that an
  order-one zero of an entire continuation is equivalent to zero value and
  nonzero derivative at 1. `analyticRankOne_iff_value_deriv` retains the
  equivalence for any supplied continuation by uniqueness.
- `level_eq_newformLevel_of_isNewformOf` retains the proof that the matching
  newform is at the least matching cusp-form level `CST.newformLevel E`.
  The p. 310 application uses the existential witness directly.

`GZ73Print` is the sole new leaf statement relative to the headline. It
supplies one point after the caller provides a genuine matching newform and
an entire continuation with the two central conditions (L1086–1093,
L1111–1113). Its conclusion at each curve is weaker than the old forward-rank
assertion, which gives rank equality and finiteness of Sha. At an
`HKConsumed` call the leaf supplies the point once the BCDT route has
strengthened cusp-form modularity to a matching newform. The conditions on
the central zero follow directly from `AnalyticRankOne`. The legacy locator
docstring already has the requested wording from the prior work.

**VERIFIED (Lean).** `Reduction.lean` and the current scratch check pass
`lake env lean` after the single-target import builds. The check composes
the revised consumer with `poleCompleteness_of_hkConsumed` and verifies the
matching newform's continuation and the implication from `Prints.kolyvagin`
to `hK`. `GZ73Print` and all four theorems report only `propext`,
`Classical.choice` and `Quot.sound`. The prior scratch check describes the
p. 231 interface at `34f9cd14a`.
[Check.lean](../../scratch/hk-gz73b/Check.lean) · [Axioms](../../scratch/hk-gz73b/axioms.txt)

## Remaining inputs and fold arithmetic

| Input | Scope and TeX lines | Owner |
| --- | --- | --- |
| Height bundles `r`, `t`, `l` | Height estimate, L377–972 and L10936–11007. | Existing height suppliers |
| `hRC` | Theorem 5.3 supplies analytic rank one, L1005–1011 and L1111. | Restricted-converse work |
| `hCT` | Cassels–Tate pairing gives corank one at the eight-class calls, L1072–1084. | Existing pairing supplier |
| `hB` | `BCDTThmAPrinted` and its adapter, L1092, L1779–1780, L11150–11154. | Modularity supplier |
| `RCLeaves.shimuraConjugates`, `RCLeaves.liMultiplicityOne` | Shimura 1973 and Li 1975 inputs to the newform step, L1779–1784, bibliography L11050–11057. | `RCLeaves` suppliers |
| `RCLeaves.carayolEulerFactors`, `RCLeaves.faltingsRigidity` | Existing GLUE readings that compare Euler factors in the newform step, L1779–1784, bibliography L11084–11086 and L11205–11208. | `RCLeaves` suppliers |
| `GZ73Print` | Published rational-point implication for the use of the forward theorem at L1086–1093 and L1111–1113, bibliography L11161–11162. | Reading desk and reviewer |

- **Before Theorem 5.3 is supplied through its assembly.** The trial removes
  `hK` and adds `GZ73Print` and the four named `RCLeaves` fields. The height
  inputs, `hRC`, `hCT`, and `hB` stay. The 31 open rows (9 LEAF / 22 GLUE)
  would become 35 (12 LEAF / 23 GLUE with the p. 310 leaf counted, or
  11 LEAF / 24 GLUE pending independent source review). This is +4 rows
  over the headline and one fewer GLUE row than the p. 231 trial.
- **After sharing the existing Theorem 5.3 assembly.** Independently of
  this change, `restrictedConverseGenuine_of_leaves` replaces `hRC` by
  its `Prints` and `RCLeaves` suppliers. `hB` supplies `Prints.bcdt` through
  the adapter. Against that assembly with a separate `hK`, the pole change
  removes `hK` and adds `GZ73Print`. All four newform suppliers are shared.
  The delta is zero rows (+1 LEAF / −1 GLUE once the leaf is counted, or
  0 / 0 pending independent review). If Theorem 5.3 and its suppliers are
  all closed, the pole change takes 30 rows (9 / 21) to 30 (10 / 20 with
  the leaf counted, or 9 / 21 pending independent review).
- **If `Prints.kolyvagin` is retained.** Its rank-one instance already
  supplies `hK`. Theorem 5.3 also uses the input at rank zero
  (L2616–2626, L7625–7627, L7780–7781) and for finiteness at simple zeros
  (L4020–4021). It remains GLUE under the preprint rule. Relative to
  reusing that input to remove `hK`, the p. 310 route adds one row.

## Known issues and source checks

- **Source lens, STANDARD (lead’s reading).** The citation is faithful as
  (7.3)(1) in its p. 310 form (any newform `f` with `L(f, s) = L(E, s)`)
  together with BCDT Thm A (some such `f` exists). The p. 231 form alone
  would also need level = conductor. Independent inspection of p. 310
  is unverified here.
- **Lean lens, VERIFIED (definitions).** `IsNewformOf` uses normalized
  Tau Ceti weight-two newforms with trivial nebentypus and coefficients
  agreeing at every positive index, including the bad Euler factors.
  In `GZ73Print`, the value and derivative are of the arithmetic
  continuation `F`, which `eq_L_of_isLContinuation` identifies with the
  matching newform’s uncompleted `ModularForm.L`.
- The p. 310 substitution is for the pole application at L1111–1115.
  The geometric statement at L1781–1788 and the forward theorem’s rank
  equality and finiteness conclusions are outside this application.

## Manuscript check

All line numbers refer to `diophantine_zq.tex`.

| TeX lines | Step | Verdict |
| --- | --- | --- |
| L1001–1011, L1771–1775 | Use the restricted converse for an order-one zero. | **OK**. The existing proof takes `hRC`. |
| L1033–1069 | Produce both admissible parameters and eight Selmer classes for each. | **OK**. The existing construction and Kummer identification supply both calls. |
| L1072–1084 | Deduce corank one from the eight classes. | **OK**. The existing pairing proof takes `hCT`. |
| L1086–1089, L1111–1113 | Read the order-one zero as the two central conditions. | **OK**. The Lean dictionary identifies the value and derivative of the same continuation. |
| L1092, L1779–1784, L11150–11154 | Apply BCDT and obtain the matching weight-two newform. | **OK**. The existing adapter and newform route give an existential positive level, sufficient for the p. 310 premise. |
| L1781–1788 | Cite the geometric realization at the conductor and assert Hecke equivariance. | **unverified**. The Milne locator has the gap described above. The pole substitution uses only the matching L-series. |
| L1093–1097, L11161–11167 | Replace the pole use of the cited forward theorem by Gross–Zagier’s rational-point implication. | **unverified** in an independent source check. The p. 310 scope follows the lead’s reading. |
| L1111–1115 | Obtain rational Kummer representatives. | **gap filled**. The existing Lean argument uses the point and eight-class count to make the rational Kummer image exhaust the Selmer classes. |
| L1116–1121 | Rescale both witnesses to conclude pole completeness. | **OK**. The existing pole proof supplies the rescaling. |
| L2616–2626, L4020–4021, L7625–7627, L7780–7781 | Use the full forward theorem in Theorem 5.3. | **OK** for the dependency trace. Those calls retain their forward-rank input. |
