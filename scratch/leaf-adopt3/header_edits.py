#!/usr/bin/env python3
"""leaf-adopt3: edits of the module docstring of Leaves.lean (text only). Usage: header_edits.py FILE"""
import sys
p = sys.argv[1]
t = open(p).read()
R = [
("""* `HSyn` §2: every other leaf as a **placeholder** `opaque … : Prop`. **A placeholder carries no
  content**: it is an uninterpreted proposition whose docstring records the exact statement and
  reference. A theorem with a placeholder among its hypotheses says nothing until the placeholder
  is replaced by a genuine statement.
* `HSyn` §3: the leaves bundled (`ResearchLeaves`, `TextbookLeaves`) and the top-level theorem
  `sixContactMin_of_leaves : ResearchLeaves → TextbookLeaves → ZInQ.SixContactMin`, which is
  `glueOutputs_of_leaves` (glue G1-G17, G19, `sorry`) followed by glue-assembly's proved
  `GlueOutputs Mult.S_mul → SixContactMin` (G18-G20, checked against the real
  `ZInQ.SixContactMin`). `GlueOutputs` is a numerical interface, not a leaf.

The only `sorry` in the file is `glueOutputs_of_leaves` (hsyn-fix, after the reviews): A6""",
"""* `HSyn` §2: the remaining placeholders (`opaque … : Prop`; since leaf-adopt3 only R1(b) and
  R17). **A placeholder carries no content**: it is an uninterpreted proposition whose docstring
  records the exact statement and reference. A theorem with a placeholder among its hypotheses
  says nothing until the placeholder is replaced by a genuine statement.
* `HSyn` §3: the leaves bundled (`ResearchLeaves`, `TextbookLeaves`), the glue pieces bundled
  (`GluePieces`, leaf-adopt3) and the top-level theorem
  `sixContactMin_of_leaves : ResearchLeaves → TextbookLeaves → GluePieces → ZInQ.SixContactMin`,
  which is `glueOutputs_of_leaves` (glue G1-G17, G19: **proved** from the bundles, g0-split, folded
  by leaf-adopt3) followed by glue-assembly's proved `GlueOutputs Mult.S_mul → SixContactMin`
  (G18-G20, checked against the real `ZInQ.SixContactMin`). `GlueOutputs` is a numerical
  interface, not a leaf.

**leaf-adopt3 (2026-11-13): the file has no `sorry`.** The paragraph below is historical.
Before leaf-adopt3 the only `sorry` in the file was `glueOutputs_of_leaves` (hsyn-fix, after the reviews): A6"""),
("""No `axiom` declarations. Leaf numbering (R1-R22 and H5 research-level, T1-T35 textbook, T12 and
T32 now glue) is that of the note's §2.""",
"""leaf-adopt3 (2026-11-13) folded in wave 25 and g0-split, each in its own section:
`GlueSSBCSec` (glue-ssbc's `SemisimpleBaseChange`, before `HSyn`); between `HSyn` §2 and the bundles,
`TDifferentSec` (T20, T21 local forms and T22 proved), `TSkolemKWSec` (T13, T19 proved; T18's
density form from `ChebotarevExists`; T17 narrowed to `KroneckerWeberCyclic`; `c10_of_chebotarev`),
`T30Sec` (T30 from T16(a), with copies of the kernel's `GlueI6Rest`, `GlueSqrtLocal`,
`GlueSqrtDisj`), `T10EtaleSec` (T10 concrete and Galois-equivariant), `Pi0X6Sec` (`R1pi0Props`
from clauses plus two Props; R1's clause kept), `HodgeLatticeSec` (`HodgeLatticeTheorem` from two
Props and `DimBaseChange`), `H5NeronSec` (H5's Néron identity from N1, N2 and glue; additivity),
`X1BelyiSec` (`X1ModelExists`, `BelyiX1` from five new leaves T36-T40), `E1SubSec`
(`VSurjOfSurjective` proved), `C9RhofSec` (C9 proved); and in §3 the proof of
`glueOutputs_of_leaves` (g0-split) with the bundle `GluePieces`. Bundle changes: `t10` concrete;
`t13`, `t19`, `t22a`, `t22b`, `t30` removed (proved, `HSyn.t13_proved` etc.); `t17`, `t18`
narrowed; new `x1` (T36-T40), `t41` (N1, Néron models exist). See
`docs/research/leaf-adopt3.md`.

No `axiom` declarations. Leaf numbering (R1-R22 and H5 research-level, T1-T41 textbook; T12, T13,
T19, T22, T30, T32 now glue, proved except T12) is that of the note's §2."""),
]
for old, new in R:
    assert t.count(old) == 1, old[:80]
    t = t.replace(old, new)
open(p, 'w').write(t)
