# bp-audit-size: blueprint audit of size/ and model/

The full findings are in `docs/kernel-audits/blueprint-audit-2026-11-07-size.md`. This report
copies its summary.

## Scope and status

- **Audited: 87 articles with `statement: formalized`.** That is 36 under `size/` and 51 under
  `model/`, at base commit `de90139`.
  - All 36 size articles were new since the previous Lean audit.
  - In `model/`, 8 articles were new and 2 had changed (torsion, division-polynomial-multiples).
  - The other 41 model articles were covered by `lean-audit-2026-11-06.md`. Neither their text
    nor their Lean changed since.
- **Edited:** 4 articles, prose only, in `size/majorants/`.
- **Checks.**
  - `lake build ZInQKernel` succeeds, with only Main.lean's expected `sorry`.
  - `autoform check blueprint --lean-root .` passes after the edits.
  - `#print axioms` on all 118 names in the audited `lean:` fields shows no `sorryAx`.

| Article | Lean name(s) | Status |
| --- | --- | --- |
| size/majorants/admissible-cutoff.md | admissible_cutoff, D_le_T | drift, fixed in prose |
| size/majorants/template-heights.md | templateHeightTable, LibraryAdmissible, templateLibrary_maj | drift, fixed in prose |
| size/majorants/recipe-heights.md | recipe_heights | drift (hypotheses), fixed in prose |
| size/majorants/node-majorant.md | ConstructorBounds, NodeAdmissible, nodes_majorant, library_majorant | implicit hypothesis made explicit |
| size/syntax-bounds.md, size/majorants/degree-coefficient-bound.md | Pstar_size, Pstar_target_bounds, Pstar_degree_coeff, PstarNat_maj | faithful; extra hypotheses `HaltingNodeCheck` (expected) and `\|c₃\| < 2^(2^24)` (discharged by `c3_natAbs_lt`) |
| the other 30 size articles | see audit table | faithful (several with stronger Lean) |
| the 10 new or changed model articles | see audit table | faithful |

## Statement corrections

- **admissible-cutoff.**
  - Item 1 claimed $\lvert c\rvert\le T$ for every constant node. The Lean has no such
    statement: the literal constants need no hypothesis, and only $2^{69}<T$ is proved.
  - The items now restate the template-height hypotheses, starting with the uniform
    constructor bounds for the constructors of the specification.
  - The program-literal bound $\lvert c_3\rvert<2^{2^{24}}$ is now a stated hypothesis, as in
    the Lean, and $D\le T$ was added.
- **template-heights.** "Every other constant is below $2^{128}$ (compared by evaluation)" is
  not a Lean fact. It is replaced by the Lean argument: each literal is bounded as
  $2^{2^k}$ for small $k$, which $B\ge2^{20}$ absorbs.
- **recipe-heights.**
  - The hypotheses now match `LibraryAdmissible`: constructor bounds, psi indices, $\ell$ and
    $T$, with no constant hypothesis.
  - They also include `PrecisionShape`, the circuit shape as upper bounds.
  - "precision has at most 293622 constraints".
- **node-majorant.** The `ConstructorBounds` hypothesis is now stated, together with the note
  that the constructors of the specification satisfy it at every $B\ge2^{20}$
  (`specConstructors_bounds`).

## Lemmas added

None. No Lean files were edited.

## Problems

None blocking. No consumer article had to be weakened. The edited articles feed exactly the
compiled chain `admissible_cutoff → integers_maj → PstarNat_maj → Pstar_degree_coeff`.

## Suggestions for the next agent or the lead

- **Add the missing names to the `lean:` frontmatter** (the full list is in the audit):
  - admissible-cutoff: `one_le_ell_value`, `specConstructors_bounds`, `two_pow_sixtynine_lt_T`.
  - node-majorant: `library_nodes_majorant`.
  - template-heights: `psiIndices`.
  - recipe-heights: the conjunct-count lemmas and `precisionShape_of`.
  - membership: `MemberSpec`.
  - raw-addition-points: `RawAddSpec`.
  - fixed-point-codes: `psiP0`, `fixedX`, `fixedY`.
  - division-polynomial-multiples: `mulByN_formulas_of_charZero`.
- **Fix `size/majorants/README.md`.** It still says the majorant needs $B$ to exceed "every
  occurring constant". It should mention the constructor bounds instead.
