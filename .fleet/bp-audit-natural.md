# bp-audit-natural: blueprint audit of compiler/natural

The full table is in `docs/kernel-audits/blueprint-audit-2026-11-07-natural.md`. It gives
the article, Lean names, verdict, and what was changed or still needs changing. This report
copies its summary.

## Scope and checks

- 85 articles under `blueprint/roadmap/compiler/natural/` with `statement: formalized`,
  audited at `de90139`.
- `natural-polynomial-semantics.md` was audited before (at `0bea4dc`). Its Lean file changed
  since, so I re-audited it: still faithful.
- `lake build ZInQKernel` succeeds.
- `autoform check blueprint --lean-root .` passes: 353 articles, 897 names resolved.
- A scratch `#check` of every unlisted name recommended in the audit succeeded. One needs its
  namespace prefix: `Precision.JTriple.two_nsmul_of_Y_eq_zero`.
- No Lean file was edited.

## Summary

| Verdict | Articles |
| --- | --- |
| faithful (possibly with unlisted names) | 52 |
| Lean stronger | 11 |
| drift, fixed in the article prose | 20 |
| extra hypothesis `HaltingNodeCheck` (expected, no change) | 2 (halting-node-check, circuit-node-counts) |
| other extra hypotheses | none left unstated (the hierarchical-calls item 2 hypotheses are now stated) |
| wrong names in `lean:` | none; about 45 articles have claims proved under unlisted names |

No Lean statement in this directory is false or vacuous, or weaker than a consumer needs.

## Statement corrections (articles edited)

- **exponential/, formulas/**
  - natural-circuit-semantics: the polynomial ring is $\mathbb Z[X_i:i\in\mathbb N]$, and
    variables of index $\ge V$ are set to $0$.
  - macro-semantics: the argument polynomials must take natural values at natural points.
  - hierarchical-calls, item 2: the hypotheses ($k\le V$, variables of $\kappa(\varphi)$ below
    $V$, private blocks) are now stated. Calls are read through the template's natural
    relation, which is $P=Q^R$ only at natural argument values.
  - power-template-semantics: the "Consequently" sentence needs natural-valued arguments.
- **packed/**
  - packed-state-selection: $1\le m<B$.
  - packed-transitions, item 2: $B\ge2$.
- **precision/**
  - capped-height-test: a false remark about intermediate values is replaced by
    $\beta\le L+1$ and $\langle e\rangle_L\le L+1$.
  - jacobian-formulas: characteristic $\ne2$ in items 3 and 8 and in the group-law clause of
    item 7.
- **programs/**
  - register-machine: register files are arbitrary maps, not finitely supported.
  - structured-programs: $k\le\rho_S$.
  - lowering: the division block works unit by unit, with invariant $y=r+qz+m$.
  - lowering-correct, item 0: the backward direction is what `code_backward` proves (three
    alternatives); forward runs start from a simulating file.
  - precision-ir: $M$ is computed by an integer expression; the temporaries form one shared
    region.
  - precision-machine: on rejection the machine "never halts" (not "enters a self-loop").
  - ir-integer-routines, ir-field-routines, ir-point-routines, ir-capped-routines: rewritten to
    match the routines that exist and their contracts. Removed routines that do not exist:
    rational comparison, point negation, multiplication by a constant, signed zero-test
    branches. Binary exponentiation became a loop of capped multiplications. Added a
    paragraph on the integer-variable layer.
- **universal/**
  - interpreter-primitives: divmod2 adds $\lfloor y/2\rfloor$ to $q$.
  - universal-interpreter: for $o=2$, $v=0$ the value $0$ is written back with setList.

## Lemmas added

None. This task edits only prose.

## Problems

- The integer-variable layer of the programs (`ZStmt`, `ZBigStep`, `ZStmt.compile`,
  `ZStmt.compile_sim`) has no article. Nearly all routine contracts (`*_spec` in
  SignedSpec, FieldSpec, PointSpec, CappedSpec) are missing from the `lean:` fields.
- `HaltingNodeCheck` remains a hypothesis of item 1 of halting-node-check.md, and of item 3
  and the order remark in item 4 of circuit-node-counts.md. This is as expected and is
  recorded in the final audit.

## Suggestions for the next agent

- Add the unlisted names given per article in the audit table to the `lean:` fields.
- Consider a new leaf article for the integer-variable layer.
