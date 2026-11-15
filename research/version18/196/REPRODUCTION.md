# Reproducing the selected 196-variable table

This directory proposes a portable copy of the independent audit of José Brox's 196-variable reduction at commit `5c35db3253a70b0875acec4b451cdaac4da3c8fd` of `JoseBrox/diophantine-z-q_improvements`. The reduction uses the unbalanced Conant198 parent. Keep the complete `../198/` directory for its arithmetic proof provenance, original package and separate reproduction. No author or publication agreement is changed here.

The selected table is `upstream/source/computation/quartic/laurent_recovery_v38/family196/polynomial.json`. Its SHA-256 is `a8ab93d66fe83f4bdfd4b176d47c250c2e124f42535d7a6a133edff6a97389ad`. It has 196 total variables including the input, 195 existential variables, 182 quadratic summands and 2,943 coordinate monomials. The separate balanced table is checked as an existing comparison; it is not the Version 18 presentation. In the upstream paper, the headline `P_N` is balanced. Identify the selected unbalanced table by its path and hash.

## Files and command

`INPUT-FILES.json` lists every required file. The mathematical audit reads eight JSON files, including the upstream copy of the parent. Before running it, the I/O helper checks the complete 29-file source inventory against the recorded Git blob IDs and SHA-256 values, and separately checks the retained Conant parent table. Keep `checks/` and `provenance/SOURCE-PINS.json` together. The source root and parent-table locations are explicit arguments. No upstream program is imported or executed.

Use a normal Python interpreter without `-O`. The checker uses the standard library only and passed with Python 3.14.7. It needs no installation or credentials. From the proposed public repository root, run:

```text
python -B research/version18/196/checks/independent196.py --source-root research/version18/196/upstream/source --parent-table research/version18/198/upstream/H10-quartic198/circuits/inverse198/quadratic.json --output reproduction-output/196-result.json
```

Choose a new output filename for each run. Absolute arguments also work from another current directory. The helper refuses existing outputs, outputs inside the selected source or checker tree, altered pins or source files, and an altered parent table. The relocated test used paths containing spaces, an unrelated current directory and an environment containing only the system and Python settings listed in `evidence/PORTABILITY-CHECK.json`.

The expected result is `PASS` with 48,690 assertions. It checks all 182 retained-row identities and both deleted defining identities, the unchanged guard rows, the coordinate map and nonzero multipliers, both full expansions, degrees and coefficient statistics, and the original coefficient, division-shift and primitive-multiplier corruption controls. The portable replay matched every original result field after normalizing path separators. Extra I/O tests rejected altered source and parent files, optimized Python, existing outputs and protected outputs. Original inputs stayed unchanged.

## Mathematical and coefficient scope

The source paper is `upstream/source/papers/quartic/laurent_elimination_20261115_v38.tex`. Section 2, `thm:general`, proves the elimination lemma. Section 3 applies it to the 198 parent. Section 5 gives coefficient heights; Section 6 describes the reconstruction checks and their limits. The accompanying weight note and finite data remain in their original relative layout. The checker retains the independently transcribed coordinate formulas; its comparison body is unchanged. `provenance/independent196.diff` shows the complete path adaptation, and `CHECKER-ADAPTATION.json` records a literal reverse-patch check against the preserved original.

The elimination preserves the rational input projection for every fixed integer `N >= 1`. Thus it transfers the parent's defining theorem with its existing threshold. It introduces no arithmetic hypothesis. This finite replay does not re-prove the inherited Conant198 arithmetic, the Version 18 Busy Beaver theorem, or the assembled manuscript.

For the selected unbalanced family, `A = 149^(2N+1)`. Its only parameter terms in the table's one-based coordinates are

```text
-2*A*x102 - 44402*A*x102^2*x114 + A^2*x102^2
```

The exact coefficient height is `max{K_fixed, 149^(4N+2)}`, with

```text
K_fixed = 484991541504995159662206970923766531374664106904986910720
```

The crossover `N = 7` is a coefficient comparison, not a sufficient defining threshold. Version 18's separate parent proof selects `N = BB(2^1000)`, hence `A = 149^(2*BB(2^1000)+1)`, and supplies the strict coefficient bound `BB(2^2000)`. Neither this checker nor the supplied table computes BB. The original table's `sufficientDefiningThreshold: "Ineffective"` metadata is preserved as upstream provenance; the new BB specialization is a separate manuscript result.

## Evidence and historical qualifications

`provenance/original-AUDIT.md` and `original-RESULT.json` retain root's original bytes and scope. That audit predates the user's correction of the Version 18 target to 196 and therefore still says the chosen target is 198. This is a historical statement, not the current selection. Likewise the source paper retains its original parent-premise and threshold qualifications. The manuscript must discharge the inherited inputs through its internal results.

`evidence/PORTABILITY-CHECK.json` records the relocated replay. Final manuscript, PDF, build and reviewer identities remain pending. This package supplies finite reproducibility evidence and source provenance; it supplies no acceptance or publication record. The 258/259 data and programs among the authenticated source files are retained provenance only. No optimization was attempted.
