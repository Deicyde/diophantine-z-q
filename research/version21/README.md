# Version 21

This version incorporates José Brox's explicit 229-variable quartic from
[PR158](https://github.com/elliotglazer/diophantine-z-q/pull/158), merged at
`b013ec5319c25d427b55a1f18e9be753ed392bf7`. It has 207 quadratic rows,
3,312 nonzero quartic monomials, content one, largest absolute coefficient
`149^30 < 2^217`, and a 74,007-byte decimal expression. The unchanged
195-variable polynomial has Busy Beaver coefficients. Both counts include
one rational input. The 247 and 250 remain as intermediate constructions.

The new effective arithmetic at `N = 15` is proved in Part I of the
[new TeX](../../manuscripts/quartic_v21.tex) and
[PDF](../../manuscripts/quartic_v21.pdf). It is not obtained by substituting
15 in an ineffective threshold. The proof includes the torsion-inclusive
height bound, the small-exceptional-set local extraction, the numerical
contradiction and simultaneous completeness.

[DEPENDENCIES.md](DEPENDENCIES.md) identifies the exact retained suppliers
and new arguments. [CORRECTIONS.md](CORRECTIONS.md) accounts for all 25
selected Version 20 and PR158 notes, preserving their original IDs.
[RETAINED-EDITS.json](RETAINED-EDITS.json) records the two mathematical
explanations, edition-specific wording changes and AI-attribution addition
in the retained body. No released file is modified.

From the repository root, run:

```sh
python -B research/version21/construction/check.py
python -B scripts/check_current_manuscript.py
```

The first command authenticates data, runs the retained finite checks,
checks both full quadratic tables parsed from the actual TeX, and checks
the maps, expansion, constants and plain notation. It uses only the Python
standard library. Its report is written under `build/version21/`.
It does not establish arithmetic soundness or completeness.

The three-pass serial PDF build is recorded in [BUILD.json](BUILD.json).
[RELEASE-MANIFEST.json](RELEASE-MANIFEST.json) binds these files and states
the current review limits. A local build or finite-check pass does not
constitute the protected App review or release approval. Those are still
required. CI registration of the new finite entry point is a separate
follow-up; no hosted execution of it is claimed here.
