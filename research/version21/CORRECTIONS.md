# Version 21 corrections and adoption notes

This author disposition covers all 25 selected notes. Original text and links
are preserved in [CORRECTIONS.json](CORRECTIONS.json). The six issue comments
are cited there. Implemented entries await review of this manuscript; no
reviewer acceptance is inferred from a local check. Released files stay frozen.

| Original item | Class | Disposition | Location or reason |
| --- | --- | --- | --- |
| `44075047861-1-astra-V20-N1` | C | implemented; independent acceptance pending | README.md construction table, current handoff and verification navigation |
| `44075047861-1-fable-v20-n1-ratio` | C | implemented; independent acceptance pending | construction/verify247_retained.py: all 216 transformed rows and three ladder rows must agree literally |
| `44075047861-1-fable-v20-n2-start-cite` | C | implemented; independent acceptance pending | retained v20:overview: exact v19:250-construction citation and ladder deletion |
| `44075047861-1-fable-v20-n3-det-m6` | C | implemented; independent acceptance pending | retained v20:normalization: signed three-block determinant calculation |
| `44106224232-1-fable-v20-n1-hosted-checks` | C | deferred | CI registration in a separate follow-up, as required by docs/manuscript-agent-guide.md section 9 |
| `44106224232-1-fable-v20-n2-starting-system-derivation` | C | implemented; independent acceptance pending | retained v20:overview: unique ladder value and absence of coordinates 245..249 |
| `44115113273-1-fable-N1-arithmetic-certificates-absent` | C | implemented; independent acceptance pending | construction/verify_arithmetic.py and v21:effective-soundness: exact factorizations and rational log bounds |
| `44115113273-1-fable-N2-status-wording` | C | implemented; independent acceptance pending | v21:overview and DEPENDENCIES.md: the N=15 arithmetic is new and its proof is included |
| `44126365630-1-astra-N1-artifact-paths` | C | implemented; independent acceptance pending | construction/README.md: explicit distinction between source and normalized quadratic tables |
| `44126365630-1-astra-N2-command-numbering` | C | implemented; independent acceptance pending | construction/README.md: one standard-library entry point, no SymPy command or stale ordinal |
| `44126365630-1-fable-N1-citation-precision-and-stale-paths` | C | implemented; independent acceptance pending | DEPENDENCIES.md and v21:completeness: exact supplier labels, avoidance modulus, Gaussian residues and gcd checks |
| `44126365630-1-fable-N2-graft-checker-coverage` | C | implemented; independent acceptance pending | construction/verify229.py: authenticated source, nine-helper isolation and both field components |
| `44126365630-1-fable-N3-premise-list-height-inputs` | C | implemented; independent acceptance pending | v21:finite-sum-height: both duplication constants and the lower canonical height are derived |
| `44126365630-1-fable-N4-reconstructed-short-steps` | C | implemented; independent acceptance pending | v21:five-pole-obstruction and v21:local-extraction: parity, valuation rounding and inert trace derivations |
| `44152402106-1-fable-N1-helper-isolation-not-in-paper` | C | implemented; independent acceptance pending | v21:contacts and construction/verify229.py: helper isolation stated and independently executed |
| `44152402106-1-fable-N2-no-ci-execution-of-package-checkers` | C | deferred | CI registration in the separate follow-up; no hosted finite-check execution is claimed |
| `44152402106-1-fable-N3-upstream-paths-in-paper` | C | implemented; independent acceptance pending | construction/README.md and DEPENDENCIES.md: local paths and retained labels replace upstream navigation |
| `44152402106-1-fable-N4-short-steps-left-implicit` | C | implemented; independent acceptance pending | v21:effective-soundness, v21:completeness and v21:finite-sum-height: harmonic bound, gcd, trace residue and canonical-height steps |
| `44152402106-1-fable-N5-premise-list-not-itemized` | C | implemented; independent acceptance pending | DEPENDENCIES.md: all retained inputs and all new connecting arguments are itemized |
| `44420323106-1-astra-N1-physical-coordinate-summary` | C | implemented; independent acceptance pending | v21:point-recovery: table of stored components and displayed physical scalings |
| `44420323106-1-fable-N1-recovery-point-of-use` | C | implemented; independent acceptance pending | v21:point-recovery and v21:aggregate-components: both components identified before either aggregate is consumed |
| `44420323106-1-fable-N2-paths-and-filenames` | C | implemented; independent acceptance pending | construction/README.md: source/quadratic229-v62.json and final quadratic.json are distinguished |
| `44420323106-1-fable-N3-checkers-not-in-hosted-CI` | C | deferred | CI registration in the separate follow-up; author-run results are not gate coverage |
| `44420323106-1-fable-N4-dependency-index-labels` | C | implemented; independent acceptance pending | DEPENDENCIES.md: recovery-order, pair-ratios, nonzero-scale, shifted-aggregate and parity labels named |
| `44420323106-1-fable-N5-minor-wording` | C | implemented; independent acceptance pending | v21:effective-soundness proves E(M)<=1+log M; no stale above/below wording; README and release records identify preparation status |

Three entries concern hosted checker registration and are deferred to one
workflow-only follow-up. The Version21 entry point already reruns the retained
Version20 checks and independently checks the new data and printed tables.
Until that follow-up passes on the committed data, these are author-run
finite checks, not CI table coverage. No mathematical result is deferred.
