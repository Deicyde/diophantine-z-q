# Smaller coefficients at the same 380 or 383 variables

This conditional research layer above #13 sharpens the height transfer and
final input contradiction. It changes only the fixed anchor parameter.

| Route | Variables including input | Maximum coefficient | Previous |
| --- | ---: | --- | --- |
| Default, order 45 | 380 | 28902*3^1412: 679 digits, 2253 bits | 682 digits |
| Optional, order 47 | 383 | 28902*3^1340: 644 digits, 2139 bits | 646 digits |

Read [PROOF.md](PROOF.md), [APPLICATION_CONTRACT.json](APPLICATION_CONTRACT.json),
[FINDINGS.json](FINDINGS.json) and the cumulative [HANDOFF.md](HANDOFF.md).
The arithmetic interpretation retains the inherited inputs. This is not a
new current manuscript edition or full proof verification.

```sh
python3 -B research/height-consumer-refinement/reproduce.py --output build/height380
python3 -B research/height-consumer-refinement/reproduce.py --order 47 --output build/height383
```

Python 3 and Node suffice, without network or third-party packages. Use a
new or empty output directory. The runner checks exact integer margins,
the complete symbolic source comparison with #13, five negative controls,
every compiler gate, four conic transports, all diagonal substitutions and
every quartic coefficient. It verifies source bindings before and after
the run. These finite checks do not establish the informal arithmetic proof.

EXPECTED.json catalogs the generated full decimal expansions and their
hashes. The new directory commits their deterministic specification and
checkers; the tables are regenerated and uploaded by CI. No committed full
expansion is claimed. The prior packets and their historical verdicts are
preserved. Separately authored review and public readback are linked at
immutable revisions from the PR; author status fields are not approvals.
