# Optional higher-order construction

Above #19's 376-variable /425-digit route, this adds one scalar inverse
coordinate and uses a different detector chain of the same size. The
result has **377 variables,327-digit coefficients**, scalar order47,
detector order50 and anchor3^1512. The 376-variable alternative is retained.

Run from the repository root with Python3 and Node:

```sh
python3 -B research/higher-order-variant/reproduce.py --output build/higher377
python3 -B scripts/check_audit_history.py --self-test
```

The replay uses only standard-library Python, Node, committed sources and
fixed exact weights; it needs no network or floating-point optimizer.
It checks actual source differences and seven corruptions, compiles and
checks gates, applies four conic transports, and checks the whole diagonal
expansion. EXPECTED.json binds the full generated decimal table and other
artifacts. CI uploads that table; it is not committed in this packet.

PROOF.md covers the changed scalar and detector applications, both-place
proxy, precision/identity cases, simultaneous real and finite completeness,
and every height consumer. APPLICATION_CONTRACT.json is the author
submission, not a reviewer decision. A separate source-bound review must
assess it. HANDOFF.md and FINDINGS.json preserve provenance and limits.
The inherited global arithmetic remains conditional; Version13 is still
the current manuscript and release. Internal review does not supply the
designated Protocol / independent agent audit App check.
