`LiftPhase.actualLift` constructs the Appendix F stage phase as the
elliptic conductor root product times the detecting prime's quadratic
character. The extraction factors cancel the genus twist on units.
The original zero extension at exceptional nonunits is retained, so
`actualEta_reduce` proves the `Lift.phase` field at the full stage
precision. `actualLift_order` proves the phase order on stage good
primes.

`LiftPhase.actual_hchar` supplies the character comparison of
`oldStageLaw_of_finiteAction` via the existing pool identification.
The lift, pool diamonds and old character use the same local factors,
and both sides of the comparison use one coefficient embedding.
`actualOldStageLaw` leaves the grid and relative finite action as the
existing named hypotheses. The actual-stage parameters and numerical
old-level coverage remain; no phase identification remains to assume.

All three modules compile individually with serial `lake env lean -j1`.
The 19 theorem audits report only `propext`, `Classical.choice` and
`Quot.sound` or subsets thereof. No print was added and no new
manuscript error was found in scope. The statements and remaining owners
are in `docs/research/rc-lift-phase.md`.

Verified result, report and log SHA: `dd5c3194cda80db497b3fb3b7a983450ecc430b3`.
The final branch SHA is the commit adding this handoff, available as
`git log -1 --format=%H -- .fleet/rc-lift-phase.md`.
