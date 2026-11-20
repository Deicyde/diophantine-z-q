# Rational Atkin–Lehner handoff

**Scoped stop.** The at-scale parametrization is on `X0Branch.model`.
The matrix calculation identifies the pullbacks as `j(Qτ)` and
`j((N/Q)τ)`. The new `AtkinRational/Coordinates.lean` proves that
`jqN m` belongs to the rational model's function field for every
positive `m ∣ N`, including both pullbacks. The literal swap is the
Fricke case.

Both retained declarations elaborated during the scoped attempt.
Their axiom audits list only `propext`, `Classical.choice`, and
`Quot.sound`. The larger module failed on the matrix proof; no
successful standalone `lake build` is claimed. Automatic review
rejected the rerun because another Lean job was active; the last
guarded check still found an active job and launched nothing.

The next step is to lift the generator identities to a pullback of
meromorphic germs, extend the generic map using the existing
valuative lemma, and check the analytic arcs and the square.
The based identity additionally needs the signed point difference
represented by a morphism into the fixed projective elliptic curve.
The report gives the density argument and the formal cusp check.
`RationalAtkin`, `BasedAtkinOnPoints`, and the generic input of (O.7)
are still open. No printed leaf was added. Rationality of the fixed
`κ` stays an input.

See `docs/research/rc-atkin-rational.md` and
`scratch/rc-atkin-rational/log.md`.

Final SHA: `git log -1 --format=%H -- .fleet/rc-atkin-rational.md`
(the commit containing this handoff; its hash includes this file).
