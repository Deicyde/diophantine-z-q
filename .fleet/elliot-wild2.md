# Wild inertia: fold complete

The uncited manuscript step at L817–818 now comes from Silverberg–Zarhin,
Theorem 3.3, p. 405, of the paper cited at L816. `SZThm33.lean` states both
directions at the separable closure on the rational Tate module. It reads
semistability at the extended valuation as semistability at a finite
subextension, allowing the base itself. The supplied semistability gives
that witness. The theorem gives square zero, and the Tate lattice inclusion
and proved prime-to-ℓ wild periods give triviality on the Tate module.

`#discharges` checked that `elliot_of_sz33` discharges the exact old row
with only `SilverbergZarhinThm33` as an assumption. `TailZ90` replaces
`elliotWildInertiaTrivial` by `silverbergZarhinThm33` in
`OpenResearchLeaves64`. The real contribution and folded `frozenTarget`
build with Lake and only the three standard axioms. The hash comparison
found no change to any other existing declaration. The open-hypothesis
documentation was regenerated and checked.

Strict and strictest GLUE are both **28 → 28** on 33 H inputs, or
**29 → 29** on 34 inputs including pole completeness. If the reviewer
accepts the replacement as printed form in both columns, these counts
become **27 / 27** for H and **28 / 28** including pole completeness. The
remaining work is review of the finite-subextension reading and the
statement match. See [the report](../docs/research/elliot-wild2.md) and
[check results](../scratch/elliot-wild2/log.md).
