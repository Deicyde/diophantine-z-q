# PR70 selective interface adoption — 2026-11-13

## Source and selection

Source: [PR70](https://github.com/elliotglazer/diophantine-z-q/pull/70), contributor **loning**, commit `8a91bb253f2462c303c8bd9c6fa5efe190b9b834`; original `ZInQKernel/Contrib/D1.lean` SHA-256 `b15443d9cdfefcf2db0e6e674631c7e815f5356c94fe6adb4b9c393fbfc1fc2f`.

Destination: `ZInQKernel/Contrib/ConductorBounds/LocalForms.lean`, SHA-256 `f119a3d482f42317220260f83e75d43dedea8e2ca1100eb00d73389e4330f2d0` (3,799 bytes). The four local-wrapper declarations, including their bodies, are byte-identical to PR70. The first endpoint is rebound to canonical `ZInQ.Contrib.ConductorBounds.D1_closed`, retaining PR70's full telescope and named instance labels `hpF`/`hPl`.

Only this thin consumer layer is adopted. PR70's alternative Hilbert/Serre port is not copied. The canonical supplier sources and their existing attribution stay unchanged. The original PR, branch, commit and review history remain intact; this does not close or commandeer PR70. The original 21-PR `SOURCE-MAP.json` remains the frozen core ledger, not relabelled to include this new destination.

**Do not co-import the original PR70 `Contrib/D1.lean` with this facade:** they deliberately expose the same five declaration names. Integrate one canonical supplier tree and this facade, not both implementations.

## Available result → needed assertion → exact map

- `D1_genuine`: canonical `D1_closed` supplies the genuine number-field upper-break bound with no Hilbert/Serre proof argument. All original field, prime, Galois, `P | p`, `a ≥ 1`, factorial ramification and nontrivial `G_b` inputs remain.
- `D1_local`: baseline `ramificationIdx_le_factorial_local` uses the stated core-free `localSub L K P` and its bounded index to supply the factorial input for that same `L`, `P`, `K`.
- `D1_local'`: baseline `index_localSub` identifies that same index with the contracted prime's `e * f`; its stated bound feeds `D1_local`.
- `D1_krasner`: baseline `ramificationIdx_le_factorial_of_unique` consumes the original global-core, unique-prime and contracted `e * f` inputs on the same objects.
- `D1_krasner'`: baseline `normalCore_fixingSubgroup_eq_bot` converts the original normal-closure equality to the required global-core equality; uniqueness and degree inputs are retained.

No index set, field, prime or witness is replaced. The endpoints still include `p = 2`, `a = 1` and the original natural `b` range. Neither Krasner-named wrapper constructs an approximation or proves the existence of its residual data. These are number-field conductor interfaces, not the more general complete-DVR leaves, H/height construction, C10 compatibility or Hilbert10.

## Evidence boundary

The new destination was checked against independently written full signatures copied from the pinned PR70 source, not signatures inferred from the providers. All five full kernel type comparisons passed, with no additional universe parameters. Each actual theorem body passed a fresh-name trust-level-zero kernel add. Five extra-hypothesis and five wrong-body controls were rejected. Actual dependency bodies were traversed; only `propext`, `Classical.choice`, `Quot.sound` were allowed. Ordinary compilation and this focused fixture passed; an independent read-only source/transition review found no mathematical blocker and requested preservation of the named instance labels, which was done.

This focused result does **not** relabel PR70's historical audits, the earlier frozen core audit, or any future combined-head CI. The frozen core `b9389e7b53b3976dfc32bccf346697831b79bd2c` separately passed its full 1,406-module local/public audit and original controls. This extended candidate requires its own full audit, controls, source identity and all live required CI checks on the current base before landing. No protected root, target, definition, registry, checker, dependency or pin is changed by this adoption.

See [the end-to-end roadmap](../hilbert10-roadmap.md). **Hilbert10 remains unfinished.**
