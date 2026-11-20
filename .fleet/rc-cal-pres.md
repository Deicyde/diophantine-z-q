# Calibration local quotient presentations

Scoped stop: conditional presentations for the two moving places and every
active place. The Tate coordinates reduce the moving differential to
`χFr − r`; the active split model has `2 · 1₂` as its second
differential. Precision zero has unconditional presentations.

Manuscript error (tex 3471–3477): the short expression for the tame norm
in (4.4) requires involutive inertia. The general norm is the full sum of
powers. Both central cases used here satisfy the required involution.
The report gives a finite counterexample to the unrestricted wording.

At positive precision the remaining local theory is the comparison on
full cochains in degrees one and two and the actual Kummer image in the
ordinary coordinate. At a moving place this is the unramified
coinvariant coordinate; at an active place it is minus inertia evaluation
modulo two. No new print is added. See the
[report](../docs/research/rc-cal-pres.md) for the exact statements and sizes.

`SplitModel.lean`, `Presentations.lean`, and `Actions.lean` compiled
individually with `lake env lean --threads=1`. The 29 axiom checks
reported only `propext`, `Classical.choice`, and `Quot.sound`, or a subset.
The assembly, ordinary Kummer calibration and post leaf are unchanged.

Final implementation and report SHA: `aefa0bdf6e1bc6a52938e15c0a77171495aeecc7`.
The separate final handoff commit is identified by
`git log -1 --format=%H -- .fleet/rc-cal-pres.md`.
