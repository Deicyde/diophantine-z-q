# RC calibration local lengths

`GenuineLengthBlockModelP.toLengthModel` derives `lenMov`, `lenMov'` and
`lenAct` from the actual local Galois actions and the existing Milne local
duality order statement. The two moving lengths are
`v₂(r + 1 − χ_h(r)a_r)`; each active length is two.
`calibrationTarget_of_HKL2P` reuses the existing HKL2 route with the same
target and uniform constant. The post leaf is unwired.

The moving supplier proves the comparison between the Frobenius at the
chosen split place and rational Frobenius, and uses the existing global
trace input. At an active odd split prime, good reduction and a squarefree
radicand give an inertia element acting by minus one on the central
coefficients. No new print or GLUE hypothesis was needed.

`LocalOrders.lean`, `Calibration.lean` and `Suppliers.lean` compile
individually. The scratch audit checked 34 declarations; each reports only
`propext`, `Classical.choice` and `Quot.sound`.

Remaining: the local model owner has `presMov`, `presMov'` and
`presAct`; the assembly owner has `hcentral`; the ordinary Kummer
owner has `KummerCoordinateBlockG.I` and `link`; the companion owner has
`goodModel`. The local arithmetic owner can now instantiate the active
supplier at each address. The cloud root owns the leaf switch. The
[report](../docs/research/rc-cal-local-lengths.md) records the precise
inputs and the manuscript check.

Final implementation and report SHA: `fb8ad3eb941fe77e7c92e3c375e97abbd576a29d`.
The separate commit adding this handoff is identified by
`git log -1 --format=%H -- .fleet/rc-cal-local-lengths.md`.
