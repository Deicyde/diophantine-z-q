Scoped stop — Appendix F, tex 9725–9729. The determinant calculation gives
vanishing at every positive Fourier index modulo the maximal ideal. The
frozen field `det_orbit` asks for membership in the abstract submodule
`𝔪Λ`. Those statements need a comparison on the tested discrepancy
vectors; a nonsaturated lattice does not give it (tex 9644–9646).

`ZInQKernel/Contrib/OneProof/RC/TraceLimits/` proves trace and determinant
stability, open constituent subgroups of finite index, and the Kummer
field via squarefree radicals and absolute inertia. The chosen-lift
Chebotarev field follows from the tree's density theorem. The constructor
builds the unchanged `GaloisConstituentModel` from the named interfaces
and `DetectsDetOrbit`. The genuine theta data, the abstract
`two_fresh` statement, and the existing `Inputs` for the two readings
remain to be supplied.

All 13 files compiled in the final serial validation, with 45 axiom
audits using only `propext`, `Classical.choice`, and `Quot.sound`.
An earlier build handoff allowed a prerequisite check and a proof check
to overlap. The final validation ran serially after that build exited.

Report: `docs/research/rc-trace-limits.md`.
Results commit: `0156de3870dcf6ab724c2e1d7fa4a984473c618f`.
