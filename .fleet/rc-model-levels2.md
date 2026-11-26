# RC model levels 2 handoff

The checked construction reaches the finite-group quotient of the exact-order cover. The divisor restriction squares give arbitrary scalar extension. The Jacobian formulas give the geometric `(ZMod N)ˣ` algebra action, including its group laws, field-valued generator action, and compatibility with scalar extension. Levels one and two have the identity action.

`DetectorCyclicLevelAlgebra` fixes the finite-group invariants on the universal short chart under `2 ≤ N`, `5 ≤ ell`, and `¬ ell ∣ N * N.totient` (tex 8366–8368). Over a chosen coefficient point, `detectorCyclicLevelPoints` identifies its points with cyclic subgroups of order `N`, including over the algebraic closure of the detector residue field. The finite quotient commutes with scalar extension over the coefficient chart and is flat there when the group order is a unit.

The short scaling formulas and the polynomial weights compile. The remaining theorem descends them to an internal grading of the cover preserved by unit multiplication. The degree-zero quotient, its coarse pair points, and smoothness are still needed for `PMWire.GoodRow`. `GenericFibreComparison` remains uninstantiated. The report sizes the pointwise operator, Néron extension, and CM comparisons. [Research report](../docs/research/rc-model-levels2.md)

All 17 modules passed the final serialized Lake build. The 87 axiom outputs contain only the permitted axioms. The initial prerequisite build exceeded the single-compiler limit. Subsequent builds serialized all compiler invocations in the required resource scope.

Verified source and report commit `3bfdf4d0879575f7c4134b13b5e51d8a6a81890d`. The final handoff SHA is returned by `git log -1 --format=%H -- .fleet/rc-model-levels2.md`.
