# rc-heegner-values

Scoped stop on #83. The existing `hf`, `hLat`, `hNC` and `hκ` build
`CSTParam` with exactly the selector’s `f`, `Lat` and `κ`. The swap moves
the fixed-scale comparison into `CCLGenuine`. Theorem 2.15 supplies the
geometric trace; identifying the algebraic image `π(x_d)` with `phiAn` at
the same CM root and scale is consequence glue. This is the CM-point
restriction of `AlgebraicParametrizationAtScale`. It requires less than
the full model, field-of-definition and all-points package, but the cited
norm theorem does not supply it.

No Lean changes, builds or axiom checks. `MissingParamValues`, `halgG`
and `halgR` remain open. The fixed-scale comparison stays with
`rc-param-at-scale` on `rc-x0-model` for the global route. The anchored
print and same-datum class-field identification stay with the cloud root
and field dictionary owner; the separate field-of-definition locator is
unverified. The curve inputs retain their existing owners and any selector
widening is a root decision. No manuscript or primary-source error was
found in the steps checked.

Final result SHA (report and log): `099957c7069ab47c3b782387c7d49d7706c2025e`.
The final branch commit adds this handoff; its SHA can be read with
`git log -1 --format=%H -- .fleet/rc-heegner-values.md`.
