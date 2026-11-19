# rc-heegner-values results

- Base: `433db7d632d91dc9542deeffbac7cc677acd64ca` merged with `e68f39edbb180eb48343871210e2638d2c9f5173` using `git merge --no-edit`; clean merge.
- Scale match: `CSTParam E` takes `f`, `hf`, `Lat`, `hLat`, `hCM := hNC`, `κ`, `hκ`; `p.f`, `p.Lat`, `p.κ` match by definition. Both consumer contexts have these inputs.
- CCL Theorem 2.15, p. 3730 (archived source audit): geometric trace with the full old conductor as source base conductor and multiplier one. No fixed-scale analytic equality.
- Missing comparison: `π_ℂ(x_d ⊗_{ι_d} ℂ) = phiAn E f Lat κ (cmPoint A B (D_K d²))` for a form representing the same embedded `x_d`, at each admissible `d`. CM specialization of the global comparison, proper restriction of the three-part package in scope.
- Stop: `CCLGenuine` moves the comparison into its anchor. No new theorem or print. `MissingParamValues`, `halgG`, and `halgR` unchanged.
- Later bindings: `FullAnchor.field` is separate from `CCLGenuine`; existential anchor form does not imply `formAtLevel` or `companionForm`. Widening requires root decision.
- Compile / axiom audit: no new Lean files or declarations; not applicable. No Lean processes started.
