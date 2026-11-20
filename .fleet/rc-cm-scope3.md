# CM field-of-definition scope: complete

The previous run's wrapper patch now checks. The prepared genus and companion
proofs specialize scoped descent at their original forms, then transport the
evaluation along the order discriminant equality. The broad-to-scoped
implication and the two level-one cases are unchanged. No print was added.

All seven `CMScope` modules compiled in serial. `ScopeCheck`, `CoreCheck`,
and `ConsumersCheck` passed: all 29 audited declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The consumer check passes
the selector's `hCMField` directly at the anchor's CM input type.

Switch the `hCM` binders of `ParamJoin.genus_values`, `ring_values`,
`prepared_values`, and `missing_values` to their `CMScope` wrappers. Switch
`SelectorTotal.ParamInputs.hCMField` to `CMScope.ParamInputs.hCMField` and use
the scoped `genusInstance` and `oddStagedOfParamValues`. Switch
`HeegnerAnchor.cmPointsAtScale.hCM` and `genuineHeegnerAnchor.hCM` to the
scoped wrappers; only these two also take
`h2N : 2 ∣ newformLevel (Ecurve ℓ)` to preserve the full conductor range.
The [report](../docs/research/rc-cm-scope3.md) lists the forwarding binders.

General-level `CMFieldOfDefinitionScoped` remains the next descent lane's
input. The actual-curve lane owns the Lean proof of level parity for the
anchors. See the [verification log](../scratch/rc-cm-scope3/log.md).

Final implementation and report SHA: `bccadac739860dd786259d473660388767943662`.
Resolve the separate final handoff commit with
`git log -1 --format=%H -- .fleet/rc-cm-scope3.md`.
