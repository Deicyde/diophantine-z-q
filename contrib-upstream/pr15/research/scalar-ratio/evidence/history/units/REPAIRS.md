# UnitCriterion and BoundaryCup candidate repairs

Author: model agent `/root/scalar_units_lean`. Scope is native Lean 4.35 proof elaboration, not independent mathematical acceptance. Original received bytes remain preserved in the ZIP and intake extraction. No old frozen module, packet, toolchain, dependency, or root Lake configuration was edited.

## Result

Both full source modules compile under the pinned Lean 4.35.0 with `-j1 -Ddebug.skipKernelTC=false`. Final logs `unit-02.log` and `cup-02.log` are empty (exit zero, no warnings). `BUILD_RECORD.json` binds exact sources, flags, dependency search paths, artifacts and logs. The direct compilation uses freshly compiled Coordinate/CommonStrict artifacts supplied by the other worker and copied into this worker’s standalone lib because Lean resolves a common module prefix from the first search root. Parent will independently rebuild the complete source tree.

## Repairs

1. `UnitCriterion.transported_ratio`: removed unreachable `<;> ring` after `field_simp [hd, he, ht, hs]`, which already closes the goal. No statement, hypothesis, or definition changed.
2. `BoundaryCup`: replaced `(d.J : Matrix _ _ K)` coercions with explicit `(d.J : Matrix (Fin 2) (Fin 2) K)` at their occurrences. The failed elaboration could not infer the coercion’s remaining row index. This states the existing unit matrix type explicitly; no parameter type or premise was strengthened.
3. `BoundaryCup.normalization_defect`: introduced the local derived fact `heta : d.eta ≠ 0 := d.area_ne` and supplied it to `field_simp`. The candidate’s direct `d.area_ne` term referred syntactically to `area d.v d.x`, so inverse cancellation for the accessor `d.eta` was left unsolved. The nonzero fact is definitionally the existing hypothesis, not a new theorem assumption. The final `field_simp` closes the goal, so the now-unnecessary final ring tactic was removed.
4. Parent had already replaced the uncompiled-candidate header with a current-verification link; exact original/working diffs include that provenance annotation.

## Retained diagnostics

- `unit-prefix-01.log`: missing Mathlib NonsingularInverse cache artifact before the parent fetched the exact pinned cache closure.
- `unit-prefix-02.log`: scalar/unit prefix compiled in a scratch-only module using the already cached Adjugate import, with unreachable-tactic warnings. Partial debugging evidence only.
- `unit-prefix-03.log`: complete prefix through `valuation_equal_of_unitRelated` compiled without warnings against NonsingularInverse after cache completion.
- `unit-01.log`: initial full compile could not locate CommonStrict because the first same-prefix search root was the worker’s own empty library. Copied the other worker’s fresh dependency artifacts into the owned library, without changing their sources or bytes.
- `unit-02.log`: full UnitCriterion PASS, no diagnostics.
- `cup-01.log`: original BoundaryCup matrix coercion error and the unresolved eta cancellation goal.
- `cup-02.log`: full BoundaryCup PASS, no diagnostics.

## Scope limitations

No custom axioms, placeholder proofs, native evaluation, trust bypasses, heartbeat increases, or theorem-premise changes were introduced. Zero functionals, zero common normalization and nonunit common scale remain permitted exactly as specified. The quotient theorem alone retains its nonzero denominator assumptions. The valuation consumer remains an abstract multiplicative monoid-with-zero homomorphism trivial on R-unit images; it does not construct an arithmetic valuation.

This native compile is not a protected comparator, replay, external-kernel or paranoid result. No cloud check was launched, no commit or push was performed, and the actual Selmer/Poitou–Tate application remains open. Parent performs fresh combined auditing and separate model review.

## Source SHA-256

- `Research/DerivativeSwitch/UnitCriterion.lean`: `efd9f4404b9760f9d7ebc2cb0874f21f517ed3868e9e23f78fd0465a2c03e45a`
- `Research/DerivativeSwitch/BoundaryCup.lean`: `64750e7706f82cf0a47b76c80503bcab0577c2aa18f9703c09b4b8288be0df90`
