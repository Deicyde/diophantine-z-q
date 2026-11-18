| Check | Status | Result |
|---|---|---|
| Base source census | VERIFIED | Three current bundle projections lead to one pointwise application: `dual_of_H1` at finite `F/ℚ_p`, `ℓ = p`, in all dimensions. See `census.md`. |
| Base classifications | VERIFIED | The existing kinds table has 29 H entries (5 LEAF / 24 GLUE in both modes), and 33 headline entries. |
| Milne locators | VERIFIED (recorded reading) | v2.0 I.12.1(a), p. 55 and Rem. 12.5, p. 56 are recorded in the kinds table. The older 1986 locator and the proposed pro-étale comparison locator were not checked against print. |
| Lean census of base headline | VERIFIED | 113147 project constants; 18 marked declarations: three projection readers, eight Scholze readers, five bundle forwarders, and the projection and constructor. No other T10 instance. |
| Local statement | VERIFIED | `T10Etale.T10_TateDualityLocal` compiles using the original coefficient, Tate-module, and transport definitions. |
| Specialization | VERIFIED | `t10Local_of_tateDuality` compiles; `#print axioms` reports only the three standard axioms. |
| Local readers and compatibility | VERIFIED | All eight readers in the live route and two adjacent compatibility readers compile with `_loc`; the ten examples compile with the old statements. All ten axiom reports are standard. |
| Bypass | VERIFIED | The generated chain and `frozenTarget_t10` compiled with standard axioms. The old T10 proposition is present below the base H and headline tops, absent below both new tops. The 32 other entries have identical types. |
| Discharge scan | VERIFIED | Base headline: 33 open entries, 15257 theorems checked, 347 matches. No match for the old general T10 field. |
| Replacement kinds row and count | VERIFIED | Proposed `t10TateDualityLocal`, added, consequence, GLUE/GLUE, pending review. Both readings stay at 5 LEAF / 24 GLUE (29 H entries); total headline entries stay at 33. |
