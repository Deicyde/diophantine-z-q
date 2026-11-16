# Supplement: explicit row-multiplier reference

**PASS.** The original review remains valid. No mathematical change or new assumption was introduced.

The current `elimination196.tex` has SHA-256 `34c7a434ccc12031fe28ee0ade7283f98e42c99fefdbcae5977afb9558ae5485`. At lines 109–111, the sole change inserts the reference to Table `q196:rowmultipliers` and says that it gives each source row, target row, and multiplier. Replacing that exact span by the previously reviewed sentence reconstructs SHA-256 `c7e72648ab6536967ddaa31b144cd2fe480ea6b7fb893e526a0f6bd285319f1d`, exactly the prior CHECKS.json binding. Thus there are no other byte changes.

The checked `tables/q196-rows.tex` has SHA-256 `9fd8c918535ad5b7364360fb6f1926c0ee935fbf9bb34ccc7cccc95d5411cd6b`. Its identity convention is printed at lines 1793–1803:

\[
q_i=\eta_i R^{-s_R}w_0^{-s_0}w_1^{-s_1}f_r(\Phi(\mathbf Y)).
\]

The table beginning at line 1809 has exactly 182 entries. It covers every parent row except the deleted rows 58 and 59, and every target row 1 through 182 once. Each exponent triple and each nonzero rational multiplier agrees with the independently inferred identity recorded in the original CHECKS.json, with the reciprocal constant required by the displayed convention. The five retained power identities, which reduce to zero on both sides, have the stated trivial multipliers and were separately checked literally in the original review.

To bind this comparison to the actual printed equations, I also parsed all 69 printed integer coefficient aliases and all 182 displayed residuals. Every residual agrees coefficientwise, including its sign, with the pinned unbalanced JSON table used by the original independent expansion. The retained inverse/square identities and the definitions of H and K have the correct coordinate indices and values.

`SUPPLEMENT.json` and `verify_supplement.py` record and reproduce these checks. The original REPORT.md and CHECKS.json were preserved byte-for-byte. No manuscript, author component, table, or GitHub item was changed. This supplement is limited to the added reference and its table; the frozen Jose196 target and inherited arithmetic scope are unchanged.
