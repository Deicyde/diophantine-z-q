# hodge-fil1

**Scoped stop on `dcc3d7723`.** Keep the Hodge-number clause in `scholzeH1AbVar` for now. The tree gives the two possible weights but does not determine their multiplicities from the surviving inputs. The old pairing proof uses the two Picard hypotheses removed from the headline. The missing statement is `HodgeFil1.TatePolarizationSymmetry`: existence of a nondegenerate pairing on the row's rational Tate module with cyclotomic multiplier.

`ZInQKernel/Contrib/OneProof/HodgeFil1.lean` compiles. With that symmetry, the first two Scholze clauses and existing T10 imply `dim Fil¹ = g` for every `g`, including the surface case. All four theorems have only the three standard axioms. The transitive dependency check excludes the original Hodge-number input and all audited consumers. The discharge check against the actual headline recognizes the conditional proof and lists the missing symmetry among its assumptions.

L10996 (S16) is uncited, an omitted justification rather than a known wrong assertion. Scholze's cited corrigendum changes the period-site definitions and preserves the comparison, per the existing locator audit. The source issue stays open on this base. The native stabilizer quotient and descended Picard family are a possible way to supply the missing compatible Weil pairings without proving full Picard representability.

No new leaf, no fold. The count preview, conditional on proving the symmetry, gives 5 LEAF / 26 GLUE in strict and strictest before and after. See `docs/research/hodge-fil1.md` and `scratch/hodge-fil1/`.
