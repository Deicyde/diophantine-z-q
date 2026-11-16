# Independent review of the 198-to-196 elimination

**Verdict: PASS within the assigned scope. No overclaim or missing mathematical join found in the new elimination, its coefficient formula, or its transfer from the receiving 198-variable Busy Beaver theorem.** The inherited 198 arithmetic remains a separate dependency; it is neither strengthened nor reproved by this review.

Reviewed components: `elimination196.tex` (168 lines), `theorem196.tex` (23 lines), and `bibliography196.tex`, as bound by SHA-256 in `CHECKS.json`. The upstream source is revision `5c35db3253a70b0875acec4b451cdaac4da3c8fd`. The parent row table has SHA-256 `c55d7eefe41f62fee88b467e3ea8f6be8ba1e66f6a94b30eb74b39f6f6e7efad`; the unbalanced new table has SHA-256 `3b6ab20da25bced159559c35e512e2bb2e56959b734b4265c8f80a7bd9cdb1c1`.

## Elimination lemma and full solution domain

`elimination196.tex:9–39` states the needed two-sided localization argument. At an old solution the inverse diagonal scaling exists; at a new solution the same nonvanishing and retained identities permit recovery. The constants are nonzero rational numbers and all exponents are integers. Thus both maps are rational on the entire relevant zero sets, fix the input, and undo one another. Passing to the sum of squares is valid over the specified field Q.

The actual application explicitly fixes the guard and power coordinates, so there is no ambiguity about using the retained power identities on both sides. The nine old rows and their new row numbers are:

| Old row | New row | Content |
|---:|---:|---|
| 1 | 1 | input square |
| 26 | 26 | first inverse weight |
| 27 | 27 | first weight square |
| 39 | 39 | second inverse weight |
| 40 | 40 | second weight square |
| 48 | 48 | first scalar product |
| 49 | 49 | scalar contact product |
| 60 | 58 | scalar normalizer square |
| 63 | 61 | forced-prime equation |

I compared these literal equations after renumbering, independently of their names and of the row certificate. They match the formulas at `elimination196.tex:46–68`.

The scalar contact identity was independently expanded as a polynomial in u=x^2. It gives exactly

\[
RJ=(51x^2+103)(51x^2+2503)(51x^2+2504)(1632x^2+80471).
\]

Every factor is strictly positive for every rational x, including x=0. Hence R and J cannot vanish on any solution. With A>0, the forced-prime row gives R=Ar(x)/(1+22201r(x))>0. The two inverse equations exclude w_0=0 and w_1=0 without using any inherited arithmetic theorem.

The deleted old rows are 58 and 59, and the deleted old coordinates are 80 and 95. Their actual equations are x_79^2=x_80 and x_94^2=R x_95. The retained square identities therefore determine the unique values x_80=w_0^4 and x_95=R^(-1)w_1^4 stated at lines 71–74. In particular, the factor R^(-1) in the second recovery formula is necessary and correctly present.

The multiplier tables at lines 81–100 were transcribed directly into a fresh checker. They agree with the upstream configuration, including the signs of the nine constant scalings and H=31581660^14, K=82479248H. None rescales the input, R, w_0, or w_1. The coordinate order is exactly the old order with 80 and 95 removed.

For all 182 retained rows I expanded the old substituted row and the new row in the same Laurent ring, reducing only the displayed retained square and inverse-weight relations. I inferred the common scalar and exponent shift from the two expansions instead of reading them from the supplied certificate. Every coefficient comparison passed. The five rows that become zero after power reduction are also covered by the separate literal guard comparison, so their validity is not inferred from a vacuous zero identity. Both deleted rows reduce to zero.

This proves the full-zero-set bijection claimed at lines 5–7 and the projection equality at lines 117–123. It does not discard torsion, tangent, identity, repeated-point, sign, or zero-test branches allowed by the parent. Those coordinates may vanish; only the three proved nonzero scaling coordinates are divided by. No new completeness restriction appears.

## Exact polynomial and coefficient formula

I rebuilt the unbalanced quartic by squaring and summing the actual 182 new rows using exact integer arithmetic. This fresh expansion agrees coefficientwise with the upstream polynomial file. All rows are primitive integer quadratics. The result has 196 occurring coordinates, degree exactly four, and 2,943 coordinate monomials. The input fourth-power coefficient is 1, so the content is 1.

The only positive-parameter-degree terms in delivered one-based coordinates are

\[
-2A x_{102},\qquad -44402A x_{102}^2x_{114},\qquad A^2x_{102}^2.
\]

They have no constant-part coefficient. Thus the zero-based indices Y_101 and Y_113 in `elimination196.tex:139–145` are correct, and positive specializations cannot cause a support cancellation. The largest constant coefficient is exactly

484991541504995159662206970923766531374664106904986910720.

Since A_N>=149^3>44402, A_N^2 dominates both linear parameter coefficients. This proves the exact maximum in lines 124–152 for every N>=1. Direct integer comparison gives 149^26<K_fixed<149^27. Therefore N=6 still lies below the crossover and every N>=7 lies above it, as lines 155–157 say. The new statement uses the unbalanced polynomial-in-A table throughout; it does not mix in the different balanced height formula from the upstream headline theorem.

## Busy Beaver transfer and inherited scope

The retained standalone parent file `height-bb/q198bb-proof.tex:26–49` uses the same unbalanced family and parameter N_BB=BB(2^1000). Its coefficient lemma at lines 827–830 proves A_BB^2+1<BB(2^2000); lines 867–870 give N_BB>=54. Consequently the new crossover N>=7 is automatic, and the height asserted in `theorem196.tex:15–19` is exactly the same A_BB^2. No machine, state budget, input search, or threshold program needs alteration.

The statement-scope distinction was checked explicitly. The standalone parent component says “subject to” its arithmetic premises at lines 26–29. The receiving manuscript `work/v18-198-bb-integration-20261115/assembled-local/quartic_v18.tex:101–104` instead states the established q198bb:fixed theorem for its printed parent rows; this is the theorem consumed by `elimination196.tex:159–168`. The unconditional receiving statement is not obtained merely by dropping the standalone qualifications. It uses the receiving manuscript's already established 198 arithmetic and BB results. The new equivalence preserves that dependency exactly, as lines 5–7 say. I did not reopen those inherited proofs.

Applying the bijection at that same fixed integer parameter gives the equivalence with Z and exactly 195 existential coordinates in `theorem196.tex:9–13`. Its fixed parameter is not counted as a variable, and its upper-bound wording makes no minimality claim. No missing join was found.

## Evidence and limits

`verify196.py` is a fresh standard-library checker. It imports or executes none of the upstream producer/checker code and none of the root's independent audit. `CHECKS.json` records all inferred row identities, the literal guards, exact support and height results, and source/component hashes. The root's AUDIT.md and RESULT.json, and Fable's relay report, were read as comparison evidence after identifying the actual pinned sources.

The source-consumer comparison is against the pinned unbalanced JSON rows. Final TeX row rendering, assembly, publication, and preservation of the inherited manuscript are separate checks. No manuscript, source component, GitHub item, or relay file was changed. No further optimization was attempted.
