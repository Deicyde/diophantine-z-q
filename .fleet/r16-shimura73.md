# r16-shimura73 (done 2026-11-17)

**Verdict.** Re-routing `r16CoreY` to the manuscript's own sources (Li 1975 p. 296; Shimura 1973 Thm 1) reaches the
known gap at diophantine_zq.tex L770-773 and stops there. Shimura's Euler-factor identity is an identity of total
characteristic polynomials on V_l(A_f); it does not mention the K_f-action, so it cannot give the per-embedding
trace iota(a_p) that `r16CoreY` asks for, and that the only Lean consumer (g13 -> commonConstituent_of_attached, l = 5,
one embedding, trace at cofinitely many p) needs. Recorded under "Known issues" in docs/research/r16-shimura73.md.
The gap is not repaired. The statement the chain would need is named: `R16ShimuraLi.ShimuraTotalToComponents`.

**Compiles** (standard axioms): ZInQKernel/Contrib/OneProof/R16ShimuraLi.lean has the printed-form leaves
`LiFrickePrinted` and `ShimuraThm1Printed` (both unread, locators UNVERIFIED), the uncited step `ConjNewform`
(conjugates of newforms are newforms), and the known-issue Prop. It proves `r16CoreYTotal_of_shimura_li`, which is
everything the two citations give, and `r16CoreY_of_shimura_li` (which also needs ConjNewform and the gap Prop).
scratch/r16-shimura73/FoldCheck.lean compiles both fold steps (open68, open69).

**Fold.** autofold only discharges top fields, so the fold is two steps. Step 1 is gen_r16_restore.py ->
TailZ75R16.lean: `r16CoreY` replaces heckeJ1DS, afShimura, afCharpolyDS965 and igusaGL2DSGalSome on the top. Step 2
is autofold.json. The dry run (on a temp tree) gives a net GLUE count unchanged vs the base (4/27 on 31). Rows that
disappear: those four. dsThm965Printed stays.

**#discharges** shows no discharge, since `r16CoreY` is not a field of the current top.

**Recommendation:** do not fold until Jack rules on the source issue.

**Remains:** readings of Li p. 296 and of Shimura Thm 1 (the Euler clause premise and its exceptional set), a print
for ConjNewform, and the ruling.
