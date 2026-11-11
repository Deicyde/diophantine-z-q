# d2-check (fleet report)

**Task.** Numerical guard on the trusted hypothesis CertifiedRankDLRk on the curves C_{d₁}, C_{d₂}
(d₂ = d₁θ) that the descent-lemma slots actually produce. Note: docs/research/d2-check.md; scripts,
JSON and raw output in scratch/d2-check/ (log.md, out_table.txt).

**Verdict: PASS.**

- 30 admissible pairs (B, m) drawn (ω(β) ≤ 3, |β| ≡ 7 mod 8, θ < 10⁶; pairs.py builds them from
  a conic D² − θY² = β(2730²c′)² and re-checks admissibility with descent_search.py). Slots from
  slotk.construct with the smallest admissible prime per slot. All 30 slot choices satisfy every
  field of the Lean structure RouteK.Slots.
- **Only 10/30 pairs** have d₁, d₂ < 10¹² (20 curves, 19 distinct d), all with ω(β) = ω(θ) = 1.
- Lean slot facts hold on all 20: d ≡ 5 (8), squarefree, β | d, dim Sel₂ = 3 with β a first
  coordinate (sel2cong). PARI's ellrank gives the same Selmer dimension.
- Root number −1: 20/20. Analytic rank 1: 9/9 (d < 2·10⁶). ellrank [1, 1], s = 0: 20/20 (no upper
  bound 0). Points at effort ≤ 3 on 6 curves (all d₁). On all 6, the class of β lies in the span of
  the point and the torsion classes.
- No FAIL condition occurred, so the audit (selmerCertified_d1/d2, det_M5b_eq_one, T5b vs PARI)
  was not triggered.

**Limits.** No d₂ (5·10⁸ to 8·10¹¹) has a point or an analytic rank. There the evidence is only
root number −1 plus Sel₂ of dimension 3, and positive rank then needs finite Sha, which is what CR₃
assumes. The bound 10¹² keeps only the smallest slot configurations (no r_p slots, a single r_ℓ).
ellheegner on C_12549 timed out at 10 minutes. No Lean was run, and no files outside
scratch/d2-check, docs/research/d2-check.md and .fleet/ were touched.
