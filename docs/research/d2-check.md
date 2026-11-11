# d2-check: numerical guard on CR₃^DL,Rk on the curves the descent lemma produces

**Verdict: PASS** (20 curves from 10 of 30 drawn pairs; no root number +1, every computed analytic
rank 1, every ellrank upper bound 1, the class of β realized on all 6 curves with generators).

## Hypothesis under test

`RouteK.Rank.CertifiedRankDLRk` (ZInQKernel/RouteK/RankDL.lean): for slot inputs `Inputs β θ p₀`
there is a slot choice `D` with points of infinite order on `C_{d₁}` and `C_{d₂}`, d₂ = d₁θ,
C_d : y² = x³ − d²x. Lean proves for every slot choice (`slots_d₂_facts`, `sel_of_selmerCertified`):
d ≡ 5 (mod 8), d squarefree, β | d, and `SelmerCertified d β` (#Sel₂(C_d) = 8 with a class (β, b)).

## Method (scripts and raw output in scratch/d2-check/, log in log.md)

1. **Pairs** (`pairs.py 30 2026` → pairs.json). β odd squarefree, ω(β) ≤ 3, primes < 200,
   |β| ≡ 7 (mod 8); θ squarefree, θ ≡ 1 (mod 8), prime to 2730β, a square mod 3, 5, 7, 13,
   log-uniform in [17, 10⁶). A primitive solution of D² − θY² = β(2730²c′)² (PARI qfsolve/qfparam),
   m a random signed divisor of 2730 with sign(m) = sign(β), B = mβc²/D². Then sqf(mB) = β,
   sqf(m(m − B)) = θ; admissibility (square denominator, 0 < B < 1/2, v_p(B) ≥ 4 on S0) and both
   square classes are re-checked with `descent_search.admissible`/`sqfQ`
   (scratch/rv-route-k/descent_search.py). Drawn θ range: 15649 – 897121.
2. **Slots** (`slots.py` → slots.json). `slotk.construct` (scratch/slot-k/slotk.py) with its prime
   search replaced by the smallest prime in the class mod 8 meeting the same symbol constraints;
   p₀ = min P. Every slot choice (30/30) re-checked field by field against the Lean structure
   `RouteK.Slots` (legBit p a = bit of (a/p)): all fields hold.
   **Kept** (d₁, d₂ < 10¹²): **10 of 30 pairs** (#3, 4, 5, 7, 11, 15, 17, 18, 22, 23), 20 curves,
   19 distinct d (#4 and #18 share β = −191, d₁ = 9741). All kept pairs have ω(β) = ω(θ) = 1
   (one slot q₀, one slot r_ℓ): pairs with more primes give d₂ > 10¹².
3. **Slot facts** on the 20 curves: d mod 8 = 5, squarefree, β | d, and exact 2-descent
   (sel2cong.py) dim Sel₂ = 3 with β a first coordinate: 20/20. PARI's ellrank gives the same
   dim Sel₂ = 2 + r₂ + s = 3 on all 20.
4. **Curves** (`curves.py` → curves.json): ellrootno; ellanalyticrank (real precision 19) when
   d < 2·10⁶ (9 curves); ellrank at effort 0, 1, 2, 3, stopping when r₁ = r₂ and r₁ points are
   found; Kummer images (sqf x, sqf(x − d)) of the points, with the 2-torsion images (−1, −d),
   (d, 2), (−d, −2d); test whether β is the first coordinate of an element of their span.

## Table (scratch/d2-check/out_table.txt)

```
d | primes (mod 8) | pair#/role beta theta | slot facts (d%8, sqf, beta|d, dim Sel2, beta in pi1) | rootno | anrank | ellrank r1..r2 s (effort) | #pts | Kummer images | beta in span
23749 | 11(3) 17(1) 127(7) | #3/d1 -127 33289 | 5 True True 3 True | -1 | 1 | [1, 1] 0 (0) | 1 | [[187, 374]] | True
790580461 | 11(3) 17(1) 127(7) 33289(1) | #3/d2 -127 33289 | 5 True True 3 True | -1 | - | [1, 1] 0 (3) | 0 | - | -
9741 | 3(3) 17(1) 191(7) | #4/d1 -191 281761 | 5 True True 3 True | -1 | 1 | [1, 1] 0 (0) | 1 | [[51, 102]] | True
2744633901 | 3(3) 17(1) 191(7) 281761(1) | #4/d2 -191 281761 | 5 True True 3 True | -1 | - | [1, 1] 0 (3) | 0 | - | -
374821 | 31(7) 107(3) 113(1) | #5/d1 -31 15649 | 5 True True 3 True | -1 | 1 | [1, 1] 0 (0) | 1 | [[-31, -31]] | True
5865573829 | 31(7) 107(3) 113(1) 15649(1) | #5/d2 -31 15649 | 5 True True 3 True | -1 | - | [1, 1] 0 (3) | 0 | - | -
34013 | 7(7) 43(3) 113(1) | #7/d1 -7 788449 | 5 True True 3 True | -1 | 1 | [1, 1] 0 (0) | 1 | [[-7, -7]] | True
26817515837 | 7(7) 43(3) 113(1) 788449(1) | #7/d2 -7 788449 | 5 True True 3 True | -1 | - | [1, 1] 0 (3) | 0 | - | -
2877 | 3(3) 7(7) 137(1) | #11/d1 7 234361 | 5 True True 3 True | -1 | 1 | [1, 1] 0 (0) | 1 | [[7, 7]] | True
674256597 | 3(3) 7(7) 137(1) 234361(1) | #11/d2 7 234361 | 5 True True 3 True | -1 | - | [1, 1] 0 (3) | 0 | - | -
359053 | 23(7) 67(3) 233(1) | #15/d1 23 52081 | 5 True True 3 True | -1 | 1 | [1, 1] 0 (3) | 0 | - | -
18699839293 | 23(7) 67(3) 233(1) 52081(1) | #15/d2 23 52081 | 5 True True 3 True | -1 | - | [1, 1] 0 (3) | 0 | - | -
12549 | 3(3) 47(7) 89(1) | #17/d1 -47 342889 | 5 True True 3 True | -1 | 1 | [1, 1] 0 (3) | 0 | - | -
4302914061 | 3(3) 47(7) 89(1) 342889(1) | #17/d2 -47 342889 | 5 True True 3 True | -1 | - | [1, 1] 0 (3) | 0 | - | -
9741 | 3(3) 17(1) 191(7) | #18/d1 -191 253969 | 5 True True 3 True | -1 | 1 | [1, 1] 0 (0) | 1 | [[51, 102]] | True
2473912029 | 3(3) 17(1) 191(7) 253969(1) | #18/d2 -191 253969 | 5 True True 3 True | -1 | - | [1, 1] 0 (3) | 0 | - | -
12419789 | 139(3) 199(7) 449(1) | #22/d1 -199 63361 | 5 True True 3 True | -1 | - | [1, 1] 0 (3) | 0 | - | -
786930250829 | 139(3) 199(7) 449(1) 63361(1) | #22/d2 -199 63361 | 5 True True 3 True | -1 | - | [1, 1] 0 (3) | 0 | - | -
7701 | 3(3) 17(1) 151(7) | #23/d1 151 70249 | 5 True True 3 True | -1 | 1 | [1, 1] 0 (0) | 1 | [[-51, -102]] | True
540987549 | 3(3) 17(1) 151(7) 70249(1) | #23/d2 151 70249 | 5 True True 3 True | -1 | - | [1, 1] 0 (3) | 0 | - | -
curves: 20 failures: 0
```

## Outcome

- Root number −1 on 20/20 curves.
- Analytic rank 1 on the 9/9 curves with d < 2·10⁶ (all d₁ except 12419789).
- ellrank bounds [r₁, r₂] = [1, 1], s = 0 on 20/20; no upper bound 0.
- Generators found on 6 curves (d₁ = 23749, 9741 (twice), 374821, 34013, 2877, 7701). On each
  one, β is a first coordinate of the span, and never of the torsion span alone: the generator's
  class is β itself or β times a torsion first coordinate (e.g. d = 9741, β = −191: image
  (51, 102), and −191·(−9741) = 51 mod squares).
- On the other 14 curves (all ten d₂ ≥ 5.4·10⁸, and d₁ = 12549, 359053, 12419789) ellrank at
  effort 3 finds no point. Its r₁ = 1 there is not a point but the parity step (dim Sel₂ = 3,
  Cassels–Tate), so it is conditional on finiteness of Sha. ellheegner on C_12549 did not finish
  within 10 minutes and was dropped.

**PASS.** No FAIL condition occurred, so the audit of selmerCertified_d₁/d₂, det_M5b_eq_one and T5b
against PARI was not triggered. The Selmer side (dim 3, class β) agrees between Lean's slot facts,
sel2cong and PARI on all 20 curves.

## Limits

- Only 10 of 30 pairs survive the bound 10¹², all with ω(β) = ω(θ) = 1. The bound selects the
  smallest slot configurations, so pairs with r_p slots (ω(β) ≥ 2) or several r_ℓ are untested here.
- Unconditional evidence of positive rank (an analytic rank 1, or a point) exists for 8 of the 19
  distinct d: the 9 analytic-rank curves (d = 9741 twice), which include the 5 distinct d with points. No d₂ has either. On those curves
  the evidence is root number −1 with Sel₂ of dimension 3: positive rank then follows from finite Sha
  (2-parity), which is exactly what CR₃ assumes.
- This is a consistency check of the hypothesis, not evidence for it beyond the sample.
