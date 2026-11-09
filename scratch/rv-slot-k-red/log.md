# rv-slot-k-red log

## Step 0 (setup)
- Read descent-alt.md and slot-k.md in full.
- Python venv with sympy + cypari2 at /tmp/rvred-venv (not committed).

## Step 1 (independent descent + Proposition 0 cross-check)
- `sel2.py`: exact Sel_2(C_d) from the definition (local images: odd p|d torsion span, oo sign,
  2 by 2-adic point search). Sanity vs PARI ellrank on 27 small d: dim Sel2 = 2 + R + s in all cases
  (e.g. d=17: Sha[2] rank 2, dim 4; d=113: dim 4).
- `prop0.py`: Selmer system of slot-k 2.1 implemented from the text.
- `t_prop0_full.py 2 600`: Sel_2 as a subspace, definition vs Proposition 0, 600 random d with 1-8
  primes < 3000, classes {1:128, 3:162, 5:153, 7:157}: 0 mismatches. Prop 0 CORRECT (all four
  classes mod 8, tested).
- By hand: E1/E2 rows from the torsion span at odd p (CORRECT); real place (CORRECT); place-2 rows
  for c = 5 from the three generators (5,2), (-1,-5), (1,5) [x=1/4] (CORRECT).
