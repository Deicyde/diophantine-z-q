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

## Step 2 (own implementation of slot-k 2.4; first adversarial batches)
- `construct.py`: section 2.4 from the text (multiplier given; q0 by CRT on 8, P, T; r_p by CRT on
  8, P, T, q0 plus search for symbols at earlier slots; r_l likewise). Checks (theta1)-(theta4) on
  each input and certifies C_|n|, C_|n|theta with `sel2.py` (definition-based, not Prop 0).
- `gens.py`, `families.py`: own generators. B = m beta t^2, t = 2730^2 a/b gives sqf(mB) = beta,
  theta = sqf(1 - beta t^2); theta = 1 via t = 2k/(beta + k^2).
- Results (all certified, (theta1)-(theta4) held on every input):
  - theta1 (theta = 1; beta = +-7, +-15, +-39, +-455, omega(beta) 1-4): 21/21.
  - omega1 (beta = +-p, p = 7, 23, 31, 47, 71, 10079, 999983, a random 8-digit p; theta with
    primes in classes 3/5/7): 16/16.
  - all3mod4 (all primes of beta = 3 mod 4, omega 1-7, both signs, theta with a 3 mod 4 prime): 28/28.
  - mostly1mod4 (one prime 3 mod 4, rest 1 mod 4, omega 2-7): 18/18.
  - thetacls (theta with {3,5,7} present / only 3s / only 7s / only 5s / only 1s / two 3 mod 4): 30/30.
- Negative controls on random30 seed 5 (shows the check is not vacuous):
  - wrong sign x = s: 6/30 certified; flipping [q0/p] for p != p0: 0/30.
  - **q0T** (symbols [q0/l], l in T, random instead of 0): 30/30 certified. So the condition
    [q0/l] = 0 is not used. Reason: in Lemma 2 (g = q0, G = T) symbols inside X = T u {q0} cancel,
    and l is not in S_1. slot-k 2.5 "What each slot does" says q0's symbols at T are dictated by
    the transfer: that justification is wrong (harmless superfluous condition). MINOR.

## Step 3 (symbolic checks with the Proposition 0 system)
- `t_symbolic_exh.py a b`: EXHAUSTIVE over classes mod 8, all symbols (reciprocity, theta3, theta4),
  both signs, every p0. (a,b) = (1,0) 2, (2,0) 32, (3,0) 768, (1,1) 2, (1,2) 16, (2,1) 32,
  (2,2) 512, (1,3) 256, (3,1) 768, (2,3) 16384, (4,0) 32768, (4,1) 32768, (1,4) 8192 cases:
  0 failures.  `2 2 free` (q0 symbols at T arbitrary): 2048 cases, 0 failures.
- `t_base.py`: Lemma 3 / 2.3 claims confirmed: with one auxiliary prime, dim 3 and +-p* in pi_1
  iff classes {7,3} or {3,7} (both symbols, both signs); with two auxiliary primes bases exist for
  every class of p*.  Note: +p* and -p* are always both in pi_1 (since (-1,-d) is in Sel_2), so the
  sign of beta never matters for membership; the sign only enters through x in q0's symbols.
- `t_variants.py v 1000 7`: randomizing one prescribed family of symbols at a time
  (random abstract data, omega(beta) <= 6, omega(theta) <= 5): none 0/1000 failures;
  q0P 676; q0T 0 (superfluous); rpT 344; rpq0 440; rpP 613; rpR 455; rlP 780; rlT 335; rlR 620;
  q0 = 7 mod 8: 1000 (dim 4); x = s: 527 (only C2 loses beta). Every other condition is load-bearing.

## Step 4 (more adversarial batches; report drafting)
- s0beta (P inside {3,5,7,13}, beta in +-{7,15,39,455}, theta nontrivial, every p0): 26/26.
- allm (3 random inputs x all 8 eligible multipliers, both signs): 24/24.
- p0var (omega(beta) = 7, 8; every choice of p0): 15/15.
- slope_site (t = u/v with all six |u + cv| prime = +-1 mod 8, v = 0 mod 8; R0 = eta F(t)/(t-1)^8,
  B = R0 s^2): 30/30.
- cores: isotropic cores k = 3, 4, 5, 6 (primes = 1 mod 21840, pairwise QR), all eligible m: 30/30.
- cores_extra crashed on a generator bug (duplicate core prime -> leg(p,p)); fixed, rerun pending.
- t_variants sign 1000 8: failures (470, all "C2 loses beta") occur exactly when theta has a prime
  = 3 mod 4 (530 others certified): confirms slot-k 3.3 negative-control statement.
- Report sections 1-2.5 drafted (all steps CORRECT).

## Step 5
- t_symbolic_exh (3,2): 24576 cases, 0 failures. (5,0) exhaustive was stopped (too slow); random
  abstract data t_variants none 5000 21 (omega(beta) <= 6, omega(theta) <= 5): 0 failures.
- test_site seed 13: 17 runs completed before the batch was stopped by a time limit, 17/17
  certified, omega(beta) 4-14, omega(theta) 1-6, up to 18 slots. (Bottleneck: the search for the
  symbols at earlier slots, 2^j candidates for the j-th slot; not factoring.)
- Report: sections 1-3 and 4.1-4.2 drafted.

## Step 6 (all batches done)
- cores_extra 30/30; small_slots (least primes; q0 = 3 in 4 runs, slots 17, 19, 41 ...) 26/26;
  large 9/9 completed (the 10th run hit the search budget of 10^7 candidates for a slot with ~19
  earlier-slot conditions: an implementation limit, not a failure); random30 seed 21 30/30;
  test_site_b (|n| <= 3000) 13/13.
- `summarize.py`: 16 families, 363 runs, 363 certified, 0 failures; omega(beta) 1-14,
  omega(theta) 0-9, slots 1-18; both signs of beta in every family except p0var.
- VERDICT: DL proved as written. No GAP found; findings F1 (superfluous [q0/l] = 0 with wrong
  rationale), F2 ("within one of the bound" overstated), remarks F3-F5.

## Step 7 (deliverables)
- docs/research/rv-slot-k-red.md complete (verdict, marks, audit 2.1-2.5, findings F1-F5,
  computations 4.1-4.5, repairs, scripts). .fleet/rv-slot-k-red.md written. Task complete.
