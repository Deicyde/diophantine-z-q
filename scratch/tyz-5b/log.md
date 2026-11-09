# tyz-5b log

## Step 0 (setup)
- No earlier run. Sources: TYZ arXiv:1411.4728v1 (only version; Period7.tex), Smith arXiv:1603.08479v2
  (cnc.tex, cnc2.tex) downloaded to a temp dir outside the repo. PARI via cypari2 in a temp venv.
- Slot-k output: |n| = |beta| q0 * (glue primes = 1 mod 8), |beta| = 7 mod 8, q0 = 3 mod 8,
  so |n| = 5 mod 8, n odd; theta = 1 mod 8 so |n theta| = 5 mod 8. Only row 5b needed; row 6 never.

## Step 1 (TYZ statement) -- findings
- TYZ Thm 1.2 (label lg') = Thm 3.5(2) (label m3), arXiv v1 Section 1 and Section 3.1.
- Statement combines the brackets: "first sum = second sum = 0 mod 2". For n = 5 mod 8 the
  second sum contains the (7,3) terms (= Smith 5b) and (5,1) terms.
- Proof of Thm 3.5(2) (last subsubsection of Section 3, "Proof of Theorem m3: part (2)") shows
  separately: coefficient of tau(1/2) (d0 = 7, d1 = 1,3 => d1 = 3) is even, and coefficient of
  tau((1-i)/2) (d0 = 5) is even. The tau(1/2) bracket is exactly Smith's 5b sum, with no
  ambiguity about d1 = 1 (d1 = 3 mod 8 forces d1 > 1).
- If d1 = 1 is allowed in the statement (as the proof needs: Z(n) term), statement-level sums are
  5a and 5a+5b, so "5b odd => certified" follows from the statement itself. Literal reading
  (d1 > 1) gives second sum = 5a + 5b + g(n); then one needs the proof's separate bracket.

## Step 2 (row 5b) -- a new, shorter proof by forest expansion (no Smith closures)
Definitions fixed: V = odd primes of n; a_ij = (p_j/p_i)_+; L = Laplacian (L_ii = sum_j a_ij) = Smith's A;
y_i = [p_i = 3 mod 4], z_i = [p_i = +-3 mod 8]; reciprocity a_ij + a_ji = y_i y_j.
kappa_rho(B) = det L_B[B-rho, B-rho] = # arborescences of induced graph on B rooted at rho (mod 2).
Lemmas (all proved on paper, all VERIFIED on abstract random data, scripts forest_check.py, lemma_check.py):
- Forest lemma F (all-minors matrix-tree over F_2): det L[V-F, V-W] = # forests rooted at F with each
  tree containing exactly one W-vertex.
- Redei (STANDARD, derived from genus theory): y(B)=1: g(B) = kappa(B) (all roots equal);
  y(B)=0: g(B) = sum_rho z_rho kappa_rho(B).
- det M_1 = sum over forests with an even number of trees of prod_T z_root y(T)
  = sum over partitions into class-3 blocks (even number) of prod g.  [3000/3000]
- kappa_i + kappa_j = sum over 2-forests rooted at {i,j} of c(T_i), c = column sums of L. [VERIFIED]
- R1: for class-1 S, sum over class-1 partitions = sum over class-3 partitions (proved by comparing
  z-coefficients with the kappa_i + kappa_j lemma).  This is Smith's row 1 in disguise.
- det M_5b = sum over partitions with one class-7 block and all other blocks class 3; with R1 this is
  the TYZ tau(1/2) bracket.  So Smith row 5b holds (abstract data: 0 mismatches).

## Step 3 (RK6 rule for row 5b) -- proved via Lemma K + bordered lemma
- Lemma K: for odd n > 0, n = 5 mod 8, Sel_2 = T + H with H = {b1 = 0, a0 = lambda.u}; H ~ ker M_1 via
  sigma -> (u+v, u) (i.e. (S(ab), S(a))).  Proof: direct comparison of slot-k Sigma(C) (c = 5 rows) with
  the kernel equations of M_1; uses lambda.s = 0, mu.t = 0 from summing rows (y(V) = 0).
- Bordered lemma: det [[M, v],[v^T, 0]] = v^T k (F_2, corank 1).  v = (0, y): v^T k = lambda.u = [|a|_odd = 3 mod 4].
- VERIFIED on actual curves (rule_check.py, exact descent sel2cong.py, PARI class groups for TYZ):
  seed 11: 300 n (omega 2-6, p<400): K1 300/300, minimal 229, K2/K3/T 229/229.
  seed 12: 600 n (omega 3-8, p<3000): K1 600/600, minimal 453, K2/K3/T 453/453.
  seed 13: 300 n (omega 8-14, p<1e5): K1 300/300, minimal 249, K2/K3 249/249 (no PARI sum).

## Steps 4-5 (slot-k curves) -- VERIFIED
- slot_tyz.py admissible 30 (run_dl.gen_random seed 2026, first multiplier): 60 curves, all |d| = 5 mod 8,
  dim Sel_2 = 3, beta in pi_1, chi_{-1}(|beta|) = 1, det M_5b = 1.  0 failures.  (out_slot_admissible.txt)
- slot_tyz.py small 30 7 (least-prime realizations, T nonempty): 60 curves, 55 with omega <= 8 where the
  TYZ tau(1/2) bracket was computed with PARI class groups: all = 1.  0 failures. (out_slot_small.txt)

## Facts fixed for the note
- TYZ numbering (arXiv v1, thm counter per section, remarks share it): Thm 1.1 (lg), Thm 1.2 (lg'),
  Cor 1.4, Thm 3.3 (GZ formula, from YZZ), Prop 3.4 (congruence), Thm 3.5 (m3), Lemma 3.18 (torsion2:
  A(H'_n)_tors in A[4]), Lemma 3.21 (betaaction); proof of 3.5(2) = last subsubsection of Section 3.3.
- tau(1/2), tau((1-i)/2) independent mod Z tau(1): checked by hand (a u(1-i)/2 + b/2 in Z[i] => a,b even).
- Fubini numbers odd => the d0 = 5 bracket of Prop 3.4 is 5a with set-partition L (side remark only).
- Genus theory derivation of Table 1 rows 1, 3 written out (principal genus via Hilbert 90 + Hasse norm;
  kernel {1, n} of ambiguous ideals for n > 1; Hilbert symbols).
- Manuscript lem:forward-rank at line 1086 (A020) gives rank one from analytic rank one.

## Note status
- docs/research/tyz-5b.md written (sections: verdict, notation, 1 TYZ, 2 forests + Redei, 3 row 5b,
  4 rule, 5 slot curves, 6 validation, 7 remains, scripts). analytic_check.py: 12 small slot curves,
  analytic rank 1 and point with x in beta Q^2 on all.
- Independent referee (subagent) checking sections 2-4; pending. Then .fleet/tyz-5b.md.

## Done
- Referee remarks incorporated; .fleet/tyz-5b.md written.
