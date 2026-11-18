# pc-from-rc results log

## 2026-11-17 setup
- Base 19fdd483. `lake build ZInQKernel.Hypotheses.PoleManuscript` OK (VERIFIED).
- PARI/cypari2 and sympy are NOT installed on this host (~/pyenv missing); numerics use plain python3.
- 2-adic Kummer image of E_l (l = 3 mod 4), classes (x+3l, x-l) in (Q_2^*/Q_2^*2)^2, sampled
  x = a/2^k (|a|<2000, k<8) for l mod 32 in {3,...,31}: exactly the 8 classes {a odd unit, b in {1,5} mod 8}
  (scratch/pc-from-rc/local2.py). VERIFIED (computed, sampling). So every 2-Selmer class has a, b odd and
  b = 1 mod 4: the manuscript's representative shape (no factor 2, L1062) comes from the 2-adic image,
  which the text does not spell out (ELLIOT).

## Lean, first deliverable (core)
- `ZInQKernel/Contrib/PoleRC/Defs.lean`: `LocM`, `SelM`, `CRM`, `SimultaneousConstruction` (defs only). COMPILED.
- `Rescale.lean`: `point_of_locM`, `polePoly_eq_zero_of`, `witnesses_of_points` (L1107-1121). COMPILED.
- `Bookkeeping.lean`: `bookkeeping` (L1020-1032): from B get bits b (m | 2730 positive), beta, theta
  squarefree, beta = 17, theta = 1 mod 24, coprime, mutual local squares (in ZMod p), A = beta s^2,
  H = theta c^2. COMPILED, axioms [propext, Classical.choice, Quot.sound].
  Construction used: B = N/D^2, N = k^2 r, r0 = gcd(r,2730), r1 = r/r0, f | 455 with f r1 = 17 mod 24,
  m = r0 f / gcd(r0,f)^2, beta = f r1, theta = sqfree part of T = D^2 - N/m, H = T (mB/D)^2.
- `Reduction.lean`: `poleCompleteness_of_crm : CRM -> SimultaneousConstruction -> Manuscript.PoleCompleteness`.
  COMPILED, axioms [propext, Classical.choice, Quot.sound].

## Lean, second deliverable (statement level)
- `CRM.lean`: `crm_of_restrictedConverse P (hRC : RestrictedConverse P) (h54 : Lemma54At P)
  (hK : KolyvaginRankOne) (hMW : MordellWeil) (hD : DescentGlueM) : CRM`. COMPILED.

## Numerics (plain python3, scratch/pc-from-rc/{selmer,compare,construct,batch}.py)
- compare.py: for all 55 squarefree l < 700, l = 11 mod 12, the brute-force explicit 2-Selmer set
  (local searches at p | 6l and R; good primes assumed unramified) EQUALS the set predicted by the local
  image formulas: R: a > 0; Q_2: a, b odd, b = 1 mod 4; Q_3: 3 does not divide b, b = 1 mod 3;
  q | l: (a,b) in span of torsion classes (l,1), (3,-l) mod Q_q^*2. 0 mismatches. VERIFIED (computed).
- selmer.py: l = 323 = 17*19: matrix conditions (ker K = <1,1_beta>, lambda not in im K) hold for
  beta = 17, and brute-force #Sel = 8 with (17,1) in Sel. VERIFIED (computed).
- batch.py: for 30 random beta (1-3 primes < 400, beta = 17 mod 24), theta = 1 (the random theta
  generator produced no theta > 1 -- weak test for theta), a random search over n = beta*q0*p_1..p_{d-1}
  (q0 = 7 mod 12, p_k = 1 mod 12, the slot types of L1042) found n with the matrix conditions for n
  in all 30 cases (within <= 308 tries); for n = 5627 = 17*331 brute force gives #Sel = 8, (17,1) in Sel.
  construct.py: (beta, theta) = (65, 97*193) also succeeded (n = 308487335).
- batch2.py: 30 random (beta, theta) with theta > 1 (1-3 primes, theta = 1 mod 24, mutual local squares):
  slot-shape search found n with the matrix conditions for BOTH n and n*theta in 30/30 cases
  (<= 697 tries each). VERIFIED (computed). Evidence that MatrixRealization is true; not a proof.

## Lean: the dimension-three linear algebra
- `LinAlg.lean`: `dimThree_linear_algebra` (abstract F_2: K^T = K + ss^T + diag s, K1 = 0, s.1 = 1,
  lam.1 = 0, ker K in {0,1,b,1+b}, lam not in im K; local equations E1-E4 with sign sigma
  => v = sigma*1, delta = sigma, K u = 0). Uses duality (Submodule.exists_dual_map_eq_bot_of_notMem)
  and rank K^T = rank K. COMPILED, standard axioms.
- `Recip.lean`: for the genuine K (`Kmat`): `kmat_transpose` (quadratic reciprocity),
  `kmat_mulVec_one`, `sgn_dot_one` (l = 3 mod 4), `lam_dot_one` (l = 11 mod 12), and
  `kmat_forces : MatrixConditions l beta -> E1..E4 -> v = sigma*1, delta = sigma, K u = 0`.
  COMPILED, standard axioms. This is the manuscript's line-1068 claim, with the reciprocity identities
  and the 2-adic equation it leaves implicit (ELLIOT), and both signs of b.
- #discharges (scratch/pc-from-rc/discharges-output.txt): 34 open hypotheses, 12080 theorems checked;
  no PoleRC theorem discharges an open hypothesis (Manuscript.PoleCompleteness is not a bundle field). VERIFIED.

## Lean: the dimension-three count from the local images
- `QClass.lean`: `qcls q x` (square class at odd q of a squarefree integer), `lsym_mul`, `qcls_mul`,
  `qcls_eq_sum`. COMPILED.
- `Count.lean`: five local-image Props (`LocalReal`, `LocalTwo`, `LocalThree`, `LocalBad`, `LocalGood`);
  `localReal : LocalReal` PROVED; `dimThreeCount_of_local : LocalTwo -> LocalThree -> LocalBad ->
  LocalGood -> DimThreeCount` PROVED (standard axioms). Steps: necessity (local conditions -> E1..E4 ->
  kmat_forces), injectivity of (a,b) -> (ind a, sign b) on SelM, the 8 candidates (3^s c, (-l)^s),
  c in {1, l, beta, l/beta}, are in SelM (sufficiency), image = {0,1,1_beta,1+1_beta} x F_2.
- `Contrib/OneProof/PoleCompletenessFromRC.lean`: `poleCompleteness_of_restrictedConverse_local`
  (DimThreeCount replaced by the four local Props). COMPILED, axioms [propext, Classical.choice, Quot.sound].

## Lean: the complete 2-descent of E_l (DescentGlueM proved)
- `KummerM.lean`: Kummer map `kum l e` at a root e of x^3+2lx^2-3l^2x is a homomorphism (`kum_add`;
  chord identity from Mathlib's `addPolynomial_slope` at X = e). COMPILED.
- `DescentM.lean`: `deltaM` (coords (x+3l, x-l)), halving lemma `exists_two_nsmul_eq_M`
  (x' = x + r1r2 + r1r3 + r2r3, slope r1+r2+r3; identities by hand, no CAS), `deltaM_eq_one_iff`
  (l > 0 not a square), `selRepM_mem_selM`, `card_ker_two_nsmul_eq_four_M`, and
  `descentGlueM : DescentGlueM` PROVED (standard axioms). DescentGlueM now carries l = 11 mod 12
  (needed so that l is not a square; CRM supplies it).
- `poleCompleteness_of_restrictedConverse_final (P) : RestrictedConverse P -> Lemma54At P ->
  KolyvaginRankOne -> MordellWeil -> MatrixRealization -> LocalTwo -> LocalThree -> LocalBad ->
  LocalGood -> Manuscript.PoleCompleteness`. COMPILED, axioms [propext, Classical.choice, Quot.sound].
- localprops.py (per-prop brute-force check, 12 l) did not finish within 3500 s: NOT RUN to completion.
  (The combined check compare.py, 55 l, did pass.)
