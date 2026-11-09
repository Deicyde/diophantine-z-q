# nt-h log

## Step 0 (start)
- No earlier log: fresh run. Read KERNEL_PLAN.md, rs-height.md (all), h-cm.md (summary),
  rv-h-cm.md (verdict), h-leaves.md (§§1, 2.2, 4.5, 5), rs-global.md (C1-C7, A3-A10),
  HeightMin.lean, manuscript 52-140, 540-580, 630-860, 966-1060, 1123-1265.
- Plan: (Q1) consumer analysis + slack; (Q2) structural obstruction for cusps / affine moduli;
  (Q3) Serre-pigeonhole variant of the modularity step (KW strong form at large l) replacing
  Pan + p-adic Hodge theory + Carayol.
- Ideas so far:
  * Q2: "moduli affinity" lemma: parity mechanism => family over complete curve C (genus 17)
    with potentially good reduction => coarse moduli must contain complete curves; all
    Baker/S-unit effective Shafarevich targets (M_{1,1}, M_{0,n}, H_g, M_2) are affine.
  * Q2: cusp lemma: at a cusp, Tate parameter valuation = width * v_p(u-alpha), bad reduction
    for every positive valuation, parity cannot see it; approach primes infinite (Chebotarev).
  * Q1: rank-0 elliptic quotient route is vacuous on twists having a nontrivial point (image
    point is non-torsion) - to verify numerically on the 131 points of rs-height §3.3.

## Step 1 (computation: elliptic quotients)
- scratch/nt-h/quotients.py (output quotients.output.txt): for all 131 points u with M_S(u)=1,
  S = primes <= 13, |a|,b <= 1500, the image of u in each of the 15 elliptic quotients
  E_I^{(d(u))} is NON-torsion (131/131 points, 15/15 quotients). So every twist that carries a
  nontrivial point has all 15 elliptic quotients of positive rank: a "rank-zero quotient" route
  is vacuous exactly on the twists that matter. VERIFIED.
- Lean consumers re-read: ratHeight_le_bound_of_test (MainBranch.lean:27), eq_of_close_of_test
  (:42), slope_height_le_of (ContactSupport.lean:49, uses the estimate only at the slope t),
  sixContact_at_Smul (ConstantsProperties.lean:135), sixContact_at_heightPrimes (HeightMin.lean:76).

## Step 2 (note §§0-2 written, commit c71aafc)
- docs/research/nt-h.md: summary, §1 consumers + slack (slack.py), §2 thin sets / rank-zero.
- Run interrupted after this; resumed (Step 3): remaining §3 (cusp, affine-moduli, detection
  lemmas), §4 (Serre large-l argument), §5 ranking, .fleet/nt-h.md.

## Step 3 (computation: genus-2 curve model degenerates at all contact primes)
- scratch/nt-h/genus2cusp.py (+ .output.txt): with the Igusa point of line 538,
  J2^5/J10 = 12^5 (j+1)^5 / j^3, and v_p(J2^5/J10) < 0 for v_p(u-c) = 1 AND = 2 (even!) at
  p in {331,...,353}, and for u p-adically near a root of G (p = 1 mod 3). 19 inputs, all
  non-integral. By Liu's criterion the genus-2 curve C_{J(u)} has bad (non-potentially-good)
  reduction at every prime with a positive contact valuation, whatever the parity; only the
  Jacobian is good. VERIFIED (algebra + computation); Liu's criterion STANDARD, number UNCHECKED.
- Consequence for Q2: the Baker-accessible genus-2 Shafarevich (Smart 1997; von Kanel 2014)
  would need all positive-valuation primes in the conductor = C1. The contact set is exactly the
  preimage of the decomposable locus (J10 = j^3 = 0 <=> F(u) = 0).
- Q3 plan for §4: Serre's pigeonhole at large l: KW strong form (level N(rbar), weight 2 from
  finite flatness at l outside T), pigeonhole over newforms of level <= QM^2. Removes Pan,
  A009/A010, Conrad's local algebraicity; Carayol moves inside the citation of the strong form.
