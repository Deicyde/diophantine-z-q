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
