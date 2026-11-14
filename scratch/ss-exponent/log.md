# ss-exponent results log

Target: `SupersingularExponentA` (verbatim from scratch/tyz-318/Lemma318.lean §1, merged origin/wip/tyz-318).

## Compile outcomes
- [VERIFIED, compiled, 2026-11-14 00:10] `scratch/ss-exponent/Abstract.lean`: abstract group lemma
  `nsmul_eq_zero_of_frob`: finite abelian `G`, `π` involution, `i² = −1`, `π i = −i π`, every `π`-fixed subgroup
  has order dividing `N = 2^v m` (`m` odd) ⟹ `N • G = 0`. No sorry. (Proof: weak exponent `2N` as in tyz-318;
  `#G[2^{v+1}] ≤ #(fixed part)·#(anti-fixed part) ≤ 2^v·2^v`; the chain `ker (1+i)^n` strictly increases until it
  stabilizes, `(1+i)² = 2i`, so `(1+i)^{2v} = 2^v i^v` kills `G[2^{v+1}]`.)
