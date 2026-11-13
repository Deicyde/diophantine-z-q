# rv-qm-polar results log

Marks: VERIFIED (read/computed/compiled), STANDARD (published, reference), SPECULATIVE.
Theorem numbers from memory: UNVERIFIED (no network).

## Step 1. Exact computations (`polar_checks.py`, ~/pyenv/bin/python; all VERIFIED, exact arithmetic)

Setting: B = (2,-3) (i^2=2, j^2=-3, k=ij), O = Z<1, i, (1+j)/2, (i+k)/2>, mu = 2j+k (N5 L410-420).
- mu^2 = -6.
- Twisting elements (Rotger's sense): chi2 = i (i^2 = 2), chi3 = j+k ((j+k)^2 = 3), both in O, both
  anticommute with mu; i(j+k) = mu. Ad(i), Ad(j+k), Ad(mu) commute with dag_mu(x) = mu^-1 xbar mu
  on the basis of O. So the Atkin-Lehner group W (classes of i, j+k, mu in N_B(O)/Q^* O^*)
  preserves the Rosati type mu.
- Elements of B anticommuting with mu: a*i + b*(j+k), reduced norm -2a^2-3b^2 < 0 (never +-1 over Q
  unless a=b=0... norm -1 would need 2a^2+3b^2 = 1, impossible: (2,3) local obstruction; recorded
  only as the computed formula).
- Other types: 12 pure mu' in O with mu'^2 = -6 and coordinates in [-6,6]; for each, the form
  E_mu'(x,y) = trd(mu'^-1 x ybar) has integral Gram matrix of determinant 1 on N5's basis.
  Example mu' = 2j - k: Gram [[0,0,-1,-1],[0,0,-1,-2],[1,1,0,0],[1,2,0,0]] (not a multiple of
  N5's Gram [[0,0,-1,1],[0,0,1,-2],[1,-1,0,0],[-1,2,0,0]]); dag_mu'((1+j)/2) differs from
  dag_mu((1+j)/2) (k-coordinate +1 versus -1).
- mu' = 2j-k = -v' mu v'^-1 with v' = -1+i in O, nrd v' = -1 (so type mu' is the transport of
  type mu by the automorphism iota(v')).
- All 12 small mu' are conjugate to +-mu by a unit of O with coordinates in [-4,4] (466 units).
  Evidence (not proof) that O^* acts transitively on {mu' in O : mu'^2 = -6}/+-1.
- mu^-1 (u mu u^-1) lies in O with reduced norm 1 for all 126 units u of O with coordinates in
  [-2,2] (the PEL twist by an inner automorphism transports lambda by an element of O^1).
