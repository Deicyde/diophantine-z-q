# rv-nocm results log

## Computations
- `nocm_check.py` (pure Python 3, no PARI: `~/pyenv` and cypari2 are absent on this host and no
  network install was attempted), output `nocm_check.output.txt`. VERIFIED (computed):
  - Part A: on the 24 non-elliptic rows of Elkies' Table 1 (rational points of X*), (Emb) holds,
    `2^b h(R) = 4` = fibre size in every row; the unqualified `#CM(R) = h(R)` contradicts the
    4-point fibre in 15 of 24 rows (all rows with b >= 1, e.g. |D| = 19: h = 1, 4 points).
    The 9 rows with b = 0 are exactly the rows where `#CM = h` holds.
    Elliptic: |D| = 4, 3: h = 1, b = 1, 2 points each; |D| = 24: h = 2, b = 0, 2 points.
  - Part B: fibre fields on X6 agree with GR Thm 5.12 (degree 2h with K inside if b >= 1;
    degree h, K not inside, if b = 0) in all 24 rows; [K.Q(x):K] = h; unramified-outside-f
    consistency check passes.
  - Part C: D = -24: on X* the point t = 0 (j = -16/27) is rational, [H_R:Q(j)] = 4; on X6 the
    points over t = 0 have Q(x) = Q(sqrt -3), index 2 in H_R = Q(sqrt -6, sqrt 2).
  - Part D: X6 -> P^1_t has index 2 at t = 0, 1, inf. |(O/3O)^*| = 72, nrd-kernel mod 3 = 36,
    [Gamma*:Gamma_3] = 72 (x 2 components = 144 = h-b1 M3). Riemann-Hurwitz for a component
    of Y3 over P^1_j: indices (4,6,2) give g = 4; indices (2,2,2) give g = -17 (impossible).
    Of the 6 assignments of {4,6,2} to (0, inf, -16/27), only (4,6,2) makes "p not | M_S(u)
    => unramified" hold.
