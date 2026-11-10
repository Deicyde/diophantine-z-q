---
article_id: af_f41c88693d5caf730a097f9a
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Density.sum_inv_sq_le_of_primes_gt, ZInQ.Density.prime_tail, ZInQ.Density.sum_log_div_sq_le
---

# The prime tail $\sum_{\ell>L}\ell^{-2}$

For $L\ge2$ and every finite set $F$ of primes greater than $L$,
$$\sum_{\ell\in F}\frac1{\ell^2}\le\frac{3\log4}{L\log L};$$
in particular $\sum_{L<\ell\le M}\ell^{-2}\le4\log4/(L\log L)$ for every $M$, the form of the research note.

**Proof sketch.** $\ell^{-2}\le(\log\ell/\log L)\,\ell^{-2}$ for $\ell>L$; Abel summation of
$\sum(\log\ell)\ell^{-2}$ against Chebyshev's bound $\theta(m)\le m\log4$ gives the bound (the note uses a
dyadic decomposition instead and gets the constant $4\log 4$).

## Depends on

None.

## Sources

- [Assembly](../../sources/density-locators.md#assembly)
