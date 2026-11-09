---
article_id: af_0853f76d0eed4943f87807b2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.admissible_cutoff, ZInQ.Size.D_le_T
---

# The cutoff is an admissible bound

Assume the catalogue bound, and let the program literal satisfy $|c_3|<2^{2^{24}}$ (as it
does, by the size of the program literal). Then $B=T+1$ satisfies the hypotheses of the
template heights for the constructed library with the constructors of the specification:

1. $B\ge2^{20}$, and the division-polynomial and guard constructors satisfy the uniform
   bounds at $B$;
2. the fixed constant $\ell$ satisfies $1\le\ell\le T$, so $|\ell|+1\le B$;
3. every index $n$ of a division-polynomial constructor of the library has $|n|+1\le T+1$;
4. the guard constructor has cutoff $T$, and $0\le T\le B-1$.

Moreover $D\le T$. The literal constants of the templates need no hypothesis.

**Proof sketch.** By the definitions, $D\le R\le Q\le Q^{17}\le A_{\rm ht}\le T$, and
$D>2^{2^{8008}}$, so $B\ge2^{20}$. (1) The uniform constructor bounds hold at every
$B\ge2^{20}$. For (2), $\ell\ge1$ since $P_s,H_{\rm cat}\ge1$, and
$\ell<2^{2^{4623}}<D\le T$. For (3), by construction every index is $\varepsilon$,
$\varepsilon\pm1$ or $2\varepsilon$ with $\varepsilon\in\{c_*,4,2,3,c_3,1399\}$ (the values of
$\mathrm{integer\_constant}_0,\dots,\mathrm{integer\_constant}_4$ are $4,2,3,c_3,1399$), so
$|n|+1\le2|\varepsilon|+2$. Here $c_*<2^{2^{4617}}$ and $|c_3|<2^{2^{24}}$, so
$|n|+1\le2\cdot2^{2^{4617}}\le2^{2^{4618}}<D\le T$. (4) is immediate. Nothing is evaluated:
each comparison is between symbolic bounds.

The manuscript lists "the absolute values of all literal fixed constants and all occurring
division-polynomial indices are at most $T$" among the checked facts. The indices and the
fixed value $\ell$ (used by the companion proof) are bounded symbolically here. The literal
constants of the templates need no bound, since the majorant rules absorb them at every
$B\ge2^{20}$; for comparison with the manuscript's constant nodes, $2^{69}<T$.

## Depends on

- [The prescribed fixed constants](../../syntax/constants/fixed-constants.md)
- [The catalogue bound](../../main/catalogue-bound.md)
- [Templates satisfy the height majorant](node-majorant.md)

## Proof depends on

- [Closed numerical comparisons](../constants/closed-comparisons.md)
- [Template heights](template-heights.md)
- [The closed form of $T$](../constants/t-identity.md)
- [Bounds for $D$](../constants/d-bounds.md)
- [Size of $N_s$ and $\ell$](../constants/catalogue-size.md)
- [Size of the formal multiple constant](../constants/formal-multiple-size.md)
- [The template library](../../syntax/templates/template-library.md)
- [Shape of the natural precision circuit](../../compiler/natural/universal/circuit-node-counts.md)
- [Node statistics of the halting circuit and the power template](../../compiler/natural/universal/halting-node-check.md)
- [Size of the program literal](../../compiler/natural/universal/wrapper-code-size.md)

## Sources

- [Section 12.1 checked facts](../../../sources/size-locators.md#section-121-checked-facts)
- [Companion size proof](../../../sources/size-locators.md#companion-size-proof)
