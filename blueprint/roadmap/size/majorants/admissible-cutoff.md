---
article_id: af_0853f76d0eed4943f87807b2
declaration: theorem
origin: cited
---

# The cutoff is an admissible bound

Assume the catalogue bound. Then $B=T+1$ satisfies $B\ge2^{20}$ and the four hypotheses of
the template majorant for the constructed library:

1. every node $\mathrm{const}\ c$ has $|c|\le T$;
2. the fixed node has value $\ell$ with $1\le\ell\le T$;
3. every psi node has index $n$ with $|n|+1\le T+1$;
4. the guard node has cutoff $T$, and $0\le T\le B-1$.

**Proof sketch.** By the closed form of $T$, $T=(96\cdot10^{13})^{13}D^{2210G_0^2D^3}\ge D>2^{2^{8008}}$,
so $B\ge2^{20}$ and $2^{69}<T$, which gives (1) by the template-height check. For (2),
$\ell<2^{2^{2063}}<D\le T$. For (3), by the template-height check every index is $\varepsilon$,
$\varepsilon\pm1$ or $2\varepsilon$ with $\varepsilon\in\{c_*,4,2,3,c_3,1399\}$ (the values of
$\mathrm{integer\_constant}_0,\dots,\mathrm{integer\_constant}_4$ are $4,2,3,c_3,1399$), so
$|n|\le2\max(c_*,|c_3|,1399)+1$. Here $c_*<2^{2^{2059}}$, and $0<c_3<2^{2^{24}}$ by the size of
the program literal of the compiler chapter (the Lean literal is built afresh, so the digit
count of the saved literal is not used); both are far below $D/4$. (4) is immediate. Nothing is
evaluated: each comparison is between symbolic bounds.

The manuscript lists "the absolute values of all literal fixed constants and all occurring
division-polynomial indices are at most $T$" among the checked facts; it is a symbolic
consequence of the cutoff estimates, and the bound on the fixed value $\ell$, used by the
companion proof, is included here.

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
