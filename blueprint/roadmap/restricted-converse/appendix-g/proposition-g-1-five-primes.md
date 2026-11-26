---
article_id: af_d6e80d8f8fecb84fa0b32f92
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.GlueSweep.Ana.fivePrime_four_of_prints, ZInQ.Manuscript.RC.Nonvanishing.fivePrime_four, ZInQ.Manuscript.RC.GlueSweep.Ana.fivePrime_of_mem_integral
---

# Proposition G.1: nonvanishing with at most five primes

Assume the theorem of Hoffstein and Luo over newforms (the field `RCLeaves.hlPrint` of [the remaining
hypotheses](../remaining-hypotheses.md), PRINT) and modularity in newform form (`ModularNewform`, which
follows from [the cited results](../printed-results.md) and fields of the remaining hypotheses,
`RCLeaves.modularNewform`). The twisted functional equation and the absolute convergence of $L(A,s)$
on $\operatorname{Re}s>3/2$, also hypotheses of `fivePrime_four_of_prints`, are proved. The form
`fivePrime_four` takes instead three consequences of these as hypotheses: Hoffstein–Luo for elliptic
curves with at most four primes, the twist sign of Bump–Friedberg–Hoffstein, and Theorem A of
Breuil–Conrad–Diamond–Taylor.

Let $A/\mathbb Q$ be an elliptic curve, $S$ a finite set of primes containing $2$ and every prime of bad
reduction, $B$ a finite set of primes, and $\Phi$ a signed unit filter at $S$, as on the page of
[Proposition 7.3](../section-7/proposition-7-3-nonvanishing.md). If $w(A^{(u)})=+1$ for every squarefree
$u\in\Phi$, then there is an odd squarefree $u\in\Phi$, prime to $B$, with
$$\omega(u)\le5,\qquad L(A^{(u)},1)\ne0.$$

The manuscript speaks of the root number of the filter and puts $3$ in $S$; the Lean statement asks for
root number $+1$ at every squarefree parameter of the filter and does not need $3\in S$. With the root
number read off one squarefree parameter, as the manuscript states it, the proposition is
`fivePrime_of_mem_integral`, for a model over $\mathbb Z$ whose discriminant primes lie in $S\ni3$; it
also assumes Desjardins' root-number theorem for signed unit filters, a composite printed result with a
GLUE reading (`DesjardinsRootNumberFilter`), outside the reduction of Theorem 5.3. As in the manuscript,
$u$ need not be a fundamental discriminant and nothing is claimed about the size of its primes.

In the reduction of Theorem 5.3 the proposition is used as `fivePrime_four`, with its three inputs
obtained from `RCLeaves.hl`, `RCLeaves.twistSign` and `Prints.bcdt`, in two places. The proof of
[Proposition 7.14](../section-7/proposition-7-14-rough-companion.md) applies it to the curve $E^{(ha)}$.
Through the even case of [Proposition 7.3](../section-7/proposition-7-3-nonvanishing.md)
(`nonvanishing_even`), it is applied to $E_\ell$ for the genus partner (`exists_genusPartner`, in
`branchPackageNode_of_leaves`).

**Proof sketch.** By CRT and Dirichlet's theorem choose a signed prime $q_0$ in the classes of $\Phi$,
outside $S\cup B$. Apply Hoffstein–Luo to $A^{(q_0)}$, which has root number $+1$, with splitting set
$S\cup B\cup\{|q_0|\}$; this set contains the bad primes of $A^{(q_0)}$. It gives a fundamental
discriminant $d$ with at most four prime factors, split at that set, with $L(A^{(q_0d)},1)\ne0$. The
twist sign forces $d>0$ and splitting at $2$ gives $d\equiv1\pmod8$, so $q_0d$ lies in $\Phi$, is odd,
squarefree and prime to $B$, and has at most five prime factors.

## Depends on

- [The cited results](../printed-results.md)
- [The remaining hypotheses](../remaining-hypotheses.md)

## Sources

- [Appendix G](../../../sources/manuscript.md#appendix-g)
