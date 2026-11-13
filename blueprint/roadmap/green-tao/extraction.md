---
article_id: af_2349c61e3b7a030b02446f3b
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.GreenTaoDense.containsAP_of_wTrickedSetWeight_offDiagMass_pos
---

# Extraction of a progression in the set

Let $A$ be a set of natural numbers, $k\ge2$, $N\ge1$, $\alpha>0$, $W>0$ and $b$ natural. If the
off-diagonal mass of the weight of $A$ is positive,
$$\sum_{a\in\mathbb Z/N}\ \sum_{d\in\mathbb Z/N,\ d\ne0}\ \prod_{j<k}\lambda^A_{\alpha,W,b}(a+jd)>0,$$
then $A$ contains a $k$-term arithmetic progression: there are natural numbers $a'$ and $d'>0$ with
$a'+jd'\in A$ for every $j<k$.

**Proof sketch.** Some $a$ and $d\ne0$ have $\lambda^A(a+jd)>0$ for every $j<k$. By the
positivity criterion of the weight, every representative $\overline{a+jd}$ lies in
$[\lfloor N/64\rfloor,\lfloor N/4\rfloor]$, an interval of less than half the length of $\mathbb Z/N$,
and $W\overline{a+jd}+b\in A$. The short-interval lift of the vendored proof turns a cyclic
progression inside such an interval into an integer progression with positive difference in
$\{n:Wn+b\in A\}$, and the affine map $n\mapsto Wn+b$ carries it into $A$. This is the vendored
extraction for the primes, with the positivity criterion of the weight of $A$ in place of that of
the prime weight.

## Depends on

- [The W-tricked weight of a set of primes](set-weight.md)

## Sources

- [Where the primes enter](../../sources/green-tao-locators.md#where-the-primes-enter)
- [The Lean statements](../../sources/green-tao-locators.md#the-lean-statements)
