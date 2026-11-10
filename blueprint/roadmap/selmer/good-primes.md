---
article_id: af_50b4fc418dbd73ea73a890cf
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Selmer.loc_padic_good_iff, ZInQ.RouteK.Selmer.loc_padic_good_even, ZInQ.RouteK.Selmer.loc_padic_good_of_units
---

# Local solubility at odd primes not dividing d

Let $p$ be an odd prime, $d$ a natural number with $p\nmid d$, and $a,b$ integers.

1. *(Lemma G1)* If $a,b\ne0$ and $D_{a,b}$ is soluble over $\mathbb Q_p$, then $v_p(a)$ and
   $v_p(b)$ are even.
2. *(Lemma G2)* If $p\nmid a$ and $p\nmid b$, then $D_{a,b}$ is soluble over $\mathbb Q_p$.
3. Consequently, for squarefree $a$ and $b$, $D_{a,b}$ is soluble over $\mathbb Q_p$ if and only if
   $p\nmid a$ and $p\nmid b$.

(Solubility is meant in the x-form.)

**Proof sketch.** (1) The first alternative and the torsion witnesses give unit classes. Otherwise
$x\equiv a$, $x-d\equiv b$, $x+d\equiv ab$; compare $|x|$ with $|d|=1$: for $|x|>1$ all three have
valuation $v(x)$, for $|x|<1$ both $x\mp d$ are units, and for $|x|=1$ at most one of $x\mp d$ is a
non-unit since their difference $2d$ is a unit; in each case $v(a)$ and $v(b)$ are even. (2) Take
the residue witness $\xi$ over $\mathbb F_p$ for the residues of $d,a,b$; lift it to an integer
$x$, taken to be exactly $0$, $d$ or $-d$ when $\xi\in\{0,\pm\bar d\}$; the nonzero quotients are
units with square residues, hence squares in $\mathbb Q_p$. If $\bar a,\bar b$ are squares, so are
$a,b$. (3) A squarefree integer with even $v_p$ is prime to $p$.

## Depends on

- [The 2-coverings of a congruent number curve](coverings.md)

## Proof depends on

- [Squares in the p-adic numbers](padic-squares.md)
- [Square classes and torsion witnesses of a covering](covering-classes.md)
- [A residue witness for the coverings over a finite field](character-sums.md)

## Sources

- [Odd primes not dividing d](../../sources/selmer-locators.md#odd-primes-not-dividing-d)
