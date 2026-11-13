---
article_id: af_d6fbe52fe8977c7a3dd3a943
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.GreenTaoDense.exists_reducedResidue_setWeight_mean_lower_bound, ZInQ.GreenTaoDense.quarterIntervalSetClass, ZInQ.GreenTaoDense.wTrickedSetWeight_untrickPrimeZMod, ZInQ.GreenTaoDense.setClass_log_mass_div_card_le_mean, ZInQ.GreenTaoDense.card_mul_log_cutoff_le_setClass_log_mass
---

# The residue pigeonhole for a set of primes

Let $A$ be a set of natural numbers, $w$ and $N\ge1$ natural numbers, $\alpha\ge0$, $W=\prod_{p\le w}p$
and $X=W\lfloor N/8\rfloor$, and suppose $w\le\lfloor X/4\rfloor$. Let $S$ be the set of primes
$p\in A$ with $\lfloor X/4\rfloor<p\le X$. Then there is a residue $0\le b<W$ coprime to $W$ such
that the mean of the W-tricked weight of $A$ over $\mathbb Z/N$ satisfies
$$\frac1N\sum_{n\in\mathbb Z/N}\lambda^A_{\alpha,W,b}(n)\ \ge\
\frac{\alpha}{W}\cdot\frac{\#S\cdot\log(\lfloor X/4\rfloor+1)}{N}.$$

**Proof sketch.** Every $p\in S$ exceeds $w$, so it is coprime to $W$; pigeonholing $S$ over the
$\varphi(W)$ reduced classes gives a class $b$ with $\#S\le\varphi(W)\,\#S_b$, where $S_b$ is the set
of $p\in S$ with $p\equiv b\pmod W$. Each $p\in S_b$ is $W\bar n+b$ for the residue $n$ of $(p-b)/W$,
which lies in $[\lfloor N/64\rfloor,\lfloor N/4\rfloor]$, and these $n$ are distinct; at each,
$\lambda^A(n)=\alpha\frac{\varphi(W)}W\log p\ge\alpha\frac{\varphi(W)}W\log(\lfloor X/4\rfloor+1)$.
Summing over $S_b$ and dividing by $N$ gives the bound. This is the vendored density selection with
the primes of $(\lfloor X/4\rfloor,X]$ replaced by the elements of $A$ among them; the original
pigeonhole is already stated for an arbitrary finite set of primes above $w$.

## Depends on

- [The W-tricked weight of a set of primes](set-weight.md)

## Sources

- [Where the primes enter](../../sources/green-tao-locators.md#where-the-primes-enter)
- [The Lean statements](../../sources/green-tao-locators.md#the-lean-statements)
