---
article_id: af_38505fe6b85fcc899768546f
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.GreenTaoDense.containsAP_of_frequently_window
---

# Progressions in a set of primes with mass in dyadic windows

Let $A$ be a set of primes and $c_1>0$ such that
$\#(A\cap(\lfloor Z/2\rfloor,Z])\ge c_1Z/\log Z$ for infinitely many $Z$. Then for every $k$ the set
$A$ contains a $k$-term arithmetic progression: there are natural numbers $a$ and $d>0$ with
$a+jd\in A$ for every $j<k$.

**Proof sketch.** For $k\le2$ truncate a progression of length $3$; so let $k\ge3$ and
$\alpha=\alpha_k$. Put $c_2=c_1/6$ and $\delta=\alpha c_2/32$, fixed before $w$. Transference for
every large prime modulus gives $w$, $c>0$ and a threshold; put $W=\prod_{p\le w}p$. The modulus
selection gives a prime $q=M+1$ beyond the transference threshold, the threshold of the height bound
$(2\alpha\log q)^k<qc$ and $2W+4w+16$, such that $A$ has at least $c_2X/\log X$ elements in
$(\lfloor X/4\rfloor,X]$, $X=W\lfloor q/8\rfloor$; these are primes, so they form the set $S$ of the
residue pigeonhole. The pigeonhole gives a reduced class $b$ with
$\mathbb E\lambda^A\ge\frac\alpha W\#S\log(\lfloor X/4\rfloor+1)/q$, and the vendored Chebyshev
arithmetic, with the constant $\log2/4$ replaced by $c_2$, bounds this below by $\alpha c_2/32=\delta$.
Since $0\le\lambda^A\le\lambda$, transference gives $\Lambda_k(\lambda^A)\ge c$. The weight is at most
$2\alpha\log q$, so the diagonal progressions ($d=0$) carry less than the count, and the off-diagonal
mass is positive. Extraction gives the progression in $A$.

## Depends on

None.

## Proof depends on

- [Choosing the prime modulus](modulus-selection.md)
- [Transference for every large prime modulus](prime-modulus-transference.md)
- [The residue pigeonhole for a set of primes](residue-pigeonhole.md)
- [Extraction of a progression in the set](extraction.md)
- [The W-tricked weight of a set of primes](set-weight.md)

## Sources

- [The proof for a dense set](../../sources/green-tao-locators.md#the-proof-for-a-dense-set)
- [The Lean statements](../../sources/green-tao-locators.md#the-lean-statements)
