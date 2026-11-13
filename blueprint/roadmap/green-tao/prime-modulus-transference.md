---
article_id: af_4f96ed92281a909e3bd89a9c
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.GreenTaoDense.hasPrimeModulusSubweightCounts, ZInQ.GreenTaoDense.HasPrimeModulusSubweightCounts, ZInQ.GreenTaoDense.hasPrimeModulusSubweightCounts_of_orderedRemoval_of_linearForms
---

# Transference for every large prime modulus

For $k\ge3$ let $\alpha_k>0$ be the scale of the W-tricked prime weight in the Green–Tao proof (the
constant fixed there from $k$ and the normalizer of the smooth sieve cutoff, small enough that the
weight lies below the sieve majorant). For $f:\mathbb Z/N\to\mathbb R$ write
$\mathbb E f=\frac1N\sum_nf(n)$ and
$\Lambda_k(f)=\mathbb E_{a,d\in\mathbb Z/N}\prod_{j<k}f(a+jd)$.

For every $k\ge3$ and every $\delta>0$ there are a natural number $w$ and a real $c>0$ such that,
with $W=\prod_{p\le w}p$, for every sufficiently large $M$ with $N=M+1$ prime, every residue
$0\le b<W$ coprime to $W$ and every $f:\mathbb Z/N\to\mathbb R$ with
$$0\le f\le\lambda_{\alpha_k,W,b}\qquad\text{and}\qquad\mathbb Ef\ge\delta,$$
the count satisfies $\Lambda_k(f)\ge c$.

The Green–Tao proof for the set of all primes shows this only for the prime weight itself, at one
prime modulus beyond each bound, and for one fixed density. The proof never uses more: the change
is in the quantifiers.

**Proof sketch.** Write $k=r+2$. The dense Szemerédi theorem, from the ordered hypergraph removal of
the vendored proof, gives for density $\delta/2$ a count $\Lambda_k(g)\ge c_0>0$ for every
$g:\mathbb Z/N\to[0,1]$ with $\mathbb Eg\ge\delta/2$, uniformly in $N$. The parameter package of the
relative counting step, chosen for the reserves $\delta/2$ and $c_0/2$, and the linear forms
condition of the Selberg-sieve majorant $\nu_b$, uniform over the reduced classes $b$, fix $w$ and
a threshold. For $N=M+1$ prime and large, $N$ is coprime to $(r+1)!$, the prime weight lies below
$\nu_b$ for every $b<W$ at once, and so does every $f\le\lambda$. The relative Szemerédi theorem,
which holds for every $0\le f\le\nu$, then gives $\Lambda_k(f)\ge c_0-c_0/2=c$. The deep inputs, the
hypergraph removal lemma and the linear forms estimate for the majorant, are those of the vendored
proof, used unchanged.

## Depends on

- [The W-tricked weight of a set of primes](set-weight.md)

## Sources

- [Where the primes enter](../../sources/green-tao-locators.md#where-the-primes-enter)
- [The Lean statements](../../sources/green-tao-locators.md#the-lean-statements)
