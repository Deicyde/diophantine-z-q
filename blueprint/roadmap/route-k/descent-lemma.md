---
article_id: af_4ec5236a017c57ca93ab8bd6
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.descent_lemma, ZInQ.RouteK.inputs_of_admissible
---

# The descent lemma

For every admissible $B$ there are a signed divisor $m$ of $2730$ and an integer $n$ such that,
with $\beta=\mathrm{sqf}(mB)$ and $\theta=\mathrm{sqf}(m(m-B))$:

- $\beta\mid n$, $|n|\equiv5\pmod8$ and $|\beta|\equiv7\pmod8$;
- $n$ and $n\theta$ are squarefree, and $|n\theta|\equiv5\pmod8$;
- $(|n|,\beta)$ and $(|n\theta|,\beta)$ carry Selmer certificates: the systems
  $\Sigma(\mathcal C_{|n|})$ and $\Sigma(\mathcal C_{|n\theta|})$ have exactly $8$ solutions each,
  and each has a solution with first coordinate the class of $\beta$.

Through Proposition 0 this says that $C_n$ and $C_{n\theta}$ have 2-Selmer groups of dimension
$3$ in which $\beta$ is a first Kummer coordinate. The construction uses
$\omega(\beta)+\omega(\theta)$ auxiliary primes.

Along the way: for admissible $B$, a signed divisor $m$ of $2730$ with $\beta$ odd and
$|\beta|\equiv7\pmod8$, and a prime $p_0$ dividing $\beta$, the triple $\beta,\theta,p_0$ satisfies
the hypotheses of the realization: $\beta$ is squarefree, $\theta>0$ is squarefree with
$\theta\equiv1\pmod8$, $\beta$ and $\theta$ are coprime, $[\beta/\ell]=0$ for every prime
$\ell\mid\theta$, and $[\theta/p]=0$ for every prime $p\mid\beta$.

**Proof sketch.** By the multiplier lemma choose $m$ with $\beta$ odd and $|\beta|\equiv7\pmod8$;
then $P(\beta)\ne\emptyset$, and by (θ1)–(θ4) the pair $\beta,\theta$ satisfies the hypotheses of
the realization (with $\beta$, $\theta$ squarefree as squarefree parts of nonzero rationals, and
(θ3), (θ4) in residue bits). Fix $p_0\in P(\beta)$, choose the slots and take $n=d_1$. Then
$|n\theta|=d_1\theta=d_2$, and the realization gives every assertion; $d_2\equiv5\cdot1\pmod8$.

## Depends on

- [Admissible inputs, the squarefree part, $\beta$ and $\theta$](squarefree-part.md)
- [The configuration of an odd number and Selmer certificates](prime-configuration.md)
- [Residue bits](residue-bits.md)

## Proof depends on

- [The multiplier lemma](multiplier-lemma.md)
- [The properties (θ1)–(θ4)](theta-properties.md)
- [The slots exist](slots.md)
- [The realization: both curves reduce to the base configuration](realization.md)

## Sources

- [Certificates and the descent lemma](../../sources/route-k-locators.md#certificates-and-the-descent-lemma)
- [Proof of the descent lemma](../../sources/route-k-locators.md#proof-of-the-descent-lemma)
