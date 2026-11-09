---
article_id: af_5f88c47c5a405c36b7c8d7cb
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.legBit, ZInQ.RouteK.lamBit, ZInQ.RouteK.muBit, ZInQ.RouteK.signBit, ZInQ.RouteK.primesOf
---

# Residue bits

For a prime $p$ and an integer $a$, the *residue bit* $[a/p]\in\mathbb F_2$ is $0$ if $a$ is a
square modulo $p$ and $1$ otherwise; for $a$ prime to $p$ it is the bit of the Legendre symbol,
$(a/p)=(-1)^{[a/p]}$, and for $p\mid a$ it is $0$ (this value is never used). Put
$\lambda_p=[-1/p]$ and $\mu_p=[2/p]$. For an integer $\beta$ put $s(\beta)=[\beta<0]\in\mathbb F_2$,
and let $P(\beta)$ be the set of primes dividing $\beta$.

## Depends on

None.

## Sources

- [Configurations and the Selmer system](../../sources/route-k-locators.md#configurations-and-the-selmer-system)
