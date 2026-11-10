---
article_id: af_2dc0f828534b9cfa7c8927b7
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Density.deltaL_ge, ZInQ.Density.QL, ZInQ.Density.modSet, ZInQ.Density.ML, ZInQ.Density.ML_eq, ZInQ.Density.crt, ZInQ.Density.cond, ZInQ.Density.AL, ZInQ.Density.card_AL, ZInQ.Density.totient_ML, ZInQ.Density.deltaL, ZInQ.Density.deltaL_eq, ZInQ.Density.isUnit_of_mem_AL, ZInQ.Density.CL, ZInQ.Density.mem_CL
---

# The residue set $A_L$ and the primes $C_L$

For $L\ge1$ let $Q_L$ be the set of primes $\ell$ with $5\le\ell\le L$ and $\ell\equiv1\pmod4$, and
$M_L=56\prod_{\ell\in Q_L}\ell$. Let $A_L\subseteq\mathbb Z/M_L$ be the set of residues $a$ with
$a\equiv1\pmod8$, $a\bmod7\in\{3,5,6\}$ and $a\not\equiv0,-1\pmod\ell$ for every $\ell\in Q_L$, and
$C_L$ the set of primes $p$ with $p\bmod M_L\in A_L$. Then every element of $A_L$ is a unit,
$$\#A_L=3\prod_{\ell\in Q_L}(\ell-2),\qquad\varphi(M_L)=24\prod_{\ell\in Q_L}(\ell-1),\qquad
\delta_L:=\frac{\#A_L}{\varphi(M_L)}=\frac18\prod_{\ell\in Q_L}\frac{\ell-2}{\ell-1},$$
and $\delta_L\ge3/(8(L-1))$ for $L\ge4$. Every prime $p\in C_L$ is in the class
($p\equiv1\pmod8$, $(p/7)=-1$) and satisfies $\ell\nmid p+1$ for every $\ell\in Q_L$.

**Proof sketch.** The moduli $8$, $7$ and the $\ell\in Q_L$ are pairwise coprime, so by the Chinese
remainder theorem $\mathbb Z/M_L$ is the product of the $\mathbb Z/i$, and $A_L$ is the product of the
sets of allowed components, of sizes $1$, $3$ and $\ell-2$; every allowed component is a unit. The
totient is multiplicative. For the lower bound, every factor
$(n-2)/(n-1)$ with $5\le n\le L$ lies in $[0,1]$, so the product over $Q_L$ is at least the product
over all $n\in[5,L]$, which telescopes to $3/(L-1)$.

## Depends on

- [The description of the good slope primes](description.md)

## Sources

- [The residue set](../../sources/density-locators.md#the-residue-set)
