---
article_id: af_e54a738bb73d11278fd67388
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Redei.psi, ZInQ.RouteK.Redei.ambigClass, ZInQ.RouteK.Redei.ambigClass_sq, ZInQ.RouteK.Redei.ambig_pow_val_add, ZInQ.RouteK.Redei.psi_apply, ZInQ.RouteK.Redei.psi_sq
---

# The ambiguous class map $\psi$

Let $n\ge1$ and let $\mathrm{Cl}$ be the class group of the ring of integers $\mathcal O$ of
$\mathbb Q(\sqrt{-n})$. For $p\in T_n$, let $c_p=[\mathfrak p_p]$ if $[\mathfrak p_p]^2=1$, and
$c_p=1$ otherwise; so $c_p^2=1$ in every case. The *ambiguous class map* is
$$\psi:\mathbb F_2^{T_n}\to\mathrm{Cl},\qquad \psi(e)=\prod_{p\in T_n}c_p^{\,e_p},$$
where each exponent $e_p\in\mathbb F_2$ is read as $0$ or $1$. For an element $c$ of a group with
$c^2=1$ and $a,b\in\mathbb F_2$, $c^{a+b}=c^ac^b$; so $\psi$ is a homomorphism from the additive
group $\mathbb F_2^{T_n}$ to $\mathrm{Cl}$, and $\psi(e)^2=1$ for every $e$.

## Depends on

- [The ramified primes and the ideals $\mathfrak p_p$](../field/ramified-primes.md)
- [The genus class number](../genus-class-number.md)

## Sources

- [Step 3: ambiguous classes](../../../sources/redei-locators.md#step-3-ambiguous-classes)
