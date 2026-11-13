---
article_id: af_e2651dd7d386b3d71b326565
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.chi_psi, ZInQ.RouteK.Redei.chi_ramIdeal, ZInQ.RouteK.Redei.chi_ramIdeal_self, ZInQ.RouteK.Redei.chi_prod_ramIdeal
---

# The genus characters on the ambiguous classes

Let $n$ be odd and squarefree, $q$ a prime dividing $n$ and $R$ the Rédei matrix of $n$. For every
$e\in\mathbb F_2^{T_n}$,
$$\chi_q\bigl(\psi(e)\bigr)=\chi_q\Bigl(\prod_{p\in T_n}[\mathfrak p_p]^{e_p}\Bigr)=\sum_{p\in T_n}R_{qp}\,e_p .$$
In particular $\chi_q([\mathfrak p_p])=R_{qp}$ for every $p\in T_n$, and
$\chi_q([\mathfrak p_q])=\bigl[(n/q)/q\bigr]$.

**Proof sketch.** As $n$ is odd, $q\ne2$, and $N(\mathfrak p_p)=p$ for every $p\in T_n$.

- For $p=2$: $q\nmid2$, so $\chi_q([\mathfrak p_2])=[2/q]=R_{q2}$.
- For $p\ne q$ odd: $q\nmid p$, so $\chi_q([\mathfrak p_p])=[p/q]=R_{qp}$.
- For $p=q$: the ideal $J=\prod_{p\mid n,\,p\ne q}\mathfrak p_p$ satisfies $\mathfrak p_qJ=(\omega)$,
  which is principal, and $N(J)=\prod_{p\mid n,\,p\ne q}p=n/q$ is prime to $q$. Hence
  $\chi_q([\mathfrak p_q])=-\chi_q([J])=[(n/q)/q]=R_{qq}$, as $-a=a$ in $\mathbb F_2$.

The formula for $\prod_p[\mathfrak p_p]^{e_p}$ follows because $\chi_q$ is a homomorphism, and it
is the formula for $\psi(e)$ because $c_p=[\mathfrak p_p]$ for odd squarefree $n$.

## Depends on

- [The genus characters](genus-characters.md)
- [The ambiguous class map $\psi$](ambiguous-class-map.md)
- [The Rédei matrix](../redei-matrix.md)

## Proof depends on

- [The classes of the ramified primes](ramified-classes.md)
- [The primes of the discriminant ramify](../field/ramified-prime-ideals.md)
- [The ideal $(\sqrt{-n})$ is the product of the ramified odd primes](../field/ideal-of-omega.md)

## Sources

- [Step 4: genus characters](../../../sources/redei-locators.md#step-4-genus-characters)
