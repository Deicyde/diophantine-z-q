---
article_id: af_8c73b3ee48583dca36302529
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.GaussFE.card_cubic_eq, ZInQ.Contrib.GaussFE.sum_sq_comp, ZInQ.Contrib.GaussFE.sum_chi_sq_cubic, ZInQ.Contrib.GaussFE.jacobi_conj, ZInQ.Contrib.GaussFE.jacobi_mul_star
---

# The point count of $y^2=x^3-x$ as a quartic Jacobi sum

For multiplicative characters $\chi,\varphi$ of $\mathbb F_p$ with values in $\mathbb Z[i]$ (as in
[quartic characters](quartic-character.md)), the *Jacobi sum* is
$J(\chi,\varphi)=\sum_{t\in\mathbb F_p}\chi(t)\varphi(1-t)$. For a prime $p$,
$\left(\frac{\cdot}{p}\right)$ is the quadratic character of $\mathbb F_p$.

1. If $p\ne2$ is prime, then
   $\#\{(x,y)\in\mathbb F_p^2:y^2=x^3-x\}=p+\sum_{x\in\mathbb F_p}\left(\frac{x^3-x}p\right)$.

In (2)–(5), $p$ is prime and $\chi$ is a character of order $4$.

2. If $p\ne2$, then for every $F:\mathbb F_p\to\mathbb Z[i]$,
   $\sum_xF(x^2)=\sum_t(1+\chi(t)^2)F(t)$.
3. If $p\ne2$, then $\sum_x\chi(x^3-x)^2=J(\chi,\chi^2)+J(\chi^3,\chi^2)$.
4. $J(\chi^3,\chi^2)=\overline{J(\chi,\chi^2)}$.
5. $J(\chi,\chi^2)\,\overline{J(\chi,\chi^2)}=p$.

**Proof sketch.** (1) A value $x$ contributes $1+\left(\frac{x^3-x}p\right)$ solutions $y$.

(2) The number of $x$ with $x^2=t$ is $1+\left(\frac tp\right)=1+\chi(t)^2$
([quartic characters](quartic-character.md) (6)).

(3) $x^3-x=x\cdot(-1)\cdot(1-x^2)$ and $\chi(-1)^2=1$, so
$\chi(x^3-x)^2=\chi(x^2)\chi(1-x^2)^2$. Apply (2) to $F(t)=\chi(t)\chi(1-t)^2$:
$(1+\chi(t)^2)\chi(t)\chi(1-t)^2=\chi(t)\chi^2(1-t)+\chi^3(t)\chi^2(1-t)$.

(4) Termwise, $\overline{\chi(a)}=\chi(a)^3$ and $\chi(a)^6=\chi(a)^2$.

(5) In $\mathbb C$: for nontrivial characters $\chi,\varphi$ of $\mathbb F_p$ with $\chi\varphi$
nontrivial, $J(\chi,\varphi)J(\chi^{-1},\varphi^{-1})=p$ (a standard identity). Here $\chi$,
$\chi^2$ and $\chi^3$ are nontrivial, $\chi^{-1}=\chi^3$ and $(\chi^2)^{-1}=\chi^2$, so the left
side is $J(\chi,\chi^2)J(\chi^3,\chi^2)$, which is the claim by (4). The embedding
$\mathbb Z[i]\to\mathbb C$ is injective, so the identity holds in $\mathbb Z[i]$.

## Depends on

- [Quartic characters of $\mathbb F_p$ with values in $\mathbb Z[i]$](quartic-character.md)

## Sources

- [Gauss and Jacobi sums](../../../../../sources/hecke-locators.md#gauss-and-jacobi-sums)
