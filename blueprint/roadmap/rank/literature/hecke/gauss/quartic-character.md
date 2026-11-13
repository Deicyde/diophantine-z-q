---
article_id: af_60a29bd57c1f9b118446921f
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.GaussFE.gI, ZInQ.Contrib.GaussFE.gI_sq, ZInQ.Contrib.GaussFE.isPrimitiveRoot_gI, ZInQ.Contrib.GaussFE.pow_four_eq_one_cases, ZInQ.Contrib.GaussFE.twoTwoI, ZInQ.Contrib.GaussFE.unit_facts, ZInQ.Contrib.GaussFE.two_ne_zero_zmod, ZInQ.Contrib.GaussFE.exists_quartic, ZInQ.Contrib.GaussFE.chi_pow_four, ZInQ.Contrib.GaussFE.chi_apply_pow_four, ZInQ.Contrib.GaussFE.star_chi, ZInQ.Contrib.GaussFE.chi_pow_six, ZInQ.Contrib.GaussFE.chi_neg_one_sq, ZInQ.Contrib.GaussFE.chi_inv_apply, ZInQ.Contrib.GaussFE.chi_ne_one, ZInQ.Contrib.GaussFE.chi_sq_ne_one, ZInQ.Contrib.GaussFE.chi_cube_ne_one, ZInQ.Contrib.GaussFE.chi_inv, ZInQ.Contrib.GaussFE.chi_sq_inv, ZInQ.Contrib.GaussFE.quadraticChar_eq_chi_sq
---

# Quartic characters of $\mathbb F_p$ with values in $\mathbb Z[i]$

A *multiplicative character* of $\mathbb F_p$ with values in $\mathbb Z[i]$ is a map
$\chi:\mathbb F_p\to\mathbb Z[i]$ with $\chi(1)=1$, $\chi(ab)=\chi(a)\chi(b)$ and $\chi(0)=0$;
characters form a group under pointwise multiplication, with identity the character that is $1$
on $\mathbb F_p^\times$. For a prime $p$, $\left(\frac{\cdot}{p}\right)$ is the quadratic character
of $\mathbb F_p$ (with value $0$ at $0$), and $\bar z$ is the complex conjugate of $z\in\mathbb Z[i]$.

1. $i\in\mathbb Z[i]$ satisfies $i^2=-1$ and is a primitive fourth root of unity.
2. If $u\in\mathbb Z[i]$ and $u^4=1$, then $u\in\{1,-1,i,-i\}$, $\bar u=u^3$, and $2+2i$ divides
   $2(u-1)$.
3. If $p\ne2$ is prime, then $2\ne0$ in $\mathbb F_p$.
4. If $p\equiv1\pmod4$ is prime, there is a multiplicative character of $\mathbb F_p$ with values in
   $\mathbb Z[i]$ of order $4$.
5. Let $p$ be prime and $\chi$ a character of order $4$. Then $\chi^4=1$; $\chi(a)^4=1$ for
   $a\ne0$; $\overline{\chi(a)}=\chi(a)^3$ and $\chi(a)^6=\chi(a)^2$ for every $a$;
   $\chi(-1)^2=1$; $\chi(t^{-1})=\chi(t)^3$ for $t\ne0$; $\chi$, $\chi^2$ and $\chi^3$ are not the
   identity; $\chi^{-1}=\chi^3$ and $(\chi^2)^{-1}=\chi^2$.
6. If moreover $p\ne2$, then $\chi(a)^2=\left(\frac ap\right)$ for every $a\in\mathbb F_p$.

**Proof sketch.** (1) $i^2=-1\ne1$ and $i^4=1$, and $i^1,i^2,i^3\ne1$.

(2) $N(u)^4=1$ forces $N(u)=1$, so $u$ is one of the four units; check (2) for each.

(3) $\mathbb F_p$ has characteristic $p\ne2$.

(4) $\mathbb F_p^\times$ is cyclic of order $p-1$, divisible by $4$, and $\mathbb Z[i]$ contains the
primitive fourth root of unity $i$ (1); so a character of order exactly $4$ exists.

(5) Each identity follows from $\chi(a)^4=1$ for $a\ne0$, (2) for the conjugate, and the definition
of the order.

(6) Both sides vanish at $0$. Let $g$ generate $\mathbb F_p^\times$. Then
$\left(\frac gp\right)=-1$, since $g^{(p-1)/2}\ne1$; and $\chi(g)^2=-1$, since $(\chi(g)^2)^2=1$
while $\chi(g)^2=1$ would make $\chi^2$ the identity on every power of $g$. Every $a\ne0$ is a power
$g^n$, and both sides equal $(-1)^n$.

## Depends on

None.

## Sources

- [Gauss and Jacobi sums](../../../../../sources/hecke-locators.md#gauss-and-jacobi-sums)
