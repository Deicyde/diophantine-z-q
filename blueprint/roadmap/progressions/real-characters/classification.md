---
article_id: af_b11d599aa85f39a072d01b09
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.exists_legendre_of_real_char, ZInQ.Progressions.exists_legendre_of_real_char_dvd
---

# Real characters are Legendre symbols away from $2q$

Let $q\ge1$ and let $\chi$ be a nonprincipal Dirichlet character modulo $q$ with
$\chi^2=\chi_0$. Then there is a squarefree integer $d\ne1$ such that $|d|$ divides $q$, $8$
divides $q$ if $d$ is even, and
$$\chi(p)=\Bigl(\frac dp\Bigr)\qquad\text{for every prime }p\nmid2q .$$
In particular $|d|\le q$ and every prime factor of $d$ divides $q$.

**Proof sketch.** A real character is $1$ at the square of every unit. Hensel lifting shows
which units are squares: modulo $p^k$ with $p$ odd, the squares of units are the residues
that are squares modulo $p$; modulo $2^k$, every $n\equiv1\pmod8$ is a square. So modulo
$p^k$, $p$ odd, $\chi$ is $1$ at the quadratic residues and constant at the nonresidues,
hence $\chi(\ell)=(p^*/\ell)$ for primes $\ell\nmid2p$ or $\chi$ is trivial, with
$p^*=(-1)^{(p-1)/2}p$ (by reciprocity, $(\ell/p)=(p^*/\ell)$). Modulo $2^k$, $\chi(\ell)$
depends only on $\ell\bmod8$ and is fixed by $\chi(3),\chi(5)\in\{\pm1\}$; the four cases give
$d=1,-1,2,-2$, and $\chi(5)=-1$ forces $k\ge3$. For coprime moduli, split $\chi$ by the
Chinese remainder theorem; the integers $d$ of the two components multiply, by
multiplicativity of the Legendre symbol. Induction over the factorization of $q$ gives a
squarefree $d$ with $|d|\mid q$, $2\mid d\Rightarrow8\mid q$ and $\chi(p)=(d/p)$ for primes
$p\nmid2q$. If $d=1$, then $\chi(p)=1$ for every prime $p\nmid2q$; since every unit class
modulo $q$ contains such primes (Dirichlet's theorem, without bounds), $\chi$ would be
principal. So $d\ne1$.

## Depends on

None.

## Sources

- [Davenport, Chapter 5](../../../sources/progressions-locators.md#davenport-chapter-5)
- [Davenport, Chapter 4](../../../sources/progressions-locators.md#davenport-chapter-4)
- [Apostol, Chapter 9](../../../sources/progressions-locators.md#apostol-chapter-9)
