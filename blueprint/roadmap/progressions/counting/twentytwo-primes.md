---
article_id: af_610b61cb31c5ec6a071c67ce
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.twentytwo_primes_of_twisted_bound, ZInQ.Progressions.twentytwo_primes_of_LFunction_lower_bound, ZInQ.Progressions.classSum_sub_ge, ZInQ.Progressions.sum_Ioc_classSum_le
---

# Twenty-two primes from a twisted sum bound

Let $q\ge3$ and $B\ge1$ be such that
$\bigl|\sum_{n\le t}\chi(n)\Lambda(n)/n\bigr|\le B$ for every nonprincipal Dirichlet character
$\chi$ modulo $q$ and every real $t\ge1$. Let $a\ge0$ be an integer coprime to $q$. Then at
least $22$ primes $p\equiv a\pmod q$ satisfy
$$q^8<p\le q^8e^{5qB}.$$
In particular, if $c>0$ and $|L(1,\chi)|\ge c$ for every nonprincipal character $\chi$
modulo $q$, then this holds with $B=((\log q+3)^2+6q)/c$.

**Proof sketch.** Let $S_a(t)=\sum_{n\le t,\ n\equiv a}\Lambda(n)/n$, $y=q^8$ and
$x=q^8e^{5qB}$, so $\log(x/y)=5qB$. Detecting the class by characters, the principal
character contributes at least $\log(x/y)-6-\log q$ to $\varphi(q)(S_a(x)-S_a(y))$, and each
of the other $\varphi(q)-1$ characters at most $2B$ in absolute value. So
$$S_a(x)-S_a(y)\ge\frac{\log(x/y)-6-\log q-2B(\varphi(q)-1)}{\varphi(q)}\ge1,$$
using $\varphi(q)\le q$, $\log q\le q-1$, $B\ge1$ and $q\ge3$. On the other hand, each prime
$p>y$ contributes $\log p/p\le\log y/y\le16/6561$ (as $y\ge3^8=6561$ and $\log t/t$
decreases for $t\ge3$), and the prime powers $p^k$ with $k\ge2$ above $y$ contribute at most
$(\log s+2+2\log4)/s\le16/81$ with $s=\lfloor\sqrt y\rfloor=q^4\ge81$. If at most $21$
primes $p\equiv a$ lay in $(y,x]$, then $S_a(x)-S_a(y)\le21\cdot16/6561+16/81<1$. For the
last claim, the twisted sum bound gives $|S_\chi(t)|\le((\log q+3)^2+6q)/c$, which is at least
$1$ since $c\le|L(1,\chi)|\le\log q+3$ for some nonprincipal $\chi$ (one exists as $q\ge3$).

## Depends on

None.

## Proof depends on

- [Detecting a residue class by characters](orthogonality.md)
- [The principal character](principal-character.md)
- [Higher prime powers contribute little](prime-powers.md)
- [The twisted sum and $L(1,\chi)$](twisted-sum-bound.md)
- [A bound for $L(\sigma,\chi)$ near $1$](../lseries/l-value-bound.md)

## Sources

- [Apostol, Chapter 7](../../../sources/progressions-locators.md#apostol-chapter-7)
