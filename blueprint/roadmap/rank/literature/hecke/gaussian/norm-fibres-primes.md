---
article_id: af_140e72f88911a3e974166de0
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.normFiber_eq_empty_of_mod_four_eq_three, ZInQ.Contrib.HeckeFE.dvd_of_dvd_sq_add_sq, ZInQ.Contrib.HeckeFE.normFiber_inert, ZInQ.Contrib.HeckeFE.prime_of_norm_prime, ZInQ.Contrib.HeckeFE.sum_mul_bij
---

# Gaussian integers whose norm is a prime power

Notation of [Gaussian integers as pairs](norm-fibres.md): $A_n$ is the set of Gaussian integers of
norm $n$.

1. If $n\equiv3\pmod4$, then $A_n$ is empty.
2. Let $p\equiv3\pmod4$ be prime. If $p\mid a^2+b^2$ for integers $a,b$, then $p\mid a$ and
   $p\mid b$. For every $k\ge0$, $A_{p^{k+2}}=\{p\beta:\beta\in A_{p^k}\}$.
3. A Gaussian integer whose norm is a prime number is a prime element of $\mathbb Z[i]$.
4. Let $p>0$ be a natural number, $z$ a Gaussian integer of norm $p$, $n$ a natural number and
   $f:\mathbb Z^2\to\mathbb C$. Then
   $$\sum_{\beta\in A_n}f(z\beta)=\sum_{\gamma\in A_{pn},\ z\mid\gamma}f(\gamma).$$

**Proof sketch.** (1) Squares are $0$ or $1$ modulo $4$, so $a^2+b^2\not\equiv3$.

(2) If $p\nmid b$, then $(ab^{-1})^2\equiv-1\pmod p$, but $-1$ is not a square modulo a prime
$p\equiv3\pmod4$. So $p\mid b$, and then $p\mid a$. For $\gamma\in A_{p^{k+2}}$ both coordinates
are divisible by $p$, and $\gamma/p\in A_{p^k}$; conversely $N(p\beta)=p^2N(\beta)$.

(3) A unit has norm $1$, so a Gaussian integer $x$ of prime norm is not a unit; if $x=yz$, then
$N(y)N(z)$ is prime, so $y$ or $z$ has norm $1$ and is a unit. So $x$ is irreducible, hence prime,
as $\mathbb Z[i]$ is a principal ideal domain.

(4) $z\ne0$. The map $\beta\mapsto z\beta$ sends $A_n$ into the elements of $A_{pn}$ divisible by
$z$, with inverse $\gamma\mapsto\gamma/z$.

## Depends on

- [Gaussian integers as pairs, norms and units](norm-fibres.md)

## Sources

- [Arithmetic of the Gaussian integers](../../../../../sources/hecke-locators.md#arithmetic-of-the-gaussian-integers)
