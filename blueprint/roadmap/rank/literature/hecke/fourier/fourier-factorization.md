---
article_id: af_5ed949bb0ec0822d252f03c3
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.g2Sum, ZInQ.Contrib.HeckeFE.oddSum, ZInQ.Contrib.HeckeFE.crt_injective, ZInQ.Contrib.HeckeFE.sum_crt, ZInQ.Contrib.HeckeFE.cexp_two_pi_I_int_mul, ZInQ.Contrib.HeckeFE.cexp_shift, ZInQ.Contrib.HeckeFE.intCast_emod_eq, ZInQ.Contrib.HeckeFE.fourierHat_cd_eq
---

# The Fourier transform of $\omega_d$ splits into a 2-part and an odd part

For $\nu\in\mathbb Z^2$ and a natural number $d$ define the *2-part* and the *odd part*
$$G_2(\nu)=\sum_{a\in\{0,1,2,3\}^2}u(a)\,e^{2\pi i(a_1\nu_1+a_2\nu_2)/4},\qquad
G_d(\nu)=\sum_{b\in\{0,\dots,d-1\}^2}\left(\frac{b_1^2+b_2^2}d\right)e^{2\pi i(b_1\nu_1+b_2\nu_2)/d},$$
with $u$ the [primary unit](../gaussian/primary-unit.md). Let $\omega_d$ be the finite part of the
[Hecke character](../gaussian/hecke-character.md) on $(\mathbb Z/4d)^2$ and $\hat\omega_d$ its
Fourier transform as in [the functional equation of a periodic twist](../theta/twisted-functional-equation.md),
with $M=4d$.

1. If $d$ is odd, the map $(a,b)\mapsto(da+4b)\bmod4d$ is injective on
   $\{0,1,2,3\}\times\{0,\dots,d-1\}$.
2. If $d$ is odd and $g:\mathbb Z\to\mathbb C$ satisfies $g(x)=g(x\bmod4d)$ for every $x$, then
   $\sum_{j=0}^{4d-1}g(j)=\sum_{a=0}^{3}\sum_{b=0}^{d-1}g(da+4b)$.
3. $e^{2\pi in}=1$ for every integer $n$. If $M\ne0$, then
   $e^{2\pi i(A+kMn)/M}=e^{2\pi iA/M}$ for $A\in\mathbb C$ and integers $k,n$. For an integer $x$
   and a natural number $M$, $x\bmod M=x-qM$, where $q$ and $x\bmod M$ are the quotient and the
   remainder of Euclidean division of $x$ by $M$ ($q=0$ and $x\bmod M=x$ when $M=0$).
4. If $d\equiv1\pmod4$, then $\hat\omega_d(\nu)=G_2(\nu)\,G_d(\nu)$ for every $\nu\in\mathbb Z^2$.

**Proof sketch.** (1) $4$ and $d$ are coprime (Chinese remainder theorem). (2) By (1) and counting,
the map of (1) is a bijection onto $\{0,\dots,4d-1\}$. (3) Direct.

(4) The summand of $\hat\omega_d(\nu)$ is $4d$-periodic in each coordinate (by (3)), so (2) may be
applied in both coordinates: $j=da+4b$. Then $N(j)\equiv16N(b)\pmod d$ and
$\left(\frac{16}d\right)=1$, so $\left(\frac{N(j)}d\right)=\left(\frac{N(b)}d\right)$;
$j\equiv da\equiv a\pmod4$ as $d\equiv1\pmod4$, so $u(j)=u(a)$; and
$(da+4b)\cdot\nu/(4d)=a\cdot\nu/4+b\cdot\nu/d$. The double sum factors.

## Depends on

- [The primary unit of a Gaussian integer modulo 4](../gaussian/primary-unit.md)
- [The Hecke character $\psi_d$](../gaussian/hecke-character.md)
- [The functional equation of a periodic twist under a Fourier relation](../theta/twisted-functional-equation.md)

## Sources

- [Gauss and Jacobi sums](../../../../../sources/hecke-locators.md#gauss-and-jacobi-sums)
