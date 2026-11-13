---
article_id: af_2170ac7ff1b21a7278526919
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.jacobiSym_two_of_mod_eight, ZInQ.Contrib.HeckeFE.cpow_of_pos, ZInQ.Contrib.HeckeFE.const_identity, ZInQ.Contrib.HeckeFE.functionalEquation5_of_deuring_fourier, ZInQ.Contrib.HeckeFE.functionalEquation5_of_deuring_fourier'
---

# The functional equation from Deuring's identity and the Fourier identity

Let $\Lambda_N$ be the completed function of [the functional equation](../functional-equation.md):
$\Lambda_N(s)=N^{s/2}(2\pi)^{-s}\Gamma(s)F(s)$ for a given $F$.

1. If $d\equiv5\pmod8$, then $\left(\frac2d\right)=-1$.
2. For real $r>0$ and complex $z$, $r^z=e^{z\log r}$.
3. For $d>0$, with $N=32d^2$ and $M=4d$, and every complex $s$,
   $$N^{(2-s)/2}\,2^{-(2-s)}\,M\,(M^2)^{-(2-s)}\cdot(-8d)\cdot2^{-s}\,M\,(M^2)^{-s}
   =-N^{s/2}\,2^{-s}\,M\,(M^2)^{-s}.$$
4. Let $d\equiv5\pmod8$ be squarefree, and suppose that [Deuring's identity](deuring/deuring-identity.md)
   and [the Fourier identity](fourier/fourier-identity.md) hold for $d$. Then for every entire
   continuation $F$ of $L(C_d,s)$ and every $s$ with $0<\operatorname{Re}s<2$,
   $\Lambda_{32d^2}(2-s)=-\Lambda_{32d^2}(s)$.
5. If Deuring's identity and the Fourier identity hold for every squarefree $d\equiv5\pmod8$, then
   [the functional equation on the critical strip](../functional-equation.md) holds.

**Proof sketch.** (1) The supplementary law: $\left(\frac2d\right)=-1$ for $d\equiv\pm3\pmod8$.
(2) The definition of the complex power. (3) Write every power as an exponential by (2), with
$N=2M^2$ and $8d=2M$, and compare exponents.

(4) Put $M=4d$ and $c=\frac14\omega_d$, with $\omega_d$ the finite part of the
[Hecke character](gaussian/hecke-character.md). By the Fourier identity and
[the functional equation of a periodic twist](theta/twisted-functional-equation.md) (4), $c$
satisfies the Fourier relation with $\kappa=4d(1+i)\left(\frac2d\right)$, and by (1)
$-i\kappa(1+i)=-8d$.

*Step 1.* $F(s)=T_c(s)$ for $\operatorname{Re}s>3/2$, exactly as in
[the continuation from Deuring's identity](continuation-of-deuring.md) (1).

*Step 2.* $\pi^{-s}\Gamma(s)F(s)=M(M^2)^{-s}\Lambda_c(s)$ for $\operatorname{Re}s>0$. Both sides are
analytic on the half-plane $\operatorname{Re}s>0$, where $\Gamma$ has no poles; they agree on
$\operatorname{Re}s>3/2$ by Step 1 and the periodic twist (2); the half-plane is connected.

*Step 3.* With $(2\pi)^{-z}=2^{-z}\pi^{-z}$, Step 2 gives
$\Lambda_N(z)=N^{z/2}2^{-z}M(M^2)^{-z}\Lambda_c(z)$ for $\operatorname{Re}z>0$, which applies to
$z=s$ and $z=2-s$. The periodic twist (7) gives
$\Lambda_c(2-s)=-8d\cdot2^{-s}M(M^2)^{-s}\Lambda_c(s)$, and (3) turns the result into
$\Lambda_N(2-s)=-\Lambda_N(s)$.

(5) Apply (4) to each $d$.

## Depends on

- [The functional equation of $L(C_d,s)$ on the strip $0<\operatorname{Re}s<2$](../functional-equation.md)
- [Entire continuations of the L-series of an elliptic curve](../l-series-continuation.md)
- [Deuring's identity for $C_d$](deuring/deuring-identity.md)
- [The Fourier identity for $\omega_d$](fourier/fourier-identity.md)

## Proof depends on

- [The functional equation of a periodic twist under a Fourier relation](theta/twisted-functional-equation.md)
- [The continuation of $L(C_d,s)$ from Deuring's identity](continuation-of-deuring.md)
- [The Hecke character $\psi_d$](gaussian/hecke-character.md)

## Sources

- [Theta series and the method of Hecke](../../../../sources/hecke-locators.md#theta-series-and-the-method-of-hecke)
- [The functional equation and the root number](../../../../sources/rank-locators.md#the-functional-equation-and-the-root-number)
