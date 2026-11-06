---
article_id: af_386c166797b3bc6c814dbce0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Mult.uSeries_eq, ZInQ.Mult.invDiffSeries_ode, ZInQ.Mult.coeff_formalLog_genE
---

# The formal logarithm of $E$ is a binomial series

For the generator curve $E:y^2=x^3-d^2x$ ($A=-d^2$, $d=75-53s$), with $z=-x/y$:

1. the abscissa reciprocal $u=1/x$ is the unique power series $u(z)=z^2+O(z^3)$ with
   $z^2(1-d^2u^2)=u$, and $1+2d^2z^2u(z)=\sqrt{1+4d^2z^4}$ (the square root with constant
   term $1$); in particular $u(z)=z^2$ times a unit of $\mathbb Z[s][[z]]$;
2. the invariant differential is
   $$\frac{dx}{2y}=\frac{dz}{\sqrt{1+4d^2z^4}},\qquad
   (1+4d^2z^4)^{-1/2}=\sum_{j\ge0}(-1)^j\binom{2j}{j}d^{2j}z^{4j};$$
3. hence the formal logarithm of $E$ is
   $$\log(T)=\sum_{j\ge0}\frac{(-1)^j\binom{2j}{j}\,d^{2j}}{4j+1}\,T^{4j+1}.$$

These are identities of formal power series with coefficients in $K_0$; they hold over every
completion of $K_0$.

**Proof sketch.** From $y^2=x^3+Ax$, $z^2=x^2/y^2=x/(x^2+A)=u/(1+Au^2)$, so
$Az^2u^2-u+z^2=0$, whose power-series root with $u(0)=0$ satisfies
$1-2Az^2u=\sqrt{1-4Az^4}$ and $u=z^2(1+Az^4+\cdots)$. Since $x=1/u$ and $y=-x/z$,
$dx/(2y)=z\,du/(2u)$. Differentiating the quadratic gives
$du\,(1-2Az^2u)=2z(1+Au^2)\,dz$, and with $z^2(1+Au^2)=u$ this yields
$dx/(2y)=dz/\sqrt{1-4Az^4}$. With $A=-d^2$ and
$\binom{-1/2}{j}4^j=(-1)^j\binom{2j}{j}$ the binomial series gives (2), and termwise
integration with constant term $0$ gives (3), the formal logarithm being the formal integral
of the invariant differential normalized by $\log(T)=T+\cdots$.

## Depends on

- [The generator curve $E$](../../model/field/generator-curve.md)
- [The formal logarithm](formal-logarithm.md)

## Sources

- [Logarithm series](../../../sources/multiplication-locators.md#logarithm-series)
- [Local conventions](../../../sources/multiplication-locators.md#local-conventions)
