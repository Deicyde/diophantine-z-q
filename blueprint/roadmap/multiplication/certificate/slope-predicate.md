---
article_id: af_949b5d797e82cdb231fcfcb8
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Mult.SlopePred, ZInQ.Mult.slopeR0, ZInQ.Mult.slopeA, ZInQ.Mult.slopeR, ZInQ.Mult.normTests, ZInQ.Mult.groupW, ZInQ.Mult.traceTheta, ZInQ.Mult.certShifts
---

# The slope predicate

For $t,\ell\in\mathbb Q$ and $c=(c_0,c_1,c_2,c_3)\in\mathbb Z^4$, the slope predicate
$\mathrm{Slope}(t,\ell;c)$ holds when all of the following hold:

1. $t\notin\mathcal C\cup\{1\}$ and $\ell\ne0$;
2. there are $\eta\in\{1,-1\}$ and $q\in\mathbb Q$ such that, with
   $$R_0=\frac{\eta F(t)}{(t-1)^8},\qquad a=1-R_0q^2,\qquad R=\ell^2a^2R_0,$$
   one has $a\ne0$;
3. there are, for $g=1,\dots,6$, integers $h_g,z_{g,1},z_{g,2},z_{g,3}$ with $h_g\ne0$ and
   $h_g\ne c_0$ such that, with the test values $D_{gj}=\tau_j(h_g,z_g;c)\in K_0$ and the
   normalized values
   $$C_{gj}=\frac{D_{gj}}{R_0^{k_j}(t-1)^{k_j+1}}\qquad(k_j=1\text{ for }j\le8,\ k_j=25\text{ for }j\ge9),$$
   the elements $W_g=\prod_{j=1}^{12}\bigl(1+RC_{gj}^2\bigr)$ of $K_0$ and
   $\Theta=\operatorname{Tr}\sum_{g=1}^6W_g^{-1}\in\mathbb Q$ satisfy $W_g\ne0$ for every $g$,
   $\Theta\ne0$, and
   $$\Phi\bigl(R/\Theta^2\bigr).$$

Here $F(t)=t(t+15)(t+20)(t+24)(t+30)(t+60)$, $\Phi$ is the rational solubility of the pole
polynomial, and $\operatorname{Tr}(u+vs)=2u$. Since $F(t)\ne0$, $\ell\ne0$ and $a\ne0$, the pole
input $R/\Theta^2$ is nonzero, so the prefactor $B$ of $Q_{\rm pole}$ cannot make the pole
constraint vacuous. In the certificate $\ell=\ell_0$ and $c=(c_*,c_*n_1,c_*n_2,c_*n_3)$.

This is a definition.

## Depends on

- [The twelve local tests](twelve-tests.md)
- [Prime sets and clearing exponents of the multiplication certificate](constants.md)
- [Pole completeness](../../main/pole-completeness.md)

## Sources

- [Slope predicate](../../../sources/multiplication-locators.md#slope-predicate)
- [Multiplication certificate generator](../../../sources/multiplication-locators.md#multiplication-certificate-generator)
