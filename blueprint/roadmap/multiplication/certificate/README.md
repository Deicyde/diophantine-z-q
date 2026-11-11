---
article_id: af_d02df4812f02a2aeb287c2a2
---

# The certificate and its semantics

This section fixes the constants of the multiplication certificate and translates each of
its templates into a mathematical predicate. All statements here are exact equivalences
for the constructed templates, proved from the semantics of the expression language; the
arithmetic happens in the soundness and completeness sections.

## Constants

The certificate uses the prescribed constants $c_*=4M_0$, $\ell_0=12P_s^{2916}H_{\rm cat}^{732}$,
$R$, $A_{\rm ht}$ and $T$ of the specification. The sound direction works outside
$S_{\rm mul}=S_{\rm ht}\cup\mathcal H\cup\operatorname{supp}(c_*)$; the complete direction
clears denominators at the old primes $S_b=S_{\rm ht}\cup\mathcal H$ with the exponents
$B_p$, $C_p=14B_p$, $D_p=51C_p$, $E_p=52C_p+v_p(12)+4$. No constant is evaluated; the only
numerical facts are a handful of small identities.

- [Prime sets and clearing exponents of the multiplication certificate](constants.md)
- [The clearing inequalities](clearing-arithmetic.md)
- [Properties of the multiplication constants](constants-properties.md)

## The local templates and the twelve tests

The templates $\mathtt{raw\_z}$, $\mathtt{raw\_inverse\_x}$ and $\mathtt{log25}$ compute
$z=-x/y$, $1/x$ and the truncated logarithm $L$ on codes of $2E(K_0)$.

- [Semantics of the local-parameter, inverse-abscissa and logarithm templates](local-templates.md)

For indices $n_1,n_2,n_3$, a test group chooses $H=[h]P_0$ and $U_i=[z_i]P_0$ and sets
$V_0=H-[c_*]P_0$, $V_i=U_i-[c_*n_i]P_0$. Its twelve tests are the four inverse abscissas at
$H,U_i$, their conjugate counterparts at $V_0,V_i$, three differences of $L$-ratios and one
product test. Identity inverse abscissas are zero, and the two guarded denominators are
nonzero once $H$ and $V_0$ are not the identity.

- [The twelve local tests](twelve-tests.md)
- [Semantics of the test-group template](test-group-semantics.md)

## The slope predicate

For a slope $t\notin\mathcal C\cup\{1\}$ the certificate normalizes the twelve tests of each
of six groups by powers of $R_0=\eta F(t)/(t-1)^8$ and $t-1$, forms
$W_g=\prod_j(1+RC_{gj}^2)$ with $R=\ell_0^2a^2R_0$, $a=1-R_0q^2\ne0$, takes the trace
$\Theta=\operatorname{Tr}\sum_gW_g^{-1}$, and imposes the pole predicate $\Phi(R/\Theta^2)$ on a
nonzero input.

- [The slope predicate](slope-predicate.md)
- [Semantics of the slope template](slope-semantics.md)

## The height certificate and the multiplication template

The height certificate imposes membership on the three inputs, writes each abscissa as
$(a_{i0}+a_{i1}s)/b_i$, expresses each of the nine rational quantities as a sum of three
slopes, and imposes the slope predicate on all $27$ slopes. The multiplication template
conjoins it with the four fixed scalar graphs, which supply the shift points
$\iota(c_*),\iota(c_*n_i)$, and with the inverse of the finite guard.

- [Semantics of the height certificate template](height-certificate-semantics.md)
- [Unfolding the multiplication template](multiply-unfolding.md)

The guard is a product, over the false triples $(a,b,c)\in[-T,T]^3$, of denominator-cleared
squared distances to $(\iota(a),\iota(b),\iota(c))$; its semantics is proved in the
specification chapter ([semantics of the guard template](../../syntax/templates/guard-semantics.md)).
By injectivity of codes it passes every true triple and rejects every false triple in the
box.

- [The guard passes true triples and rejects false triples in the box](guard-true-triples.md)
