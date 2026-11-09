---
article_id: af_fca6e1326ab5141b86fdd02f
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.slope_rel_iff
---

# Semantics of the slope template

For all $t,\ell\in\mathbb Q$ and
$c=(c_0,c_1,c_2,c_3)\in\mathbb Z^4$,
$$\mathrm{Rel}_{\mathtt{slope}}\bigl(t,\ell,\iota(c_0),\iota(c_1),\iota(c_2),\iota(c_3)\bigr)\iff\mathrm{Slope}(t,\ell;c).$$

**Proof sketch.** The slope template polynomial is the square of the compilation of its
conjunction, so the relation holds iff some witness values satisfy every conjunct. The six
atoms of the first item say $\eta^2=1$, $t\ne1$, $F(t)\ne0$ (that is, $t\notin\mathcal C$),
$\ell\ne0$, $R_0(t-1)^8=\eta F(t)$ and $a\ne0$, which determine $R_0$. For each group the
test-group semantics turns the call into the existence of $(h_g,z_g)$ with
$[D_{g,j}]=\tau_j(h_g,z_g;c)$; since the denominators $R_0(t-1)^2$ and $R_0^{25}(t-1)^{26}$ are
nonzero, the pair equations $\mathrm{den}_j\,C'_{g,j}\doteq D_{g,j}$ say $[C'_{g,j}]=C_{gj}$; the
inverse gadget with $W_g\cdot\omega_g\doteq1$ says $W_g\ne0$ and $[\omega_g]=W_g^{-1}$, so
$\theta=2\sum_g(\omega_g)_0=\Theta$. Finally $\theta u_\theta\doteq1$ says $\Theta\ne0$,
$B\theta^2\doteq R$ says $B=R/\Theta^2$, and the pole call holds iff $\Phi(B)$, because the
pole template polynomial is $Q_{\rm pole}^2$. Conversely all witnesses can be chosen from
these values.

## Depends on

- [The slope template](../../syntax/templates/template-slope.md)
- [The slope predicate](slope-predicate.md)
- [Point codes](../../model/point-codes.md)

## Proof depends on

- [Semantics of the test-group template](test-group-semantics.md)
- [The pole template](../../syntax/templates/template-pole.md)
- [Inverse witnesses](../../syntax/nonzero-gadgets.md)
- [Pair arithmetic represents the quadratic field](../../syntax/field-pair-arithmetic.md)
- [Sums of squares and products over the rationals](../../syntax/sum-of-squares-semantics.md)
- [Evaluation of a template call](../../syntax/language/call-semantics.md)
- [Private witness blocks](../../syntax/language/existential-lifting.md)

## Sources

- [Slope predicate](../../../sources/multiplication-locators.md#slope-predicate)
- [Multiplication certificate generator](../../../sources/multiplication-locators.md#multiplication-certificate-generator)
