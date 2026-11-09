---
article_id: af_a2f47599157b711d493e7cbb
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.multiply_rel_iff_unguarded, ZInQ.Mult.multiply_rel_iff, ZInQ.Mult.multiply_rel_iff_cert
---

# Unfolding the multiplication template

For all $Y_1,Y_2,Y_3\in\mathbb Q^5$,
$\mathrm{Rel}_{\mathtt{multiply}}(Y_1,Y_2,Y_3)$ holds if and only if there are
$n_1,n_2,n_3\in\mathbb Z$ with $Y_i=\iota(n_i)$ such that
$$\mathrm{Rel}_{\mathtt{height\_certificate}}\bigl(Y_1,Y_2,Y_3,\ell_0,\iota(c_*),\iota(c_*n_1),\iota(c_*n_2),\iota(c_*n_3)\bigr)
\quad\text{and}\quad\mathrm{Rel}_{\mathtt{multiply.guard}}(Y_1,Y_2,Y_3).$$
The part without the guard is the *unguarded certificate*.

**Proof sketch.** The template polynomial is the sum of the three squared generator
equations and the square of the compilation of $\varphi_{\rm mul}$, so a zero forces
$c_1=1641/8$, $c_2=-15465/4$, $c_3=87483/32$ and makes $G=(0,c_1,-145,c_2,c_3)=\iota(1)$, the
code of $P_0$. The three membership calls inside the height-certificate conjunct do not
involve the shift points and force $Y_i=\iota(n_i)$ (accepted inputs have unique indices). The
four scalar conjuncts $S_{c_*}[\Pi_k,S_k]$ then concern codes of points of $2E(K_0)$, and since
$c_*\ge1$ the fixed-scalar semantics gives $S_0=\iota(c_*)$ and $S_i=\iota(c_*n_i)$; only now
are the shift points known to be canonical, so that the semantics of the height certificate
applies. The node
$\mathrm{fixed}\ \ell$ has value $\ell_0$. Conversely, given the right side, take these
values for the constants and shift points and the witnesses supplied by the scalar,
certificate and guard relations, in disjoint private blocks.

## Depends on

- [The multiplication template](../../syntax/templates/template-multiply.md)
- [The height certificate template](../../syntax/templates/template-height-certificate.md)
- [The guard template](../../syntax/templates/template-guard.md)
- [Prime sets and clearing exponents of the multiplication certificate](constants.md)
- [Point codes](../../model/point-codes.md)

## Proof depends on

- [Semantics of the height certificate template](height-certificate-semantics.md)
- [Accepted inputs have unique indices](../../model/membership-indices.md)
- [Semantics of the fixed-scalar templates](../../syntax/fixed-scalar-semantics.md)
- [Properties of the multiplication constants](constants-properties.md)
- [Rational constants by global equations](../../syntax/language/rational-constants.md)
- [Elementary properties of codes](../../model/field/point-code-properties.md)
- [Evaluation of a template call](../../syntax/language/call-semantics.md)
- [Private witness blocks](../../syntax/language/existential-lifting.md)
- [Sums of squares and products over the rationals](../../syntax/sum-of-squares-semantics.md)
- [Mordell-Weil for $E/K_0$ from the descent](../../model/descent/mordell-weil-from-descent.md)

## Sources

- [Height certificate](../../../sources/multiplication-locators.md#height-certificate)
- [Section 6 opening](../../../sources/multiplication-locators.md#section-6-opening)
