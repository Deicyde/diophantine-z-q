---
article_id: af_4c78eec56e9d363166369fef
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Assembly.closeCoordinates_rel_iff
---

# Semantics of the coordinate window

For all $A,L,J\in\mathbb Q^5$ and $t\in\mathbb Q$,
$\mathrm{Rel}_{\mathtt{value.close\_coordinates}}(A,L,J,t)$ holds exactly when there are
$a,l,j\in\mathbb Z$ with
$$A=\iota(a),\quad L=\iota(l),\quad J=\iota(j),\quad a\ne0,\quad l\ne0,\quad |t-r(a,j)|<\epsilon_l ,$$
with $r(a,j)=\frac12\operatorname{Tr}(z_j/z_a)$ and $\epsilon_l$ formed from the local parameter $z$ on
multiples of the generator, extended by $z_0=0$ (so $r(a,0)=0$); $a,l$ and every nonzero $j$ are
admissible by the nonzero-multiples lemma.

**Proof sketch.** The template is $\kappa(\varphi)^2$; its calls ($\mathtt{member}$ three times,
$\mathtt{value.abs}$ three times) have disjoint blocks occurring in no parameter, so by the
private-witness lemma the relation holds exactly when there are pairs
$\zeta_A,\zeta_L,\zeta_J,q$ and rationals $v,a_0,a_1,\delta,u_\epsilon,z_1,\dots,z_4$ and inverse
witnesses making the following true: $A,L,J$ are accepted by membership, $A[0]=L[0]=0$ (first code coordinates), the
gadgets $Z(A,\zeta_A)$, $Z(L,\zeta_L)$, $Z(J,\zeta_J)$, $\operatorname N(\zeta_A)v=1$ and
$\zeta_A\cdot q=\zeta_J$, $a_0=|(\zeta_L)_0|$, $a_1=|(\zeta_L)_1|$, $(a_0+a_1)u_\epsilon=1$,
$\delta=|t-q_0|$ and $(a_0+a_1-\delta)(z_1^2+z_2^2+z_3^2+z_4^2)=1$.

By the accepted-indices statement, membership means $A=\iota(a)$, $L=\iota(l)$, $J=\iota(j)$. The
conditions $A[0]=L[0]=0$ say $a\ne0$ and $l\ne0$ (first code coordinate). By the
nonzero-multiples lemma, every nonzero multiple of $P_0$ has nonzero abscissa and ordinate,
so by pair arithmetic the gadget $Z(\iota(m),\zeta)$ is satisfiable and forces $[\zeta]=z_m$
(also for $m=0$, where $z_0=0$). Then $\operatorname N(\zeta_A)\ne0$ holds because $z_a\ne0$, and
$[q]=z_j/z_a$, so $q_0=r(a,j)$. The absolute-value template gives $a_0+a_1=\epsilon_l$, which is
nonzero because $z_l\ne0$, so its inverse witness exists. Finally $\delta=|t-r(a,j)|$, and the
four-square positivity statement turns the last equation into $\epsilon_l-|t-r(a,j)|>0$.
Conversely, for $a,l\ne0$ and the strict window, all these witnesses exist.

## Depends on

- [The coordinate-window template](../../syntax/templates/template-close-coordinates.md)
- [The local parameter z on multiples of the generator](../../compiler/natural/precision/z-coordinate.md)
- [Point codes](../../model/point-codes.md)

## Proof depends on

- [Accepted inputs have unique indices](../../model/membership-indices.md)
- [Nonzero multiples of the generator](../../model/descent/nonzero-multiples.md)
- [Pair arithmetic represents the quadratic field](../../syntax/field-pair-arithmetic.md)
- [The absolute-value template](../../syntax/templates/template-abs.md)
- [Absolute value by four squares](../../syntax/language/absolute-value-gadget.md)
- [Strict positivity by four squares](../../syntax/language/positivity-gadget.md)
- [Inverse witnesses](../../syntax/nonzero-gadgets.md)
- [Private witness blocks](../../syntax/language/existential-lifting.md)
- [Template construction from formulas](../../syntax/language/builder-soundness.md)
- [Witness scope of constructed templates and recipes](../../syntax/language/builder-well-formed.md)
- [Mordell-Weil for $E/K_0$ from the descent](../../model/descent/mordell-weil-from-descent.md)

## Sources

- [Section 10 precision predicate](../../../sources/assembly-locators.md#section-10-precision-predicate)
- [Section 11.1 approximation](../../../sources/assembly-locators.md#section-111-approximation)
- [Saved specification outer recipes](../../../sources/assembly-locators.md#saved-specification-outer-recipes)
