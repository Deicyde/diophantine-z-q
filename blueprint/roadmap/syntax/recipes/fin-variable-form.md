---
article_id: af_1a2cc86d291d4eae733f9e52
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Syntax.PstarOf_spec, ZInQ.Syntax.PstarOf_zero_projection, ZInQ.Syntax.specPstar_spec, ZInQ.Syntax.specPstar_zero_projection
---

# The rational zero projection of the specified polynomial

For every $q\in\mathbb Q$ the following are equivalent:

1. there is $w=(w_1,\dots,w_{292890231904})\in\mathbb Q^{292890231904}$ with $P_*(q,w_1,\dots,w_{292890231904})=0$;
2. $\mathrm{Rel}_{\mathtt{integers}}(q)$;
3. there is $x:\mathbb N\to\mathbb Q$ with $x_0=q$ and $[\![\mathtt{integers}]\!]\,(x)=0$;
4. there are $N\in\mathbb Q^5$ and rational values of the witnesses of $\mathtt{value}$ making
   $[\![\mathtt{value}]\!]$ vanish at $(N,q)$, that is, $\mathrm{Rel}_{\mathtt{value}}(N,q)$ for
   some $N\in\mathbb Q^5$.

Moreover $P_*$, read as a polynomial $Q$ in the variables indexed by $\{0,\dots,292890231904\}$
(that is, $Q$ with $\mathrm{rename}(\iota)\,Q=[\![\mathtt{integers}]\!]$ for the inclusion
$\iota$ of the indices into $\mathbb N$), has total degree at most that of $P_*$ and the same
coefficients: $\mathrm{coeff}_d(Q)=\mathrm{coeff}_{\iota_*d}(P_*)$ for every exponent vector $d$.

So the rational zero projection of $P_*$ to its first variable is
$\{q:\exists N,\ \mathrm{Rel}_{\mathtt{value}}(N,q)\}$, which the assembly chapter identifies with
$\mathbb Z$.

**Proof sketch.** By the witness accounting, $[\![\mathtt{integers}]\!]$ involves only
$X_0,\dots,X_{292890231904}$, so its value at $x$ depends only on $x_0,\dots,x_{292890231904}$ and
equals $P_*(x_0,\dots,x_{292890231904})$; this gives $1\iff2\iff3$ (unused variables take
arbitrary values, for instance $0$). For $3\iff4$: $[\![\mathtt{integers}]\!]$ is the square
of one call of $\mathtt{value}$ with parameters $X_1,\dots,X_5,X_0$ and block
$[6,292890231905)$, which is disjoint from $X_0,\dots,X_5$; apply the evaluation of a call and
the compilation theorem.

## Depends on

- [The specified polynomial](../literal-polynomial.md)
- [The outer composition recipes](outer-recipes.md)

## Proof depends on

- [Witness accounting of the specified polynomial](witness-accounting.md)
- [Evaluation of a template call](../language/call-semantics.md)
- [Sums of squares and products over the rationals](../sum-of-squares-semantics.md)

## Sources

- [Appendix C opening](../../../sources/syntax-locators.md#appendix-c-opening)
- [Section 2 opening](../../../sources/syntax-locators.md#section-2-opening)
