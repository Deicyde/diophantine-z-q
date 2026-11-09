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

Moreover $P_*$ is $[\![\mathtt{integers}]\!]$ read in the variables indexed by
$\{0,\dots,292890231904\}$: $\mathrm{rename}(\iota)\,P_*=[\![\mathtt{integers}]\!]$ for the
inclusion $\iota$ of the indices into $\mathbb N$. Hence $P_*$ has total degree at most that of
$[\![\mathtt{integers}]\!]$ and the same coefficients,
$\mathrm{coeff}_d(P_*)=\mathrm{coeff}_{\iota_*d}([\![\mathtt{integers}]\!])$ for every exponent
vector $d$, and $P_*(v)=[\![\mathtt{integers}]\!](\bar v)$ for every
$v\in\mathbb Q^{292890231905}$, where $\bar v$ extends $v$ by zeros.

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
