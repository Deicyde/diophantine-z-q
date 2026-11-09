---
article_id: af_44a9fcf4a44e0b96baf4f9bc
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Assembly.Pstar_spec, ZInQ.Assembly.assembly
---

# The assembly lemma

Assume the minimal height hypothesis, pole completeness and the slope representation.
Then the specified polynomial
$P_*\in\mathbb Z[X_0,\dots,X_{292890231904}]$ satisfies:

1. $\deg P_*<2\uparrow\uparrow7$;
2. every coefficient of $P_*$ has absolute value less than $2\uparrow\uparrow8$;
3. for every $q\in\mathbb Q$,
   $$\bigl(\exists\,w\in\mathbb Q^{292890231904}:\ P_*(q,w)=0\bigr)\iff q\in\mathbb Z .$$

In particular $P_*$ witnesses the target statement, from which the main theorem follows
at once.

This is the manuscript's Lemma 1.2 in the form used here, over the minimal form of H (the
instance $S=S_{\rm mul}$, $R=D$ of the six-contact estimate), PC, and the slope representation,
which is what the multiplication proof uses of 22P and which 22P and 22P₂ both give; the
manuscript's fourth input CAT is a theorem here (the catalogue bound holds). Its inputs are: G, that canonical codes form $2E(K_0)=\mathbb ZP_0$ with exact
membership and raw addition (from the generator certificate, whose Mordell–Weil input is
proved by the two-isogeny descent); M, multiplication (from the minimal height hypothesis, pole
completeness and the slope representation); C, the semantics of the
natural precision polynomial and its rational translation; B, the literal specification of
$P_*$ with its witness accounting and size bounds (the size bounds use the catalogue
bound); and the hypotheses H (in its minimal form) and PC themselves. Besides the three hypotheses, the proof uses
one finite computation, checked in the kernel: the node statistics of the universal halting circuit, on which the
witness accounting and the size bounds of B depend.

**Proof sketch.** Part 3: by the rational zero projection of the specified polynomial, the
left side holds exactly when $\mathrm{Rel}_{\mathtt{value}}(N,q)$ for some $N\in\mathbb Q^5$, and by the
exact ordinary-value relation this holds exactly when $q\in\mathbb Z$. Parts 1 and 2 are the
variable, degree and coefficient bounds for the same $P_*$; the constants $D$, $T$,
$H_{\rm cat}$ and the tower values are handled symbolically there and never evaluated. The
witness accounting shows that $P_*$ involves only $X_0,\dots,X_{292890231904}$, with input $X_0$
and $292890231904$ witnesses, so $P_*$, read in these variables, is a polynomial of the
shape required by the target statement.

## Depends on

- [The target statement](../main/frozen-target.md)
- [The specified polynomial](../syntax/literal-polynomial.md)
- [The minimal height hypothesis](../main/six-contact-min.md)
- [Pole completeness](../main/pole-completeness.md)
- [The slope representation](../multiplication/completeness/slope-representation.md)

## Proof depends on

- [The catalogue bound holds](../progressions/catalogue-instance.md)
- [The rational zero projection of the specified polynomial](../syntax/recipes/fin-variable-form.md)
- [The exact ordinary-value relation](ordinary-value-relation.md)
- [Variable, degree and coefficient bounds](../size/syntax-bounds.md)
- [Witness accounting of the specified polynomial](../syntax/recipes/witness-accounting.md)
- [Mordell-Weil for $E/K_0$ from the descent](../model/descent/mordell-weil-from-descent.md)

## Informally uses

- [The generator certificate](../model/generator.md)
- [Polynomial membership in the doubled group](../model/membership.md)
- [Raw addition](../model/raw-addition.md)
- [Correctness of the multiplication template](../multiplication/multiplication-template.md)
- [Semantics of the rational translation](../compiler/translation/rational-translation.md)

## Sources

- [Lemma 1.2](../../sources/assembly-locators.md#lemma-12)
- [Theorem 1.1 proof](../../sources/assembly-locators.md#theorem-11-proof)
- [Section 12 size](../../sources/assembly-locators.md#section-12-size)
