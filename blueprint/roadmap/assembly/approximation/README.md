---
article_id: af_edcebeb08b4defc20402def1
---

# Approximation for every fixed shift

The precision computation of the compiler chapter decides, for five integers
$(n,\kappa,a,l,j)$ given by their signed encodings, whether $n\notin\mathcal C$, $\kappa\ne0$, $a,l\ge1$,
$j=na$ and the two strict tests $|r(a,j)-n|<\epsilon_l$ and $4\epsilon_l<4^{-B(n,\kappa)}$ hold. All
quantities are exact rationals and integers. The compiler chapter defines the
[precision relation](../../compiler/natural/precision/precision-relation.md), the
[local parameter and the window quantities](../../compiler/natural/precision/z-coordinate.md),
the [signed encoding](../../compiler/natural/precision/signed-encoding.md) and the
[precision height constant](../../compiler/natural/precision/precision-height-constant.md), and
proves that this constant is the six-contact constant $H_6(S_{\rm ht})$, so that its bound is the
$B(n,\kappa)$ of the ordinary-value relation
([identification](../../compiler/natural/precision/precision-height-constant-value.md)).
Its admissibility clause is automatic for nonzero indices, by the
[nonzero-multiples lemma](../../model/descent/nonzero-multiples.md).

Close chooses codes $A,L,J$, links the five signed codes to the precision inputs in the order
$(n,\kappa,a,l,j)$ and imposes $|t-r(a,j)|<\epsilon_l$ on the same coordinates.

- [The relation Close](close-relation.md)

Soundness is the triangle inequality: $|t-n|<2\epsilon_l<4^{-B}/2<e^{-B}$.

- [Soundness of Close](close-soundness.md)

For completeness, positive multiples of $P_0$ approach the identity simultaneously at both real
places. The manuscript cites compactness of $E(\mathbf R)\times E(\mathbf R)$; here the needed
compactness and continuity of subtraction are proved by hand for real curves
$y^2=x^3-e^2x$.

- [Compactness and continuity of subtraction on a real curve](real-subtraction.md)
- [Multiples of the generator approach the identity at both real places](real-accumulation.md)

Near the identity, $z([n]Q)/z(Q)$ tends to $n$; with the division-polynomial formulas this is
a limit of rational functions at infinity.

- [The derivative of multiplication at a real place](real-derivative.md)

Choosing $l$ first so that $\epsilon_l$ is small enough, and then $a$ with $r(a,na)$ within
$\epsilon_l$ of $n$, gives Close for every fixed nonzero shift.

- [Completeness of Close for every fixed shift](close-completeness.md)
