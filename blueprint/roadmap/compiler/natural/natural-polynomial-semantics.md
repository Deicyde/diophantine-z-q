---
article_id: af_952178d744c7ff270932f6cb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.natural_polynomial_semantics, ZInQ.Compiler.natural_polynomial_semantics'
---

# Semantics of the natural precision polynomial

Let $\mathcal N$ be the five-input natural precision circuit, with variable count
$1{,}305{,}811$ and polynomial $[\![\mathcal N]\!]\in\mathbb Z[X_0,\dots,X_{1305810}]$ (call nodes
denoting literal substitution into the power template). For every $c\in\mathbb N^5$,
$$\bigl(\exists z\in\mathbb N^{1305806},\ [\![\mathcal N]\!](c,z)=0\bigr)\iff\operatorname{accepts}(c),$$
where $\operatorname{accepts}$ is the precision relation: with $(n,\kappa,a,l,j)$ the signed
decoding of $c$, the early tests $n\notin\mathcal C$, $\kappa\ne0$, $a,l\ge1$, $j=na$, the
admissibility of $l,a,j$, and the strict tests $|r(a,j)-n|<\epsilon_l$ and
$4\epsilon_l<4^{-A^{(0)}_{\rm ht}|\kappa F(n)|^{24}}$.

This is equation (C.4), the natural half of input $\mathsf C$. Its proof has no height,
restricted-converse or rational-model premise: the height constant enters only as a fixed
integer expression computed with caps, and admissibility replaces the generator theorem.
The witnesses are natural numbers; the rational translation is a separate statement.
Admissibility is part of the relation so that the theorem needs no input about $P_0$; under
the generator theorem it follows from the early tests ([admissibility of nonzero
indices](precision/precision-guards.md)).

**Proof sketch.** By the specialization statement,
$Z_{\mathcal N}(c)\iff Z_{\mathcal H}(c_3,\operatorname{enc}_5(c))$ with $c_3=\operatorname{code}(\mathcal W)$. By the
semantics of the universal halting circuit this is $\operatorname{halts}(c_3,\operatorname{enc}_5(c))$,
which by the codes of primitive programs is "the wrapper halts on $\operatorname{enc}_5(c)$", which
by the correctness of the wrapper is $\operatorname{accepts}(c)$. The number $1{,}305{,}806$ of
witness coordinates is the variable count $1{,}305{,}811$ of $\mathcal N$ minus its five inputs.

## Depends on

- [The five-input natural precision circuit](universal/precision-circuit.md)
- [Natural semantics of a natural circuit](formulas/natural-circuit-semantics.md)
- [The precision relation](precision/precision-relation.md)

## Proof depends on

- [The precision circuit is a specialization](universal/precision-circuit-specialization.md)
- [Semantics of the universal halting circuit](universal/halting-polynomial-semantics.md)
- [Codes of primitive programs](universal/program-numbering-encode.md)
- [Correctness of the wrapper](programs/wrapper-correct.md)
- [Shape of the natural precision circuit](universal/circuit-node-counts.md)

## Sources

- [Section 10.3 specialization](../../../sources/compiler-natural-locators.md#section-103-specialization)
- [Section 1 input C](../../../sources/compiler-natural-locators.md#section-1-input-c)
- [Section 10.1 saved polynomial](../../../sources/compiler-natural-locators.md#section-101-saved-polynomial)
