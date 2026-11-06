---
article_id: af_9475ebe08a0ae5387320b869
declaration: def
origin: cited
---

# The five-input specialization

Let $H\in\mathbb Z[X_0,\dots,X_{V-1}]$ with $V\ge2$, whose variables $X_0$ and $X_1$ are the program
input and the packed input, and let $e_0\in\mathbb N$. Put $T_0=X_5$, $T_1=X_6$, $T_2=X_7$,
$T_3=X_8$ and $T_4=X_4$. The *five-input specialization*
$\operatorname{Spec}(H,e_0)\in\mathbb Z[X_0,\dots,X_{V+6}]$ is
$$\operatorname{Spec}(H,e_0)=H\bigl(e_0,\,X_5,\,X_9,X_{10},\dots,X_{V+6}\bigr)^2
+\sum_{i=0}^{3}\Bigl(2T_i-\bigl((X_i+T_{i+1})(X_i+T_{i+1}+1)+2T_{i+1}\bigr)\Bigr)^2 :$$
the program input is fixed to $e_0$, the old packed input becomes $X_5$, every old variable
$X_i$ with $i\ge2$ becomes $X_{i+7}$, the variables $X_0,\dots,X_4$ are the five new inputs and
$X_5,\dots,X_8$ are the four pairing variables, disjoint from the inputs.

At the level of circuits, the specialization of a natural circuit for $H$ (with call blocks)
replaces its variable node $0$ by the constant $e_0$ and its variable node $1$ by
$\mathrm{var}\ 5$, shifts every other variable index and every private-block start by $7$, declares
the explicit variables $0,\dots,4$ (inputs), $5,\dots,8$ and the shifted old witnesses, and
appends the nodes of the four pairing differences, their squares and the final sum with the
square of the old root. Its polynomial is $\operatorname{Spec}(H,e_0)$.

Applied to the universal halting polynomial (the compilation of the universal interpreter,
with $V=1305804$) and $e_0=c_3$, it gives the natural precision polynomial $C$, with
$V+7=1305811$ variables. This is a definition.

## Depends on

- [Translation of a natural circuit into a model-evaluation recipe](../../../syntax/recipes/model-evaluation-translation.md)

## Sources

- [Section 10.3 specialization](../../../../sources/compiler-translation-locators.md#section-103-specialization)
- [Section 10.1 Cantor wrapper](../../../../sources/compiler-translation-locators.md#section-101-cantor-wrapper-and-acceptance)
- [Translation artifacts](../../../../sources/compiler-translation-locators.md#translation-artifacts)
