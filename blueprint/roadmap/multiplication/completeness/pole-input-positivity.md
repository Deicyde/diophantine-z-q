---
article_id: af_3d5bc95620f4cbe105bdc460
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.pole_input_small
---

# Positivity and smallness of the pole input

Let $R_0\in\mathbb Q$ with $R_0>0$, $\ell\in\mathbb Q\setminus\{0\}$, and fix $C_{gj}\in K_0$
($1\le g\le6$, $1\le j\le12$). There is a real $\varepsilon>0$ such that for every
$a\in\mathbb Q$ with $0<|a|<\varepsilon$, putting $R=\ell^2a^2R_0$,
$W_g=\prod_{j=1}^{12}(1+RC_{gj}^2)$ and $\Theta=\operatorname{Tr}\sum_gW_g^{-1}$:

1. both real embeddings of every $W_g$ are at least $1$; in particular $W_g\ne0$;
2. $0<\Theta\le12$;
3. $0<R/\Theta^2<1/2$.

This makes precise the manuscript's "as $a\to0$, $W_g\to1$, $\Theta\to12$, and
$R/\Theta^2\to0$ through positive values". The $C_{gj}$ do not depend on $q$, so $\varepsilon$
can be fixed before $q$ is chosen.

**Proof sketch.** $R>0$, and $\sigma_\pm(1+RC^2)=1+R\,\sigma_\pm(C)^2\ge1$, so
$\sigma_\pm(W_g)\ge1$ and $\sigma_\pm(W_g^{-1})\in(0,1]$. Since
$\operatorname{Tr}=\sigma_++\sigma_-$, $\Theta$ is a sum of twelve numbers in $(0,1]$. Let $K$ be
the maximum of $1$ and all $\sigma_\pm(C_{gj})^2$. Then $\sigma_\pm(W_g)\le(1+RK)^{12}$, so
$\Theta\ge12(1+RK)^{-12}$ and $R/\Theta^2\le R(1+RK)^{24}/144$. If $RK\le1$ this is at most
$2^{24}R/144$, which is below $1/2$ when $R<72\cdot2^{-24}$. Choose $\varepsilon$ with
$\ell^2\varepsilon^2R_0<\min(1/K,\,72\cdot2^{-24})$.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../../model/field/quadratic-field.md)

## Sources

- [Pole input of a completed slope](../../../sources/multiplication-locators.md#pole-input-of-a-completed-slope)
