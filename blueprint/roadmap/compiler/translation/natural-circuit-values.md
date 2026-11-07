---
article_id: af_73174e996cbbf8d67ed04a5e
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.Translation.nodeVal, ZInQ.Translation.circuitValue, ZInQ.Translation.templateValue, ZInQ.Translation.callValue, ZInQ.Translation.circuitPoly, ZInQ.Translation.Admissible, ZInQ.Translation.circuitValue_eq_eval_poly
---

# Values and polynomial of a natural circuit

Let $\mathcal N$ be a natural circuit with $k$ inputs, in the format of the model-evaluation
translation, and let $\mathcal P$ be a natural circuit with $3$ inputs and no call nodes (the
power template). Write $V_{\mathcal P}$ for the number of variables of $\mathcal P$
($V_{\mathcal P}=82$ for the power template, so its call blocks have $79$ variables).

**Values of the power template.** For $y:\mathbb N\to\mathbb Z$ the value $\mathrm{val}^{\mathcal P}_y(j)$
of node $j$ of $\mathcal P$ is defined in node order by
$\mathrm{val}(\mathrm{const}\ c)=c$, $\mathrm{val}(\mathrm{var}\ i)=y_i$,
$\mathrm{val}(\mathrm{add}\ j\ j')=\mathrm{val}(j)+\mathrm{val}(j')$ and
$\mathrm{val}(\mathrm{mul}\ j\ j')=\mathrm{val}(j)\,\mathrm{val}(j')$. Put
$$T_{\mathcal P}(y_0,\dots,y_{V_{\mathcal P}-1})=\mathrm{val}^{\mathcal P}_y(\mathrm{root}_{\mathcal P}).$$

**Values of the circuit.** For $\theta:\mathbb N\to\mathbb Z$ the value $\mathrm{val}_\theta(j)$ of node
$j$ of $\mathcal N$ is defined in node order by the same four rules and, for a call node
$\mathrm{call}\ (a,b,c)\ w$,
$$\mathrm{val}_\theta(\mathrm{call}\ (a,b,c)\ w)=T_{\mathcal P}\bigl(\mathrm{val}_\theta(a),\mathrm{val}_\theta(b),\mathrm{val}_\theta(c),\theta_w,\theta_{w+1},\dots,\theta_{w+V_{\mathcal P}-4}\bigr).$$
The value of the circuit is $\mathcal N(\theta)=\mathrm{val}_\theta(\mathrm{root})$.

**Polynomial.** $[\![\mathcal N]\!]$ is the polynomial of the natural circuit defined in the natural
chapter: the same recursion with polynomial operations, a call node denoting the substitution
of the argument polynomials and the block variables $X_{w+i}$ into the polynomial of $\mathcal P$.
Since evaluation commutes with substitution, $\mathcal N(\theta)=[\![\mathcal N]\!](\theta)$ for every
$\theta$. For the natural precision circuit,
$[\![\mathcal N]\!]$ is the natural precision polynomial $C$ of equation (C.4); its variables are
$X_0,\dots,X_{1305810}$ and $X_0,\dots,X_4$ are the inputs.

**Admissible assignments.** $\theta$ is *admissible* for $\mathcal N$ when $\theta_v\in\mathbb N$ for every
explicit variable $v$ of kind witness and for every variable $v$ of the block
$[w,w+V_{\mathcal P}-3)$ of every call node. Inputs are not constrained by admissibility.

A call node contributes the *value* of the power template at its arguments and its block;
it does not assert that this value vanishes. This is a definition.

## Depends on

- [Translation of a natural circuit into a model-evaluation recipe](../../syntax/recipes/model-evaluation-translation.md)
- [Natural semantics of a natural circuit](../natural/formulas/natural-circuit-semantics.md)

## Sources

- [Section 10.4](../../../sources/compiler-translation-locators.md#section-104-power-value-and-precision-parent)
- [Section 10.3](../../../sources/compiler-translation-locators.md#section-103-specialization)
- [Translation artifacts](../../../sources/compiler-translation-locators.md#translation-artifacts)
