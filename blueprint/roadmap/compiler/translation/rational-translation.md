---
article_id: af_d7f5e2cab732cc7355890543
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Translation.precision_rel_iff, ZInQ.Translation.precision_rel_iff_accepts_of
---

# Semantics of the rational translation

Assume the multiplication statement M in its
all-input form: $\mathrm{Rel}_{\mathtt{multiply}}(p,q,r)\iff\exists a,b\in\mathbb Z,\ p=\iota(a),\ q=\iota(b),\
r=\iota(ab)$ for all $p,q,r\in\mathbb Q^5$. Let $C\in\mathbb Z[X_0,\dots,X_{1305810}]$ be the natural
precision polynomial, with inputs $X_0,\dots,X_4$ in the order $(n,\kappa,a,l,j)$. Then for all
$E_0,\dots,E_4\in\mathbb Q^5$ (arbitrary rational $5$-tuples),
$$\mathrm{Rel}_{\mathtt{precision}}(E_0,\dots,E_4)\iff
\exists\,\mathbf c\in\mathbb N^5:\ E_i=\iota(c_i)\ (0\le i\le4)\ \text{and}\
\exists\,\mathbf z\in\mathbb N^{1305806}:\ C(\mathbf c,\mathbf z)=0 .$$

Thus the precision recipe has rational witnesses exactly at the codes
$\iota(c_0),\dots,\iota(c_4)$ of natural numbers $c_0,\dots,c_4$ at which the natural
polynomial has a natural zero. Together with equation (C.4) this is input C of the assembly
lemma. The multiplication statement holds under the six-contact estimate, pole completeness
and the twenty-two-prime pattern by the multiplication chapter.

**Proof sketch.** The semantics of the power-value recipe is the (PV) property of the power
recipe used by $\mathtt{precision}$. The precision recipe is the translation of the
natural precision circuit $\mathcal N$ in zero mode with natural constraints on its five inputs,
and $\mathcal N$ is well-formed with bound $1305811$. Case 1 of the semantics of the
model-evaluation translation gives: $\mathrm{Rel}_{\mathtt{precision}}(E)$ iff $E_i=\iota(\theta_i)$ and
$\mathcal N(\theta)=0$ for some $\theta$ admissible for $\mathcal N$ with $\theta_0,\dots,\theta_4\in\mathbb N$.
Every explicit variable and every block variable of $\mathcal N$ is below $1305811$, so
$\mathcal N(\theta)=C(\theta_0,\dots,\theta_{1305810})$. Given such $\theta$, put $c_i=\theta_i$ and let
$z_v=\theta_v$ when $v$ is an explicit witness or a block variable, $z_v=0$ otherwise; then
$\mathbf z\in\mathbb N^{1305806}$ and $C(\mathbf c,\mathbf z)=\mathcal N(\theta)=0$. Conversely
$\theta=(\mathbf c,\mathbf z,0,0,\dots)$ is admissible. Replacing each private block of the parent by
its private power-value call therefore preserves the full existential assignment, and only
the final root is equated to the identity.

## Depends on

- [The precision recipe](../../syntax/recipes/recipe-precision.md)
- [The power-value recipe](../../syntax/recipes/recipe-power-value.md)
- [Semantics of the natural precision polynomial](../natural/natural-polynomial-semantics.md)
- [Values and polynomial of a natural circuit](natural-circuit-values.md)
- [Point codes](../../model/point-codes.md)
- [Correctness of the multiplication template](../../multiplication/multiplication-template.md)

## Proof depends on

- [Semantics of the power-value recipe](power-value-semantics.md)
- [Semantics of the model-evaluation translation](model-evaluation-semantics.md)
- [Scope conditions of the natural precision circuit](precision-circuit-scope.md)

## Sources

- [Input C](../../../sources/compiler-translation-locators.md#input-c)
- [Section 10.4 typing order](../../../sources/compiler-translation-locators.md#section-104-typing-order)
- [Section 10.4 power value and precision parent](../../../sources/compiler-translation-locators.md#section-104-power-value-and-precision-parent)
- [Section 10.4 primitive formulas](../../../sources/compiler-translation-locators.md#section-104-primitive-formulas)
