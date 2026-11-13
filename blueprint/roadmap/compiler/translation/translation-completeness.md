---
article_id: af_a670c1d34c64ea00736b9abb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Translation.translate_complete
---

# Natural solutions give rational witnesses

Assume the multiplication statement M in its all-input form.
Let $\mathcal N$, $\mathcal P$, $\rho$ and $\pi$ be as in the soundness statement, with (PV) for $\pi$ if
$\mathcal N$ has call nodes. Let $\theta$ be admissible for $\mathcal N$, with $\theta_i\in\mathbb N$ for
every input $i<k$ if the inputs carry natural constraints. Then the assignment $x$ defined by

- $\mathrm{ref}(5i)(x)=\iota(\theta_i)$ for the inputs $i<k$, and in value mode
  $\mathrm{ref}(5k)(x)=\iota(\mathcal N(\theta))$;
- $x_{g_0}=1641/8$, $x_{g_1}=-15465/4$, $x_{g_2}=87483/32$;
- $\mathrm{ref}(r_v)(x)=\iota(\theta_v)$ for the fresh point $r_v$ of every explicit witness
  variable $v$;
- $\mathrm{ref}(\mathrm{pt}(j))(x)=\iota(\mathrm{val}_\theta(j))$ for every node $j$ whose point is fresh
  (a constant node at the first occurrence of its value, an addition, multiplication or call
  node);
- $0$ elsewhere,

is well defined and satisfies conditions 1-4 of the relational form of $\rho$, and also the
root equality in value mode, and in zero mode whenever $\mathcal N(\theta)=0$. Consequently, in
zero mode with $\mathcal N(\theta)=0$, $\mathrm{Rel}_\rho(\iota(\theta_0),\dots,\iota(\theta_{k-1}))$ holds,
and in value mode $\mathrm{Rel}_\rho(\iota(\theta_0),\dots,\iota(\theta_{k-1}),\iota(\mathcal N(\theta)))$ holds.

**Proof sketch.** The fresh points of distinct explicit variables and nodes are distinct
allocations, and all occurrences of one nontrivial constant share one point and one value,
so $x$ is well defined; then $\mathrm{ref}(\mathrm{pt}(j))(x)=\iota(\mathrm{val}_\theta(j))$ for every node,
including variable nodes and the constants $0,\pm1$. Each condition holds by the completeness
half of the corresponding statement: the natural rows by the natural-code predicate
($\theta_v\in\mathbb N$ by admissibility, or by hypothesis for inputs); the constant definitions
by the fixed-scalar semantics, $\mathrm{Rel}_{S_h}(\iota(1),\iota(c))$ for $c\ge2$; additions by the
raw-addition contract; multiplications by M; calls by (PV), with the block values
$(\theta_w,\dots,\theta_{w+V_{\mathcal P}-4})\in\mathbb N^{V_{\mathcal P}-3}$ supplied by admissibility. The
root equality is $\iota(\mathcal N(\theta))=\iota(0)=\mathrm{ref}(-1)(x)$ in zero mode and holds by the
choice of the output point in value mode. The relational form then gives $\mathrm{Rel}_\rho$.

## Depends on

- [Every node point is the code of the node's value](translation-soundness.md)
- [Values and polynomial of a natural circuit](natural-circuit-values.md)
- [Relational form of a model-evaluation recipe](model-recipe-relation.md)
- [Correctness of the multiplication template](../../multiplication/multiplication-template.md)

## Proof depends on

- [The natural-code predicate](natural-code-semantics.md)
- [Semantics of the fixed-scalar templates](../../syntax/fixed-scalar-semantics.md)
- [Raw addition](../../model/raw-addition.md)
- [Values of the point references](../../syntax/language/generator-references.md)

## Sources

- [Section 10.4](../../../sources/compiler-translation-locators.md#section-104-typing-order)
- [Section 10.4 parent](../../../sources/compiler-translation-locators.md#section-104-power-value-and-precision-parent)
