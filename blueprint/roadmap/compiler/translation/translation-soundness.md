---
article_id: af_a4a51f1480d6d4e45b1adbe5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Translation.translate_sound
---

# Every node point is the code of the node's value

Assume the multiplication statement M in its all-input form.
Let $\mathcal N$ be a natural circuit with $k$ inputs that is well-formed with some bound, with
power template $\mathcal P$ if it has call nodes, and let $\rho$ be its translation in some mode,
with or without natural constraints on the inputs, with power recipe $\pi$ if $\mathcal N$ has call
nodes. If $\mathcal N$ has call nodes, assume that $\pi$ computes the power template on canonical
codes:
$$(\mathrm{PV})\qquad\mathrm{Rel}_\pi(\iota(a),\iota(b),\iota(c),r)\iff\exists\,w\in\mathbb N^{V_{\mathcal P}-3}:\ r=\iota\bigl(T_{\mathcal P}(a,b,c,w)\bigr)\qquad(a,b,c\in\mathbb Z,\ r\in\mathbb Q^5).$$
Let $x:\mathbb N\to\mathbb Q$ satisfy conditions 1-4 of the relational form of $\rho$ (all
conditions except the root equality), and assume that either the inputs carry natural
constraints, or the input points are canonical: $\mathrm{ref}(5i)(x)=\iota(c_i)$ with
$c_i\in\mathbb Z$ for $i<k$.

Then there is an assignment $\theta$, admissible for $\mathcal N$, such that

1. $\mathrm{ref}(5i)(x)=\iota(\theta_i)$ for every input $i<k$, with $\theta_i\in\mathbb N$ when the
   inputs carry natural constraints and $\theta_i=c_i$ otherwise;
2. $\mathrm{ref}(r_v)(x)=\iota(\theta_v)$ for every explicit variable $v$ with point $r_v$;
3. $\mathrm{ref}(\mathrm{pt}(j))(x)=\iota(\mathrm{val}_\theta(j))$ for every node $j$.

In particular the point of the root is $\iota(\mathcal N(\theta))$; if moreover the root
equality of zero mode holds then $\mathcal N(\theta)=0$, and in value mode the output point
$\mathrm{ref}(5k)(x)$ is $\iota(\mathcal N(\theta))$.

**Proof sketch.** Inputs and explicit witnesses: a row with a natural start gives
$\mathrm{Rel}_{\mathtt{natural}}(\mathrm{ref}(r_v)(x))$, hence $\mathrm{ref}(r_v)(x)=\iota(n_v)$ with
$n_v\in\mathbb N$ by the natural-code predicate; put $\theta_v=n_v$. Unconstrained inputs are
canonical by hypothesis; put $\theta_i=c_i$. Nodes: induction along the node list, defining
$\theta$ on the block of each call node when that node is reached.

- $\mathrm{var}\ i$: $\mathrm{pt}=r_i$ and item 2 applies (well-formedness 3).
- $\mathrm{const}\ 0,1,-1$: the references $-1,-2,-3$ have values $\iota(0),\iota(1),\iota(-1)$ by
  the generator equations.
- $\mathrm{const}\ c$ with $c\ge2$: its point is the point $r$ of the constant definition made at
  the first occurrence of $c$; the scalar template $S_h$ has $\mathrm{val}=c\ge1$ and
  $\mathrm{Rel}_{S_h}(\iota(1),\mathrm{ref}(r)(x))$, so $\mathrm{ref}(r)(x)=\iota(c\cdot1)$ by the semantics of
  the fixed-scalar templates (here $\iota(1)$ is the code of $P_0\in2E(K_0)$).
- $\mathrm{add}\ j_1\ j_2$: by induction the operand points are $\iota(\mathrm{val}(j_1))$ and
  $\iota(\mathrm{val}(j_2))$, canonical codes, so the raw-addition contract gives
  $\iota(\mathrm{val}(j_1)+\mathrm{val}(j_2))$.
- $\mathrm{mul}\ j_1\ j_2$: M gives $\iota(a)=\iota(\mathrm{val}(j_1))$, $\iota(b)=\iota(\mathrm{val}(j_2))$ and
  output $\iota(ab)$; injectivity of $\iota$ gives $\iota(\mathrm{val}(j_1)\mathrm{val}(j_2))$.
- $\mathrm{call}\ (a,b,c)\ w$: the three argument points are canonical by induction, so (PV)
  gives $w'\in\mathbb N^{V_{\mathcal P}-3}$ with output $\iota(T_{\mathcal P}(\mathrm{val}(a),\mathrm{val}(b),\mathrm{val}(c),w'))$;
  set $\theta$ to $w'$ on the block of this call. By well-formedness 5 this block is used by no
  other call and by no explicit variable, and the values of earlier nodes do not depend on
  it, so the definition is consistent and keeps items 1-3 for earlier nodes.

The root equality of zero mode says that the root point equals $\mathrm{ref}(-1)(x)=\iota(0)$, so
$\iota(\mathcal N(\theta))=\iota(0)$ and $\mathcal N(\theta)=0$ by injectivity of $\iota$. Raw addition
only ever receives canonical codes here: this is the induction order of the manuscript's
typing argument, and the natural guards constrain the explicit variables only, never
intermediate sums or products, whose values may be negative.

## Depends on

- [Values and polynomial of a natural circuit](natural-circuit-values.md)
- [Well-formed natural circuits](natural-circuit-well-formed.md)
- [Relational form of a model-evaluation recipe](model-recipe-relation.md)
- [Correctness of the multiplication template](../../multiplication/multiplication-template.md)

## Proof depends on

- [The natural-code predicate](natural-code-semantics.md)
- [Semantics of the fixed-scalar templates](../../syntax/fixed-scalar-semantics.md)
- [Raw addition](../../model/raw-addition.md)
- [The generator certificate](../../model/generator.md)
- [Values of the point references](../../syntax/language/generator-references.md)
- [Mordell-Weil for $E/K_0$ from the descent](../../model/descent/mordell-weil-from-descent.md)

## Sources

- [Section 10.4](../../../sources/compiler-translation-locators.md#section-104-typing-order)
- [Section 10.4 parent](../../../sources/compiler-translation-locators.md#section-104-power-value-and-precision-parent)
