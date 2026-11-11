---
article_id: af_3033098b737610d3d47b7757
---

# Assembly and the ordinary-value relation

This chapter proves that the rational zero projection of the specified polynomial $P_*$ is
exactly $\mathbb Z$, and assembles the target statement. It follows Section 11 of the
manuscript (the variable-shift relation for ordinary values) and Lemma 1.2 (assembly).

The polynomial never sees an integer directly. A rational input $t$ comes with a code
$N\in\mathbb Q^5$, which membership types as $N=\iota(n)$ for an integer index $n$; the value
relation must then force $t=n$. The point coordinates and the integer index play distinct
roles throughout: the index is what the precision computation and the height estimate
reason about, the coordinates are what the polynomial sees. For the six contact values
$n\in\mathcal C=\{0,-15,-20,-24,-30,-60\}$ an exceptional branch states $t=n$ outright. For
every other $n$, the main branch chooses one shift $\kappa\ne0$, a five-coordinate code shared by
two relations: Close, which says that $t$ lies within $e^{-B(n,\kappa)}$ of $n$ with
$B(n,\kappa)=H_6(S_{\rm ht})|\kappa F(n)|^{24}$, and Test, which through the height estimate bounds
$h(t)\le B(n,\kappa)$. A rational number of height at most $B$ that is so close to an integer
is that integer.

The constants $D$, $H_6(S_{\rm ht})$ and $B(n,\kappa)$ are astronomically large. Every argument
here treats them symbolically through their defining expressions; none is ever evaluated.

## The value templates

The specification chapter defines the five templates of the value relation; their meaning
is proved first. It rests on the elliptic model (input G: membership types arbitrary
inputs, raw addition is the group law on canonical codes) and on multiplication (input M).

- [The value templates and their relations](value-templates/README.md)

## Approximation for every fixed shift

The relation Close links the five signed codes $N,\mathcal K,A,L,J$ to the inputs of the
compiled precision relation (input C) and imposes the coordinate window $|t-r(a,j)|<\epsilon_l$.
It is sound, $|t-n|<e^{-B(n,\kappa)}$, and complete for every fixed nonzero shift, because
positive multiples of $P_0$ approach the identity at both real places and the derivative of
$[n]$ at the identity is $n$.

- [Approximation for every fixed shift](approximation/README.md)

## The six local tests

The relation Test forms six field-valued tests from the shift, puts them over one common
denominator $F(t)$ into one product $W$, one trace $\Theta$ and one instance $\Phi(R/\Theta^2)$ of the
pole predicate. Soundness (Lemma 11.1) uses the pole obstruction and the formal groups at
the primes above each contact prime to show $M_{S_{\rm ht}}(t)\mid\kappa F(n)$. Completeness
(Lemma 11.2) chooses $\kappa$ deep in the formal groups above the primes of
$2730^6F(n)$ and applies pole completeness (PC).

- [The six local tests](local-tests/README.md)

## Exact ordinary value

In an accepting main branch, the divisibility lemma and the six-contact estimate (H) give
$h(t)\le B(n,\kappa)$, and soundness of Close gives $|t-n|<e^{-B(n,\kappa)}$; a reduced fraction
$a/b\ne n$ has $|t-n|\ge1/b\ge e^{-h(t)}$, so $t=n$.

- [An accepting main branch forces the exact value](main-branch-exactness.md)

Conversely, for $n\notin\mathcal C$ one suitable shift satisfies Test, Close holds for that same
shift, and the two calls have disjoint private witness blocks, so they are satisfied
simultaneously. Hence the value relation is exactly the graph $t=n$, and projecting away the
code gives ordinary $\mathbb Z$ in $\mathbb Q$.

- [The exact ordinary-value relation](ordinary-value-relation.md)

## Assembly

The root recipe squares one call of the value relation with a fresh code, so the rational
zero projection of $P_*$ is the projection of the value relation; with the witness
accounting and the size bounds of the specification and size chapters this proves the
target statement for $P_*$ under the four hypotheses. The main theorem follows directly.

- [The assembly lemma](assembly-lemma.md)
