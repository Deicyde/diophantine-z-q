---
article_id: af_8e6d5ca2a978652497a89785
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.ConstructorBounds, ZInQ.Size.NodeAdmissible, ZInQ.Size.nodes_majorant, ZInQ.Size.library_majorant
---

# Templates satisfy the height majorant

Let $B\ge2^{20}$ and let $L$ be a template library, each call referring to an earlier
template, such that, in every template of $L$:

- every node $\mathrm{const}\ c$ has $|c|\le B-1$;
- every node $\mathrm{fixed}\ e$ has $|\mathrm{val}(e)|\le B-1$;
- every node $\mathrm{psi}\ e\ a\ c$ has $|\mathrm{val}(e)|+1\le B$;
- every node $\mathrm{guard}\ e\ a$ has $0\le\mathrm{val}(e)\le B-1$.

Suppose moreover that the constructors satisfy the uniform bounds at $B$: $\deg\Psi_{n,c}\le B^4$
and $\|\Psi_{n,c}\|_1\le2^{B^8}$ whenever $|n|+1\le B$, and $\deg G_T\le B^4$ and
$\|G_T\|_1\le2^{B^8}$ whenever $0\le T\le B-1$. (The constructors of the specification satisfy
them at every $B\ge2^{20}$.)

Then for every template $\tau$ of $L$ and every node $n_j$ of $\tau$,
$\mathrm{Maj}_B\bigl(h(n_j),[\![n_j]\!]\bigr)$; in particular $\mathrm{Maj}_B\bigl(H(\tau),[\![\tau]\!]\bigr)$.

**Proof sketch.** Induction over the library in stored order and, within a template, over
the nodes in stored order. Variables: rule (0). Constants and fixed nodes: rule (0), since
$|c|\le B\le2^{B^8}$. Additions and multiplications: rule (1). Constructor nodes: the hypothesis on the
constructors gives $\deg\le B^4$ and $\|\cdot\|_1\le2^{B^8}$ for $\Psi_{\mathrm{val}(e),c}$ and
$G_{\mathrm{val}(e)}$; apply rule (3) with $k$ the maximum argument height. Calls: the call
polynomial is $[\![\tau']\!]$ with parameters replaced by the argument polynomials (height at
most $k=\max(0,\max_ih(n_{a_i}))$) and witnesses by fresh variables (height $0\le k$); the
induction hypothesis for the earlier template $\tau'$ gives $\mathrm{Maj}_B(H(\tau'),[\![\tau']\!])$,
and rule (2) gives $\mathrm{Maj}_B(H(\tau')+k+1,\cdot)$. The values $\mathrm{val}(e)$ enter only through
the four hypotheses and are never computed.

## Depends on

- [Syntax heights](syntax-height.md)
- [Semantics of templates and recipes](../../syntax/template-semantics.md)

## Proof depends on

- [Closure rules for the height majorant](majorant-rules.md)
- [Uniform bounds for the finite constructors](../norms/constructor-bounds.md)

## Sources

- [Section 12.1 syntax heights](../../../sources/size-locators.md#section-121-syntax-heights)
- [Companion size proof](../../../sources/size-locators.md#companion-size-proof)
