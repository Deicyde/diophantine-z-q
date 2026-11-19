---
declaration: theorem
origin: cited
---

# Evaluation and the outer valuation ring (5.2), (5.3)

For the retained global models and for the primitive and derivative Selmer models, evaluation of cochain
maps at sequences $g=(g_i)$, $h=(h_i)$ of Galois elements satisfies
$$e^1_gd=(\rho(g)-1)e^0,\qquad e^2_{g,h}d=\rho(g)e^1_h-e^1_{gh}+e^1_g.\tag{5.2}$$
A cycle defines an abstract crossed homomorphism of the product group; the induced map on $H^1$ is injective,
and a finite detecting list of evaluations stays injective after field extension.

For a sequence of ring instances with $\omega(k_j)\le A$ and a fixed number of derivative labels, the quotient
$$\mathscr O_\infty=\Bigl(\prod_{\mathcal U}\mathscr O_j\Bigr)\Big/\{(x_j):v_2(x_j)\to_{\mathcal U}\infty\}\tag{5.3}$$
is a discrete valuation ring with uniformizer $2$ and fraction field of characteristic zero. The bounded
minimal-model matrices, evaluations, duality maps and homotopies pass to it, and sequences whose differentials
tend to zero give crossed homomorphisms there. Neither continuity on one Galois group nor completeness of
$\mathscr O_\infty$ is needed.

**Proof sketch.** One fixed ultrafilter supplies (5.2) for all sequences. At each finite stage the
evaluations $(c,w)\mapsto b_c(g)-(\rho(g)-1)w$ have common kernel $(0,W^\Gamma)$, already attained by a finite
list of at most $\dim V+\dim W$ evaluations, chosen and padded before the limit. In (5.3), a nonzero element
has one fixed valuation on a set in $\mathcal U$ and is that power of two times a unit; every nonzero ideal
has an element of least valuation and is principal. The bound (5.1) keeps the model sizes bounded along the
sequence.

## Depends on

- [The reduced generic residual rank bound (5.1)](residual-bound.md)

## Proof depends on

- [Finite free models and the inner limit](inner-limit.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:limits-outer-evaluation` (L4650–4746)

## Manuscript check

Mapped by AI review. Its use in the proof of (5.5) was checked line by line; the proof of the lemma itself is
not yet checked line by line.
