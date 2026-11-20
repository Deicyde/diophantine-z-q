---
article_id: af_e630dc970208f2ef80403e45
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves73.silverbergZarhinThm33
---

# Silverberg and Zarhin's inertia criterion for semistable reduction

The *inertia criterion statement* is the following assertion. Let $K$ be a field, $\mathcal O$ a
valuation ring of $K$ that is a discrete valuation ring, $\Omega$ an algebraic closure of $K$, $w$ a
valuation ring of $\Omega$ over $\mathcal O$, $\ell$ a prime invertible in $\mathcal O$, and $A$ an
abelian variety over $K$, with $V_\ell A=\mathbb Q_\ell\otimes_{\mathbb Z_\ell}T_\ell A$. Say that
an abelian variety has semistable reduction at a discrete valuation ring when some Néron model of it
there has a special fibre over the residue field whose identity component is an extension of an
abelian variety by a torus, not necessarily split. Suppose that $A$ has semistable reduction at
$\mathcal O$, or that for some finite separable extension $E$ of $K$ inside $\Omega$ such that
$w\cap E$ is a discrete valuation ring, $A_E$ has semistable reduction at $w\cap E$. Then $A$ has
semistable reduction at $\mathcal O$ if and only if the inertia group $I$ of $w$ acts trivially on
$V_\ell A/(V_\ell A)^I$: that is, $\tau(\sigma x-x)=\sigma x-x$ for all $\sigma,\tau\in I$ and all
$x\in V_\ell A$.

It is a published theorem, but a review rated the form stated here glue rather than the printed
form, so the project's strict count does not count it as published. It is Theorem 3.3 of Silverberg
and Zarhin, which they attribute to Grothendieck, for the print's Galois extension taken to be the
separable closure, as their proofs of Lemma 5.5 and Proposition 6.1 take it; the algebraic closure
$\Omega$ stands in for the separable closure. The print defines semistability at a place only for a
discrete valuation, so for the infinite extension "semistable at $w$" is read as semistable at some
finite separable subextension, the base allowed: that is the hypothesis above. A two-lens review
rated the statement glue rather than the printed form, for these readings and because $K$ is any
field; a page reading alone would not change that. The manuscript cites Theorem 3.5 of the same
paper (Raynaud's criterion) and then states, without citation, that wild inertia acts trivially on
each $V_\ell(A)$ with $\ell\ne p$. Lean derives that sentence from this statement. It is a
hypothesis, not proved here.

## Depends on

None.

## Sources

- [Inertia criterion](../../../sources/height-decomposition-locators.md#inertia-criterion)
