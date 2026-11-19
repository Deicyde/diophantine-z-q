---
article_id: af_2f1cfccdb3cd7896e3e972ee
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves67.elliotWildInertiaTrivial
---

# Wild inertia acts trivially under semistable reduction

The *wild inertia statement* is the following assertion. Let $K$ be a number field, $\mathcal O$ a
discrete valuation ring with fraction field $K$, $\Omega$ an algebraic closure of $K$, $w$ a
valuation ring of $\Omega$ over $\mathcal O$, and $\ell$ a prime invertible in $\mathcal O$. Let $A$
be an abelian variety over $K$ with semistable reduction at $\mathcal O$ in the sense of Silverberg
and Zarhin: some Néron model of $A$ over $\mathcal O$ has a special fibre over the residue field
whose identity component is an extension of an abelian variety by a torus, not necessarily split.
Then every element $\sigma$ of $\operatorname{Gal}(\Omega/K)$ in the inertia group of $w$ that is
wild, in the sense that $v_w(\sigma x-x)>v_w(x)$ for every nonzero $x\in\Omega$, where $v_w$ is the
valuation of $w$, acts trivially on $T_\ell A=\varprojlim_n A(\Omega)[\ell^n]$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. This is a sentence of the manuscript, which cites
nothing for it. At a prime $p$, once Raynaud's criterion gives semistable reduction over the local
field $F$ obtained from the completion by adjoining the $3$-torsion of $A$ (the $5$-torsion if
$p=3$), the manuscript says: "Its wild inertia acts trivially on each $V_\ell(A)$ with $\ell\ne p$."
The statement reads this at a finite place of a number field, through two standard identifications
(the decomposition group of $w$ is the Galois group of the completion, and Néron models commute with
completion), and on $T_\ell A$, which embeds in $V_\ell(A)$. It is true and standard: under
semistable reduction inertia acts unipotently on $T_\ell A$ (SGA 7 I, Exposé IX, Proposition 3.5),
and wild inertia is pro-$p$, so it acts on each $A(\Omega)[\ell^n]$ with period prime to $\ell$. An
argument given here derives the statement from these two facts, neither of which is proved here. It
is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Wild inertia on Tate modules](../../../sources/height-decomposition-locators.md#wild-inertia-on-tate-modules)
