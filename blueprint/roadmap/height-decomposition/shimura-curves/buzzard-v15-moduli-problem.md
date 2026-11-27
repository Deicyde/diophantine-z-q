---
article_id: af_7de3b9de810a60c7eab687c0
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves83.buzzardXDV15Lit
---

# Buzzard's moduli problem at level V₁(5) is a projective curve over ℤ[1/30]

Fix the isomorphism $\kappa:\mathcal O/5\mathcal O\to\mathrm M_2(\mathbb F_5)$ sending the classes
of $e=3+2ij$, $X$, $Y$, $1-e$ to the four matrix units, and let
$H\subset(\mathcal O/5\mathcal O)^\times$ be the group of units $\delta$ with
$\kappa(\delta)=\left(\begin{smallmatrix}a&b\\0&1\end{smallmatrix}\right)$. For a scheme $S$ over
$\mathbb Z[1/30]$ and an abelian scheme $\mathcal A$ of relative dimension $2$ over $S$ with a ring
homomorphism $\iota:\mathcal O\to\operatorname{End}_S(\mathcal A)$, a *full level-$5$ structure*
over an $S$-scheme $T$ is an isomorphism of $T$-schemes
$(\mathcal O/5\mathcal O)_T\to\mathcal A[5]_T$ commuting with the left actions of $\mathcal O$;
$\delta$ acts by $\alpha\mapsto\alpha\circ r_\delta$; and a *level-$V_1(5)$ structure* on
$\mathcal A$ is a section over $S$ of the étale sheafification, on $S$-schemes, of
$T\mapsto H\backslash\{\text{full level-5 structures over }T\}$. There are a scheme $X$ over
$\mathbb Z[1/30]$, proper and smooth of relative dimension $1$, with a closed immersion into some
$\mathbb P^N_{\mathbb Z[1/30]}$ over $\mathbb Z[1/30]$, and such an $(\mathcal A,\iota)$ over $X$
with a level-$V_1(5)$ structure, such that for every scheme $S$ over $\mathbb Z[1/30]$ and every
such $(\mathcal A',\iota')$ over $S$ with a level-$V_1(5)$ structure there is exactly one $g:S\to X$
over which $(\mathcal A',\iota')$ maps to $(\mathcal A,\iota)$ (a cartesian square commuting with
$\mathcal O$ and carrying the one level structure to the other), and that map is unique.

It is a published statement: the printed theorem, or a direct instance of it that needs no argument.
Its reading against the print or its review is not complete, and until both are the project's strict
count does not count it as published. It is Buzzard's Theorem 2.1 with Corollary 2.3 at the level
$U=V_1(5)$, for which $\mathbb Z[1/M_Ud]=\mathbb Z[1/30]$, with his own definitions of level
structures (Definitions 1.1 and 1.2) and of the morphisms of $X^D(U)$. Buzzard fixes $\kappa$ once
and for all; every isomorphism $\mathcal O/5\mathcal O\cong\mathrm M_2(\mathbb F_5)$ is the
reduction of an admissible one, so his results hold for the $\kappa$ above. "Algebraic stack" and
"regular" are dropped, and projectivity over the affine base is stated as the closed immersion (EGA
II (5.5.4)(ii)). Buzzard asks that $\mathcal A'\to\mathcal A_S$ be an isomorphism compatible with
$\iota$; the statement asks for a cartesian square commuting with $\mathcal O$, which carries zero
to zero and so is a homomorphism (Milne, Corollary 20.2(a)). Over the empty base, which Buzzard's
injectivity of $\iota$ excludes, every clause holds trivially. The concrete form of level-$V_1(5)$
structures used elsewhere in the proof (a section $Q$ with $5Q=0$ and $\iota(e)Q=0$, nonzero at
every geometric point) is derived from this one in the Lean proof, with Milne's Proposition 20.7 and
Remark 8.4 at $n=5$. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Buzzard Thm 2.1 and Cor 2.3 at V1(5), literal](../../../sources/height-decomposition-locators.md#buzzard-thm-21-and-cor-23-at-v15-literal)
