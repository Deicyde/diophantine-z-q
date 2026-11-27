---
article_id: af_5d682daa8ef5fac275ff2a7d
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves83.projectiveFalseEllipticCurve
---

# False elliptic curves over a projective base are projective

Let $X$ be a scheme over $\mathbb Z[1/30]$ with a closed immersion into some
$\mathbb P^N_{\mathbb Z[1/30]}$ over $\mathbb Z[1/30]$, and $\mathcal A$ an abelian scheme of
relative dimension $2$ over $X$ with a ring homomorphism
$\mathcal O\to\operatorname{End}_X(\mathcal A)$. Then $\mathcal A$ has a closed immersion into some
$\mathbb P^{N'}_{\mathbb Z[1/30]}$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. A consequence of printed statements, not a single
print, and weaker than what they give: the closed immersion is not asked to lie over
$\mathbb Z[1/30]$. Buzzard's canonical principal polarization $\lambda$ of $\mathcal A$ is read in
Milne's sense, as $\varphi_L$ with $L$ ample at every geometric point; Buzzard does not define a
polarization over a base. It is symmetric by Lan's Lemma 1.3.2.16 and rigidity on the connected
components of the noetherian $X$, so it is a polarization in Lan's sense, and
$(\mathrm{Id},\lambda)^*\mathcal P$ is relatively ample over $X$ (Lan, Proposition 1.3.2.18). Since
$\mathcal O_X(1)$ is ample, twisting by a power of its pull-back gives a sheaf ample relative to
$\mathbb Z[1/30]$, and a proper scheme over an affine base with a relatively ample sheaf has a
closed immersion into projective space (Stacks Project). The symmetry step is written out in the
notes accompanying the Lean proof. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [False elliptic curves are projective](../../../sources/height-decomposition-locators.md#false-elliptic-curves-are-projective)
