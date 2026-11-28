---
article_id: af_3ff1aab671ea18a5f43ec95a
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves87.milneShimuraFamilyPrint
---

# The complex Shimura curve at level three carries its family of QM surfaces

There are a proper smooth curve $T$ over $\mathbb C$, a family of abelian surfaces over $T$ with an
action of $\mathcal O$ and a full level-$3$ structure, and a surjection $\psi$ from
$\mathbb H^\pm\times(B\otimes\mathbb A_f)^\times$ onto $T(\mathbb C)$, holomorphic in the first
variable, whose fibre at $\psi(z,g)$ is the level-$3$ QM surface of $[z,g]$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. It is Milne's construction in the existence proof for
canonical models, in the PEL case: the variation of Hodge structures on each component
$\Gamma_\varepsilon\backslash X^+$ comes from a polarized family of abelian varieties by his Theorem
14.8, which is Deligne's Rappel (4.4.3) in *Théorie de Hodge II*; the quotient is an algebraic curve
by Baily–Borel, here compact since $B$ is a division algebra. It is a consequence of these printed
steps, not a single print: the compactness of the quotients, the absence of torsion at level three,
the action of $\mathcal O$ on the family (from the full faithfulness in 4.4.3), and the level-$3$
sections (from $\Gamma_\varepsilon$ acting trivially on $\Lambda/3\Lambda$, made algebraic by Chow's
theorem) are derived here, not printed; the reduction of every point to a representative $(\tau,u)$
with $u$ a unit is proved in Lean. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Milne 14.8, Deligne Hodge II 4.4.3](../../../sources/height-decomposition-locators.md#milne-148-deligne-hodge-ii-443)
