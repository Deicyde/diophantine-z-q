---
article_id: af_e0dd7e7ad58e00d84c192c48
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenAddedLeaves17.phiAmpleIsogeny
---

# The polarization of an ample line bundle is an isogeny

The *polarization statement* is the following assertion. Let $A$ be an abelian variety over a field
$K$ and $L$ an ample line bundle on $A$. Then the morphism
$\lambda_L:A\to\operatorname{Pic}^0_{A/K}$, $x\mapsto t_x^*L\otimes L^{-1}$, is finite and
surjective.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. Mumford's theorems are stated over an algebraically
closed field and about points; reaching the statement needs Mumford's dual identified with
$\operatorname{Pic}^0_{A/K}$, fpqc descent from the algebraic closure (EGA IV 2.7.1), that a proper
quasi-finite morphism is finite, and the passage from effective divisors to an arbitrary ample $L$.
It is a hypothesis, not proved here.

## Depends on

- [The identity component of the Picard scheme is an abelian variety](identity-component-of-picard.md)

## Sources

- [Polarization isogeny](../../../sources/height-decomposition-locators.md#polarization-isogeny)
