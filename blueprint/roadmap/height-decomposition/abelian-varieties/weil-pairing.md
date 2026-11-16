---
article_id: af_5491cca279af0c417f47bc1f
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenAddedLeaves17.weilPairingMumford
---

# The Weil pairing

The *Weil-pairing statement* is the following assertion. Let $A$ be an abelian variety over a field
$K$. Then there is a family of pairings $e_n:A[n]\times\operatorname{Pic}^0_{A/K}[n]\to\mu_n$, one
for each $n\ge1$, such that for every $n$ invertible in $K$: $e_n$ takes the values of Mumford's
pairing $\bar e_n$ and is perfect and Galois-equivariant, it is adjoint for the dual $f^\vee$ of
every endomorphism $f$ of $A$, and it is trivial on the pairs $(x,\lambda_L x)$ for every ample line
bundle $L$; and the family is compatible in $n$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. The printed pairing is on Mumford's dual; reading it on
$\operatorname{Pic}^0_{A/K}$ passes through Kleiman 9.2.5 and Mumford §8 (iv), §8 Theorem 1 and §13,
with base change to an algebraic closure, and the statement also combines several sources (Mumford
§§20 and 23, Milne 1986 §16). The sign convention does not matter. It is a hypothesis, not proved
here.

## Depends on

- [The identity component of the Picard scheme is an abelian variety](identity-component-of-picard.md)
- [The polarization of an ample line bundle is an isogeny](polarization-isogeny.md)

## Sources

- [Weil pairing](../../../sources/height-decomposition-locators.md#weil-pairing)
