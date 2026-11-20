---
article_id: af_52f83cb7f78009bae0bddab3
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves72.cmjDegreePrint
---

# The degree of a singular modulus

The *degree statement* is the following assertion. Let $\tau$ be a point of the upper half-plane
satisfying $a\tau^2+b\tau+c=0$ with $a,b,c\in\mathbb Z$, $a>0$ and $\gcd(a,b,c)=1$, put
$\Delta=b^2-4ac$, and let $x=j(\tau)$ be the corresponding singular modulus. Then for every order
$R$ of an imaginary quadratic field with discriminant $\Delta$,
$[\mathbb Q(x):\mathbb Q]=\#\operatorname{Pic}(R)$, the class number of $R$.

It is a published statement: the printed theorem, or a direct instance of it that needs no argument.
This is the equality over $\mathbb Q$ in a sentence of Fowler's §2.1, which he derives from Cox
(Theorem 11.1 and Proposition 13.2): for a singular modulus of discriminant $\Delta$,
$[\mathbb Q(x):\mathbb Q]=h(\Delta)$, the class number of the imaginary quadratic order of
discriminant $\Delta$. The discriminant is the one of his form definition. The order of discriminant
$\Delta$ is a parameter here; Lean proves that it is unique up to isomorphism and that its class
number does not depend on the choice. The manuscript uses the fact without a citation ("The degree
of $j(E)$ is its order class number, so $h(\Delta)\le d\le D$"), and Lean derives from this
statement the bound it needs: an elliptic curve over a number field $L$ with complex multiplication
by $R$ has $\#\operatorname{Pic}(R)\le[L:\mathbb Q]$. A person's reading of the publisher's PDF,
recorded as a human reading, compared the sentence with the print. A two-lens review rated the
statement published in its printed form. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Degree of singular moduli](../../../sources/height-decomposition-locators.md#degree-of-singular-moduli)
