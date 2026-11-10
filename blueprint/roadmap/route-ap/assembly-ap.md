---
article_id: af_d4c1a20cf6f2ebc52ffb540f
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Assembly.assembly_AP
---

# The assembly lemma under field 2′

Assume the minimal height hypothesis, pole completeness and the slope representation under
field 2′, and the bound on the addition and multiplication nodes of the universal halting circuit.
Then the specified polynomial $P_*$, the same polynomial as in the assembly lemma, witnesses the
target statement: it has $292{,}890{,}231{,}905$ variables, degree below $2\uparrow\uparrow7$,
coefficients below $2\uparrow\uparrow8$, and for every $q\in\mathbb Q$ the equation
$P_*(q,w)=0$ has a rational solution $w$ exactly when $q\in\mathbb Z$.

**Proof sketch.** The proof of the assembly lemma, with the ordinary-value relation under field 2′
in place of the exact ordinary-value relation; the size bounds and the witness accounting do not
involve the slope representation.

## Depends on

- [The target statement](../main/frozen-target.md)
- [The specified polynomial](../syntax/literal-polynomial.md)
- [The minimal height hypothesis](../main/six-contact-min.md)
- [Pole completeness](../main/pole-completeness.md)
- [The slope representation under field 2′](slope-representation-ap.md)
- [Node statistics of the halting circuit and the power template](../compiler/natural/universal/halting-node-check.md)

## Proof depends on

- [The assembly lemma](../assembly/assembly-lemma.md)
- [The ordinary-value relation under field 2′](value-relation-ap.md)

## Sources

- [The modified completeness argument](../../sources/route-ap-locators.md#the-modified-completeness-argument)
