---
article_id: af_26908decedf0232ab60fec7b
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Size.bad_place_congruences, ZInQ.Size.bad_place_congruences_zmod
---

# Congruences for $P_0$ modulo seven

The following closed statements about integers hold:
$$1641-1160\cdot3-2\cdot8\equiv0,\qquad -123720+87483\cdot3-6\cdot32\equiv0,\qquad
-11243+7950\cdot3\equiv0,\qquad 6^2-2^3\equiv0\pmod 7,$$
$$2\cdot6\not\equiv0,\qquad 3\cdot2^2\not\equiv0,\qquad 8\not\equiv0,\qquad 32\not\equiv0\pmod 7 .$$

This is a finite computation on integers below $3\cdot10^5$.

**Proof sketch.** Direct evaluation: the four left-hand sides are $-1855=-7\cdot265$,
$138537=7\cdot19791$, $12607=7\cdot1801$ and $28=7\cdot4$, while $12$, $12$, $8$ and $32$ are
congruent to $5$, $5$, $1$ and $4$ modulo $7$.

The manuscript records the outcome (the reduction of $P_0$ at the bad place is $(2,6)$ on
$y^2=x^3$ and is nonsingular) without listing the congruences.

## Depends on

None.

## Sources

- [Proof of Proposition 12.1, formal multiple](../../../sources/size-locators.md#proof-of-proposition-121-formal-multiple)
