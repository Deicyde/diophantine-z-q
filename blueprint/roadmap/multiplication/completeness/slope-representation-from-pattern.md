---
article_id: af_4d2eb3a3ad4049b1c0d518d3
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.slopeRepresentation_of_fixedPrimePattern
---

# The twenty-two-prime pattern gives the slope representation

Assume the twenty-two-prime pattern. Then the slope representation holds: every integer is a
sum of three good slopes.

**Proof sketch.** For $A\in\mathbb Z$, the slopes of an integer from the prime pattern with
$B_0=0$ give $t_1+t_2+t_3=A$ with each $t_j$ satisfying conditions 1-4 for $B_0=0$; these
are exactly the conditions of a good slope.

## Depends on

- [The slope representation](slope-representation.md)
- [The twenty-two-prime pattern](../../main/prime-pattern.md)

## Proof depends on

- [Slopes of an integer from the prime pattern](pattern-slopes.md)

## Sources

- [Prime pattern](../../../sources/multiplication-locators.md#prime-pattern)
