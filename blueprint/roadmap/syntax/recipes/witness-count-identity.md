---
article_id: af_0c6502150a154a737c5aa686
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Syntax.witness_count_arith, ZInQ.Syntax.variable_count_arith
---

# The witness-count arithmetic

The following identities between explicit natural numbers hold:
$$3+79\,(5+140604)+3\,(5+1)+196\,(5+6)+190\,(5+35134)=17786698,$$
$$3+5\cdot140604+54051\,(5+140604)+4\,(5+1)+125327\,(5+6)+98382\,(5+35134)+15845\,(5+17786698)=292889492836,$$
$$8\cdot5+5\cdot140654+292889492836+53=292890196199,$$
$$5+292890196199+35282=292890231486,\qquad 406+292890231486=292890231892,$$
$$7+292890231892=292890231899,\qquad 5+292890231899=292890231904 .$$
Adding the parameter counts gives the total variable counts $17786718$, $292889492861$,
$292890196210$, $292890231492$, $292890231898$, $292890231905$ and $292890231905$.

This is a closed decidable statement (integer arithmetic).

## Depends on

None.

## Sources

- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
