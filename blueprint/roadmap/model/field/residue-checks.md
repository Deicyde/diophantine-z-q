---
article_id: af_18be5f40662121123f869885
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.residues_mod_seven, ZInQ.not_isSquare_neg_one_zmod_seven
---

# Residue computations modulo seven

The following closed statements about integers modulo $7$ hold:

1. $3^2\equiv2\pmod 7$;
2. $75-53\cdot3=-84\equiv0\pmod7$, and $3-3=0$;
3. for every $t\in\mathbb Z/7\mathbb Z$, $t^2\ne-1$ (the squares modulo $7$ are $0,1,2,4$).

They say that $s\mapsto3$ defines a ring homomorphism $\mathbb Z[s]\to\mathbb F_7$ killing $d$
and $\delta$, and that $-1$ is not a square in $\mathbb F_7$. This is a finite computation.

**Proof sketch.** Direct evaluation; the third item is a check of the seven residues.

## Depends on

None.

## Sources

- [Second descent image](../../../sources/model-locators.md#second-descent-image)
- [Duplication bounds](../../../sources/model-locators.md#duplication-bounds)
