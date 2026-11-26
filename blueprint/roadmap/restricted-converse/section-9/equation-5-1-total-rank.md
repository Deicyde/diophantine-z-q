---
article_id: af_a8c8ed1c1ecc7e9f1194c11b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.GlueSweep.Lim.ex_limits_residual_bound_5_1_lim, ZInQ.Manuscript.RC.Limits.display_5_1
---

# (5.1): the total rank of the smaller-support cone

Assume the four specializations of statements of Milne's *Arithmetic Duality Theorems* used in [Lemma
9.2](lemma-9-2-residual-bound.md) (PRINT, each read through GLUE; the two global ones not checked
against the print; not proved, and not inputs of the reduction of Theorem 5.3), the Kummer sequence
(`kummer`, GLUE), the genus bound (`genus`, ELLIOT: the manuscript proves it), the table of local
conditions (`hcond`, ELLIOT), and rank bounds for finite free models of the global and local terms
(`hG`, `hL`, ELLIOT). As on the page of Lemma 9.2, `kummer` and `genus` say only
$h^1(G_{K,S_T},\mathbb F_2)\le|S_T|+r$, with the class-group dimension a free number.

With $v=\omega(2N)$, $m=v+1+j$ and $s$ as in (5.1a) (on [the page of Lemma
9.2](lemma-9-2-residual-bound.md)), the finite free model of the Selmer cone over the
smaller support $S_0$ satisfies
$$\operatorname{rank}_{\rm tot}C_{S_0}\le(8s+2)+48m+4\le8(s+1)+6+48(v+1+j)\le56v+8A+56j+70.\tag{5.1}$$

`ex_limits_residual_bound_5_1_lim` states the outer inequality for the cone of one Selmer datum; the two
middle steps are the arithmetic `display_5_1`, from (5.1a) and $m=v+1+j$. The manuscript gets the rank
bounds of the global and local models from Lemma 9.1 at each coefficient stage; Lean takes them as the
hypotheses `hG` and `hL`.

The reduction of Theorem 5.3 does not use this theorem: the field `PreLeaves.eq35` of [the remaining
hypotheses](../remaining-hypotheses.md) asks that the models of (3.5) have size at most
$56\,\omega(2N)+8A+56j+70$ (`eq51Cap`), a bound on matrix size that this total-rank bound implies.
The reduction never reads that size cap: its proof of (3.5) discards it.

**Proof sketch.** The global terms contribute at most $8s+2$ and the local terms at most $48m$, as in
the proof of Lemma 9.2; the complex place adds at most four. Then (5.1a) and $m=v+1+j$ give the last
two steps.

## Depends on

None.

## Sources

- [Section 9](../../../sources/manuscript.md#section-9)
