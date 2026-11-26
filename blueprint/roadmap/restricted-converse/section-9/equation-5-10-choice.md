---
article_id: af_f01f918e43625d56bc9399ed
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Boolean.choice510_exists, ZInQ.Manuscript.RC.Boolean.Choice510
---

# (5.10): the choice of the precision and the address dimension

There are no inputs: the theorem is unconditional.

Let $B$ bound $v_2\widetilde u_x(0)$ at the nonzero addresses. Choose
$$M>\max(c_{\det},B+2c_{\det}),\qquad b>(L_T(M)+2)(2^M-1).\tag{5.10}$$
The choice uses only $c_{\det}$, $B$ and $d_K$, so it is made before the graph and its theta precision.

`Choice510` is the conjunction of the two inequalities, with $L_T(M)=16(d_K+5)M$; `choice510_exists` says
that the choice can be made: some $M>\max(c_{\det},B+2c_{\det})$ has (5.10) for every
$b>(L_T(M)+2)(2^M-1)$.

The reduction of Theorem 5.3 does not use this theorem: its last step (see [the
reduction](../reduction.md)) takes $M=B+2c_{\det}+1$ and $b$ the larger of the threshold of
[(3.9)](../section-7/proposition-7-17-final-family.md) and $(L_T(M)+2)(2^M-1)+1$.

**Proof sketch.** Take $M$ one more than $\max(c_{\det},B+2c_{\det})$.

## Depends on

None.

## Sources

- [Section 9](../../../sources/manuscript.md#section-9)
