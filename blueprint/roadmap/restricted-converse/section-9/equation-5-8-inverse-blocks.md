---
article_id: af_05682e8410761b86cbafa029
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Determinant.PoleData.inv_neumann, ZInQ.Manuscript.RC.Determinant.newLocal_family_pole_genuine
---

# (5.8): the inverse new local blocks

There are no inputs beyond the data: for `inv_neumann`, square matrices $B$, $C$, $F$ over a commutative
ring with $B$ invertible and $BC=1+2F$; for `newLocal_family_pole_genuine`, a lifted family block over
$\Lambda[G]$ that augments to $\operatorname{diag}(A_q)$, with $\det A_q=t^{d_q}v_q+2w_q$, $d_q\le4$ and
$v_q$ a unit of $\Lambda$.

Put $C_q=\operatorname{adj}(A_q)/(t^{d_q}v_q)$. At a sign character $x$ the evaluated block satisfies
$B_xC=1+2F$, where $C$ and $F$ have no Laurent terms below degree $-4$, so
$$B_x^{-1}=C\sum_{j=0}^{M-1}(-2F)^j\pmod{2^M}\tag{5.8}$$
has pole at most $4M$, whatever the number of blocks.

`inv_neumann` is the exact identity $B^{-1}=C\sum_{j<M}(-2F)^j+2^MB^{-1}(-F)^M$, for matrices over any
commutative ring. `newLocal_family_pole_genuine` gives, over the actual $\mathscr O$ and at every sign
character, that $B_x$ is invertible and that every entry of $B_x^{-1}$ has pole at most $4M$ modulo
$2^M$.

The reduction of Theorem 5.3 uses `newLocal_family_pole_genuine`, which rests on `inv_neumann`, for the
pole bound on the entries in the proof of [Proposition 9.8](proposition-9-8-common-denominator.md),
applied to the new local blocks that the field `PostLeaves.clearing_model` of [the remaining
hypotheses](../remaining-hypotheses.md) supplies.

**Proof sketch.** Every sign is $1$ modulo $2$, so $B_x=\operatorname{diag}(A_q)+2V_x$ with $V_x$ over
$\Lambda$, and $\operatorname{adj}(A_q)A_q=\det A_q$ gives $B_xC=1+2F$ with poles at most four. The
geometric series telescopes, and its $j$-th term has pole at most $4(j+1)$.

## Depends on

None.

## Sources

- [Section 9](../../../sources/manuscript.md#section-9)
