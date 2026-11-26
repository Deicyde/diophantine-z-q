---
article_id: af_00374182f12b7aef814f48ea
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Central.F8_of_calibration
---

# (F.8): the central identity for the corrected coordinate

Let $b\ge1$, let $\widetilde u_x(0)\in\mathbb Q_2$ be the values at $t=0$ of the coefficient data at the
addresses $x\in\mathbb F_2^b$, and let $u_{{\rm prim},x}(0)$, $e_x\in\mathbb Q_2$ and integers $\nu(x)$ be
given. Assume, at every $x\ne0$ (the reduction derives (4.6) from the field `PostLeaves.calibration`,
ELLIOT with PRINT and GLUE, and (4.7) from `PostLeaves.common_coordinate`, ELLIOT):

- (4.6) of Section 8 for the primitive coordinate: $u_{{\rm prim},x}(0)\ne0$ and
  $v_2u_{{\rm prim},x}(0)=\nu(x)$;
- (4.7) of Section 8 at $t=0$: $\widetilde u_x(0)=e_x\,u_{{\rm prim},x}(0)$ with $e_x\ne0$ and
  $v_2e_x=0$.

Then $\widetilde u_x(0)\ne0$ and $v_2\widetilde u_x(0)=\nu(x)$ at every $x\ne0$. For the family of (3.9) and
the final $k$, the formula of (4.6) makes this the central identity
$$v_2\widetilde u_x(0)=2j_{\rm rc}(h_x,k)-4\omega(h_x)-s(h_x)-s(h_xk)-\sum_{p\mid k}t_p+\epsilon'_x,
\qquad0\le t_p\le2,\quad|\epsilon'_x|\le C_{\rm cal}.\tag{F.8}$$

In the Lean statement the right side is an arbitrary function $\nu$: the formula, with its error bound, is
the content of (4.6), and $e_x$ is the value at $0$ of the $\Lambda$-unit of (4.7). The manuscript
then discards the nonnegative terms: with $2j_{\rm rc}(h_x,k)\le4\omega(h_x)+C_J$, from (3.4) and (3.9),
(F.8) bounds $v_2\widetilde u_x(0)$ above uniformly in $x\ne0$ and in $b$, and the determinant argument of
Section 9 contradicts this bound when the base coordinate vanishes.

The reduction of Theorem 5.3 does not use this theorem: its upper bound on $v_2\widetilde u_x(0)$ at the
nonzero addresses (`central_upper_bound`) combines (4.6), (4.7), (3.4) and
[(3.9)](../section-7/proposition-7-17-final-family.md) directly.

**Proof sketch.** The valuation is additive on nonzero products and $v_2e_x=0$.

## Depends on

- [Proposition 7.17: one family for the two coefficient tests (3.9)](../section-7/proposition-7-17-final-family.md)

## Sources

- [Appendix G](../../../sources/manuscript.md#appendix-g)
