---
article_id: af_892777c7d8d70d6fdec2f9fd
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Odd.shellDiff_half_modEq, ZInQ.Manuscript.RC.Odd.shellDiff_modEq, ZInQ.Manuscript.RC.GlueSweep.Odd.ap_mod_four_curve
---

# (O.10): the parity of the divided shells

Assume only that $p$ is odd, $a_p\equiv p+1\pmod4$ and $\kappa\in\{1,-1\}$; there are no other inputs.
Removing the phase $\eta(p)^s$ in (O.6) gives the shell sequence
$$b_{-1}=0,\quad b_0=1,\quad b_1=a_p-\kappa,\quad b_{s+1}=a_pb_s-pb_{s-1}.$$
Then every difference $b_{s+1}-b_s$ is even, and for every $s\ge0$
$$\frac{b_{s+1}-b_s}{2}\equiv c_p:=\frac{a_p-\kappa-1}{2}\pmod2.\tag{O.10}$$

In the manuscript $\kappa=(\psi/\eta)(p)(-D/p)$ for the squarefree parameter $D$ of the coefficient,
with $p\nmid D$, so that $c_p=c_p(D)$; the Lean statement has $\kappa$ as a parameter. The hypothesis
$a_p\equiv p+1\pmod4$ holds for $E_\ell:y^2=x(x-\ell)(x+3\ell)$ at every prime $p\nmid6\ell$
(`ap_mod_four_curve`), since the full rational two-torsion makes $4$ divide $|E_\ell(\mathbb F_p)|$.

This theorem is not on the path of the reduction of Theorem 5.3; there the congruence
$a_p\equiv p+1\pmod4$, proved for the actual curves, enters the coefficient rules as the evenness of
$a_p$ ([Proposition F.5](proposition-f-5-coefficient-rules.md)).

**Proof sketch.** Every $b_s$ is odd, since $a_p$ is even and $\kappa$ odd. Put $d_s=b_{s+1}-b_s$; the
recurrence gives $d_{s+1}-d_s=(a_p-1-p)\,b_{s+1}+(p-1)\,d_s$. The first term is divisible by $4$, and so
is the second once $d_s$ is even, so by induction every $d_s$ is even and
$d_s\equiv d_0=a_p-\kappa-1 \pmod4$. Halving gives (O.10), without dividing a residue-field identity by
two.

## Depends on

None.

## Sources

- [Appendix F](../../../sources/manuscript.md#appendix-f)
