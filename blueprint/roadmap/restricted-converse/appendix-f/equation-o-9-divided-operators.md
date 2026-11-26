---
article_id: af_ae6d1ccb743d60061a6a19a9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Odd.O9, ZInQ.Manuscript.RC.Odd.O9_odd_stage, ZInQ.Manuscript.RC.Odd.SourceHyp
---

# (O.9): the valuation of the operator coefficients

Let $a$ be a coefficient function with values in a commutative ring, with a character $\eta$, a set of
good primes, a stage support and integers $a_q$. Assume they form a coefficient source of integer depth
$\delta$ truncated at $T$ (`SourceHyp`, named inputs, not proved): the good primes are odd with
$a_q\equiv q+1\pmod4$; the recurrence (O.6) of [Proposition F.2](proposition-f-2-odd-theta-form.md)
holds at every good prime with $(\psi/\eta)(q)=\pm1$; $a(0)=0$; $a$ vanishes at indices with a prime
factor that is not good and at squarefree parameters off the stage support; $\eta$ is completely
multiplicative; and $v_2a(D)\ge\min(T,\delta+\omega(D))$ at every squarefree $D$ in the stage support.
For a finite set $U$ of good primes put $n_U=\delta+|U|$ and
$B_U=2^{-n_U}\prod_{p\in U}(U_p-\eta(p)V_p)\,g$, where $g=\sum a(n)q^n$. Write an index as $Jrm^2$ with
$J\subseteq U$ and $r$ squarefree and prime to $U$. Then
$$2^{\min(T,\;n_U+\omega(r))}\ \Bigm|\ \Bigl(\prod_{p\in U}(U_p-\eta(p)V_p)\,g\Bigr)[Jrm^2],
\qquad\text{that is}\qquad v_2B_U[Jrm^2]\ge\min(T-n_U,\ \omega(r)).\tag{O.9}$$

In the full two-torsion family every prime is split, so the weight $w$ of the manuscript is $\omega$,
the term for simple primes and the parity defect $e_U$ vanish, and $\delta$ is an integer; the Lean
bound is for the undivided product. For the even source the depth holds at every truncation $T$. At a
valid odd stage (`O9_odd_stage`, with $T=\max(0,\delta_o+W_U)+R$) it gives
$v_2B_U[Jrm^2]\ge\min(R,\omega(r))$ for every $|U|\le W_U$, the manuscript's truncated form.

This theorem is not on the path of the reduction of Theorem 5.3, which reads the sources through the
trace models of `PostLeaves.address` ([Proposition F.5](proposition-f-5-coefficient-rules.md)).

**Proof sketch.** First the depth is extended to every index: the shell formulas of (O.6) remove the
squares of good primes, and the other indices have coefficient zero. Then induct over $U$. At $p\in U$
the operator $U_p-\eta(p)V_p$ multiplies the shell at $p$ by $b_s-b_{s-1}$ when $p\notin J$ and by
$b_{s+1}-b_s$ when $p\in J$, for the shell sequence $b$ of [(O.10)](equation-o-10-shell-parity.md); the
first is odd and the second even. The coefficient comes from the squarefree parameter
$D=(U\setminus J)r$, with $\omega(D)=|U|-|J|+\omega(r)$, and its depth plus the $|J|$ factors of two
give $n_U+\omega(r)$.

## Depends on

- [Proposition F.2: the odd theta form and its recurrence](proposition-f-2-odd-theta-form.md)

## Sources

- [Appendix F](../../../sources/manuscript.md#appendix-f)
