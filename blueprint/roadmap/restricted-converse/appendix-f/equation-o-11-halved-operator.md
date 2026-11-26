---
article_id: af_a0e52115333297f45beee072
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Odd.O11_theta, ZInQ.Manuscript.RC.Odd.O11_offJ, ZInQ.Manuscript.RC.Odd.O11_odd_stage
---

# (O.11): the halved operator $H_U$

Assume a coefficient source of integer depth $\delta$ truncated at $T$, as on the page of
[(O.9)](equation-o-9-divided-operators.md) (`SourceHyp`, named inputs, not proved), and let $\theta(m)$
be integers that are odd at odd $m$. For a finite set $U$ of good primes put $n_U=\delta+|U|$ and
$G_U=\prod_{p\in U}(U_p-\eta(p)V_p)\,g=2^{n_U}B_U$. Then:

- at every index $nm^2$ with $n\ne0$ whose squarefree kernel (the primes dividing $n$ to an odd power)
  lies in $U$, and $m$ odd with only good prime factors, $2^{\min(T,\,n_U+1)}$ divides
  $G_U[nm^2]-\eta(m)\theta(m)\,G_U[n]$;
- at every index whose squarefree part is not contained in $U$, $2^{\min(T,\,n_U+1)}$ divides the
  coefficient of $G_U$.

With $\theta(m)=\chi_{-4}(m)^im$, the coefficient at $Jm^2$ of the unary series
$\Theta_J=\sum_{(m,S)=1}\eta(m)\chi_{-4}(m)^im\,q^{Jm^2}$, where $i\in\{0,1\}$ makes $\eta\chi_{-4}^i$
odd, this says that below the truncation
$$H_U=\frac{B_U-\sum_JB_U[J]\,\Theta_J}{2}\tag{O.11}$$
has integral coefficients at these indices. Neither declaration covers the index $0$ or an index
$Jm^2$ whose $m$ is even or has a prime factor that is not good; in the abstract source the
coefficients there vanish (at $0$ by its field `zero`, elsewhere by `SourceHyp.support`). For the
lifted form of an actual stage, `ThetaCoeff.Hnum_dvd` and `ThetaCoeff.HU_spec` state the division by
two at every index; they are not on the path of the reduction either.

Only matching parity occurs, since every prime is split and $\delta$ is an integer, so the alternative
$H_U=B_U$ is not needed. The unary series enters only through its coefficients; that it is a form of
weight $3/2$ is not formalized. At a valid odd stage (`O11_odd_stage`) the first clause holds with
exponent $n_U+1$ for every $|U|\le W_U$ once $R\ge1$.

This theorem is not on the path of the reduction of Theorem 5.3, which reads the sources through the
trace models of `PostLeaves.address` ([Proposition F.5](proposition-f-5-coefficient-rules.md)).

**Proof sketch.** At an index $Jm^2$ the recurrence (O.6) at the primes of $m$ gives
$G_U[Jm^2]\equiv\eta(m)G_U[J]$ modulo $2^{\min(T,\,n_U+1)}$, and $\theta(m)-1$ is even while
$2^{\min(T,\,n_U)}$ divides $G_U[J]$ by (O.9). At an index whose squarefree part has a prime outside
$U$, (O.9) applies with $\omega(r)\ge1$.

## Depends on

- [Proposition F.2: the odd theta form and its recurrence](proposition-f-2-odd-theta-form.md)

## Proof depends on

- [(O.9): the valuation of the operator coefficients](equation-o-9-divided-operators.md)

## Sources

- [Appendix F](../../../sources/manuscript.md#appendix-f)
