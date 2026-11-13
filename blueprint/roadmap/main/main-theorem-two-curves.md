---
article_id: af_bd602c5d214aff8b7e221f0d
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLRk, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLAdmRk
---

# The main theorem from positive rank on the two curves of a slot choice

Assume the minimal height hypothesis and the hypothesis CR₃^DL,Rk. Then the target statement holds.

CR₃^DL,Rk is the following assertion. Let $\beta,\theta$ be integers and $p_0$ a prime dividing
$\beta$ such that $\beta$ is odd and squarefree with $|\beta|\equiv7\pmod8$; $\theta>0$ is squarefree
with $\theta\equiv1\pmod8$; $\beta$ and $\theta$ are coprime; $[\beta/\ell]=0$ for every prime
$\ell\mid\theta$; and $[\theta/p]=0$ for every prime $p\mid\beta$. Then there are slot data $q_0$,
$r_p$ ($p\in P(\beta)\setminus\{p_0\}$) and $r_\ell$ ($\ell\in P(\theta)$) for $\beta,\theta,p_0$,
satisfying [the slot conditions](../route-k/slot-conditions.md), such that, with
$$d_1=|\beta|\,q_0\prod_pr_p\prod_\ell r_\ell,$$
both $C_{d_1}(\mathbb Q)$ and $C_{d_1\theta}(\mathbb Q)$ have a point of infinite order. Here $C_d$ is
the curve $y^2=x^3-d^2x$. These are the two curves at which the proof of pole completeness uses
the rank hypothesis. CR₃^DL,Rk follows from [CR₃^Rk](../rank/two-curves/certified-rank-dl-rk-of-rk.md)
and from [CR₃^TYZ,Rk](../rank/two-curves/certified-rank-dl-rk-of-tyz-rk.md), so this form assumes no
more than [the main theorem from the positive-rank forms](main-theorem-positive-rank.md).

The theorem also holds under the minimal height hypothesis and
[CR₃^DL,Adm,Rk](../rank/two-curves/certified-rank-dl-adm-rk.md), which asks only that for every
admissible $B$ there be a signed divisor $m$ of $2730$ with $\beta=\mathrm{sqf}(mB)$ odd and
$|\beta|\equiv7\pmod8$, a prime $p_0\mid\beta$ and slot data whose two curves have points of
infinite order; CR₃^DL,Adm,Rk
[follows from CR₃^DL,Rk](../rank/two-curves/certified-rank-dl-adm-rk-of-dl-rk.md).

**Proof sketch.** The proof does not pass through CR₃.

1. CR₃^DL,Rk implies pole completeness. For an admissible input, the multiplier lemma and the
   properties (θ1)–(θ4) give slot inputs $\beta,\theta,p_0$, and CR₃^DL,Rk gives slot data whose two
   curves have positive rank. On each curve the Selmer certificate of the realization gives, by
   Proposition 0, a Selmer group of order $8$ containing a class $(\beta,b)$; with the point of
   infinite order and Mordell–Weil, RK9 makes that class come from a rational point $(x,y)$ with
   $x/\beta$ a square, and the two points give a zero of the pole polynomial.
   Under CR₃^DL,Adm,Rk, which supplies for each admissible input a multiplier, a prime $p_0$
   and slot data whose two curves have points of infinite order, the same argument at those curves
   gives pole completeness directly.
2. Szemerédi's theorem in the primes and Proposition D give 22P_AP, and Proposition AP turns 22P_AP
   into the slope representation under field 2′.
3. The bound on the addition and multiplication nodes of the universal halting circuit holds.
4. The assembly lemma under field 2′, applied to the minimal height hypothesis and steps 1–3, gives
   the target.

## Depends on

- [The target statement](frozen-target.md)
- [The minimal height hypothesis](six-contact-min.md)
- [The slot conditions](../route-k/slot-conditions.md)
- [The positive-rank hypothesis on the two curves of a slot choice](../rank/two-curves/certified-rank-dl-rk.md)
- [The positive-rank hypothesis at the inputs of admissible numbers](../rank/two-curves/certified-rank-dl-adm-rk.md)

## Proof depends on

- [Pole completeness from CR₃^DL,Rk](../rank/two-curves/pole-completeness-from-dl-rk.md)
- [Pole completeness from CR₃^DL,Adm,Rk](../rank/two-curves/pole-completeness-from-dl-adm-rk.md)
- [The assembly lemma under field 2′](../route-ap/assembly-ap.md)
- [Proposition AP: progressions of good slope primes give the slope representation](../route-ap/proposition-ap.md)
- [22P_AP from Green–Tao and Proposition D](../route-ap/good-prime-ap-from-green-tao.md)
- [Szemerédi's theorem in the primes holds](../green-tao/dense-theorem.md)
- [Proposition D: the good slope primes have positive relative density](../density/proposition-d.md)
- [Node statistics of the halting circuit and the power template](../compiler/natural/universal/halting-node-check.md)

## Sources

- [Theorem 1.1 and Lemma 1.2](../../sources/manuscript.md#theorem-11)
- [The two curves of a slot choice](../../sources/rank-locators.md#the-two-curves-of-a-slot-choice)
- [Positive rank on the two curves](../../sources/rank-locators.md#positive-rank-on-the-two-curves)
