---
article_id: af_14308f020a47cd5d58e29e79
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.pole_input_valuations_AP, ZInQ.Mult.GoodSlopeAP.contactQuot_eq_one
---

# Valuations of the pole input under field 2′

Let $t\in\mathbb Q$ satisfy conditions 1, 2′, 3, 4 (for some $B_0$), and let $P(t)$ be its set of
odd contact primes outside $S_b$. Let $\eta\in\{1,-1\}$, $R_0=\eta F(t)/(t-1)^8$, let $\ell\ne0$
with $v_p(\ell)=E_p$ for $p\in S_b$ and $v_p(\ell)=0$ for every other prime, and let $q\in\mathbb Q$
with $a=1-R_0q^2\ne0$ such that

- for every $p\in S_b$, either the bounds of condition 2 hold at $p$ and $v_p(q)\ge C_p$, or
  there is $e\in\mathbb N$ with $v_p(F(t)/(t-1)^8)=2e$, $v_p(t-1)=-e$ and
  $v_p(a)\ge23e+v_p(12)+2$;
- $v_p(q)\ge0$ for every $p\in P(t)$.

Let $D_{gj}\in K_0$ satisfy (i) and (ii) of the valuations of the pole input of a completed slope
(integral above $S_b$; for each $p\in P(t)$ some group and place with $v_{\mathfrak p}(D_{gj})\ge k_j$),
and assume $W_g\ne0$ and $\Theta\ne0$. Then $B=R/\Theta^2$ satisfies:

1. $v_p(B)\ge4$ for every $p\in S_b$, in particular for every $p\in S_0$;
2. $v_p(B)=1$ for every $p\in P(t)$;
3. $v_p(B)$ is even for every other prime $p\notin S_b$;

and the reduced denominator of $B$ is a perfect square.

The only change from the original lemma is part 1: $v_p(B)\ge4$ replaces
$v_p(B)\ge103C_p+8$, which is all that pole completeness and the square denominator need.

**Proof sketch.** At $p\in S_b$ with the first alternative, the original argument applies
verbatim. With the second alternative, Lemma P(3) gives $v_p(B)\ge4$; its integrality hypothesis
is (i), and $v_p(\ell)=E_p\ge0$. At $p\in P(t)$, conditions 1 and 3 alone give
$v_p(F(t)/(t-1)^8)=1$ and $v_p(t-1)=0$, and the original argument applies. At the other
primes the parity argument is unchanged, since $a$ enters $R$ squared.

## Depends on

- [Slopes with poles at the old primes: field 2′](good-slope-ap.md)
- [The slope predicate](../multiplication/certificate/slope-predicate.md)
- [Prime sets and clearing exponents of the multiplication certificate](../multiplication/certificate/constants.md)

## Proof depends on

- [Valuations of the pole input of a completed slope](../multiplication/completeness/pole-input-valuations.md)
- [Lemma P, part (3): the valuation of the pole input](lemma-p-valuation.md)

## Sources

- [The modified completeness argument](../../sources/route-ap-locators.md#the-modified-completeness-argument)
- [Pole input of a completed slope](../../sources/multiplication-locators.md#pole-input-of-a-completed-slope)
