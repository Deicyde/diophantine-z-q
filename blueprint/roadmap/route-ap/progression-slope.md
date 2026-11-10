---
article_id: af_d79c6463bdae4f4eba13dc5a
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.goodSlopeAP_of_progression, ZInQ.Mult.contactPoly_pos_of_pos, ZInQ.Mult.contactPoly_pos_of_lt, ZInQ.Mult.mem_patternShifts_bounds
---

# A slope with prime numerators satisfies field 2′

Let $u,v\in\mathbb Z$ with $v>0$. Suppose that for each $b\in\mathcal C\cup\{1\}$ the number
$|u-bv|$ is a prime larger than every prime of $S_b$, that for each $b\in\mathcal C$ it is a good
slope prime, and that $F(u/v)>0$. Then $t=u/v$ satisfies conditions 1, 2′, 3, 4 for $B_0=0$.

In addition, $F(t)>0$ whenever $t>0$ or $t<-60$.

**Proof sketch.** A prime dividing $u$ and $v$ would divide the seven numbers $u-bv$, which are
distinct primes, so $u/v$ is in lowest terms; the numbers are nonzero, so $t\notin\mathcal C\cup\{1\}$.
Let $p\in S_b$ and $e=v_p(v)$; all seven numbers are $p$-units. If $e\le B_p$ then
$v_p(t-1)=-e$ and $v_p(F(t)/(t-1)^8)=2e$ satisfy the bounds of condition 2 (when $e=0$ both
vanish). Otherwise $e\ge B_p+1\ge2$, and $e\ge5$ at $p=2$, so $t$ satisfies the hypotheses of
Lemma P at $p$, and $F(t)>0$ is assumed: field 2′ holds. Conditions 3 and 4 are the argument of
the two-slope pattern: an odd contact prime of $t$ outside $S_b$ divides some $u-cv$, so it is
that good slope prime, with contact valuation $1$, and there are at most six of them. The sign
statement holds because the six factors $t-c$ of $F(t)$ are all positive, or all negative.

## Depends on

- [Slopes with poles at the old primes: field 2′](good-slope-ap.md)
- [The two-slope prime pattern](../main/two-slope-pattern.md)

## Proof depends on

- [The two-slope pattern gives the slope representation](../multiplication/completeness/slope-representation-from-two-slope.md)

## Sources

- [The progression form](../../sources/route-ap-locators.md#the-progression-form)
