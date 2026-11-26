---
article_id: af_d20e50050fb896e0a12905fd
declaration: theorem
origin: bridged
---

# CR₃^DL,Adm,Rk from CR₃^DL,Rk

> **The congruent-number route.** This page belongs to the congruent-number route to pole completeness, through Tian–Yuan–Zhang and Gross–Zagier. [Elliot's route](../../main/main-theorem.md) is the other route to the same theorem. This page's Lean declarations are not on this fork's main (fork issue #77); the route's Lean is kept at the tag `route-k-final` and pinned upstream in elliotglazer/diophantine-z-q.

The hypothesis CR₃^DL,Rk implies CR₃^DL,Adm,Rk.

**Proof sketch.** Let $B$ be admissible. By the multiplier lemma in its combined form with the
existence of the slots, of which only the multiplier part is used here, there is a signed divisor
$m$ of $2730$ with $\beta=\mathrm{sqf}(mB)$ odd and $|\beta|\equiv7\pmod8$, and $\beta$ has a
prime factor $p_0$. With $\theta=\mathrm{sqf}(m(m-B))$, the descent lemma's facts about admissible
inputs, which rest on (θ1)–(θ4), show that $\beta,\theta,p_0$ satisfy the hypotheses of
CR₃^DL,Rk. CR₃^DL,Rk at $\beta,\theta,p_0$ gives slot data whose two curves have points of
infinite order; with $m$ and $p_0$ these are the data CR₃^DL,Adm,Rk asks for.

## Depends on

- [The positive-rank hypothesis on the two curves of a slot choice](certified-rank-dl-rk.md)
- [The positive-rank hypothesis at the inputs of admissible numbers](certified-rank-dl-adm-rk.md)

## Proof depends on

- [The slots exist](../../route-k/slots.md)
- [The descent lemma](../../route-k/descent-lemma.md)

## Sources

- [The two curves of a slot choice](../../../sources/rank-locators.md#the-two-curves-of-a-slot-choice)
