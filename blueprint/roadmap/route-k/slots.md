---
article_id: af_90809b8ed2b01245929dcac4
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.exists_slots, ZInQ.RouteK.exists_slots_of_admissible, ZInQ.RouteK.exists_multiplier_and_slots
---

# The slots exist

Let $\beta,\theta$ be odd coprime integers and $p_0\in P(\beta)$. Then slot data for
$\beta,\theta,p_0$ exist: primes $q_0$, $r_p$ ($p\in P(\beta)\setminus\{p_0\}$) and $r_\ell$
($\ell\in P(\theta)$) satisfying [the slot conditions](slot-conditions.md).

For an admissible $B$ these hypotheses hold: by the multiplier lemma there is a signed divisor
$m$ of $2730$ with $\beta=\mathrm{sqf}(mB)$ odd and $|\beta|\equiv7\pmod8$, so $P(\beta)\ne\emptyset$,
and $\theta=\mathrm{sqf}(m(m-B))$ is odd and coprime to $\beta$ by (θ1) and (θ2); so the slots
exist for every $p_0\in P(\beta)$.

**Proof sketch.** Choose $q_0$, then the $r_p$ one after the other, then the $r_\ell$ one after
the other, each by the slot lemma: each condition fixes the class modulo $8$ and the residue bit
modulo finitely many odd primes already fixed, and the new prime avoids all primes already used
and the primes of $2\beta\theta$. The conditions $[r/r']=0$ between two glue slots, imposed
against the earlier one only, hold in both directions by reciprocity, since both are
$\equiv1\pmod4$.

## Depends on

- [The slot conditions](slot-conditions.md)
- [Admissible inputs, the squarefree part, $\beta$ and $\theta$](squarefree-part.md)

## Proof depends on

- [The slot lemma](slot-lemma.md)
- [Quadratic reciprocity in residue bits](reciprocity-bits.md)
- [The multiplier lemma](multiplier-lemma.md)
- [The properties (θ1)–(θ4)](theta-properties.md)

## Sources

- [Slots](../../sources/route-k-locators.md#slots)
