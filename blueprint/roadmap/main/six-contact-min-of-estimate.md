---
article_id: af_d90d073e6528d96e052d5dd8
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.sixContactMin_of_sixContactEstimate, ZInQ.Mult.le_heightD_of_mem_S_mul
---

# The six-contact estimate implies its minimal form

Every prime of $S_{\rm mul}$ is at most $D$. Consequently the six-contact height estimate
implies the minimal height hypothesis: for every $u\in\mathbb Q\setminus\mathcal C$,
$h(u)\le H_6(D)\,M_{S_{\rm mul}}(u)^{24}$.

**Proof sketch.** Every $p\in S_{\rm mul}$ satisfies $p\le R=\max(D,H_{\max},c_*,10^{12})$, and
$R=D$ because the catalogue bound holds; so $\max S_{\rm mul}\le D$. Also $D\ge324!>10^{12}$.
The set $S_{\rm mul}$ is a finite set of primes containing every prime at most $324$, and
$R=D$ satisfies $R\ge\max(D,\max S_{\rm mul},10^{12})$, so the six-contact estimate applies
with $S=S_{\rm mul}$ and $R=D$. Its constant $H_6(S_{\rm mul};D)$ is $H_6(D)$, and its conclusion
is the minimal height hypothesis.

## Depends on

- [The six-contact height estimate](six-contact-estimate.md)
- [The minimal height hypothesis](six-contact-min.md)
- [Prime sets and clearing exponents of the multiplication certificate](../multiplication/certificate/constants.md)

## Proof depends on

- [Properties of the multiplication constants](../multiplication/certificate/constants-properties.md)
- [The parameter $R$ equals $D$](../size/constants/r-equals-d.md)
- [The catalogue bound holds](../progressions/catalogue-instance.md)
- [The precision constant is the six-contact constant](../compiler/natural/precision/precision-height-constant-value.md)

## Sources

- [Theorem 4.1](../../sources/manuscript.md#theorem-41)
