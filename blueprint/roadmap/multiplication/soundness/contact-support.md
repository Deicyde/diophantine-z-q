---
article_id: af_43506cf4e50d1d519ba33af3
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.slope_height_le
---

# The height of an accepted slope

Assume the six-contact height estimate. Let
$n_1,n_2,n_3\in\mathbb Z$ with $f=n_1n_2-n_3\ne0$, put $c=(c_*,c_*n_1,c_*n_2,c_*n_3)$, and let
$t\in\mathbb Q$ satisfy $\mathrm{Slope}(t,\ell_0;c)$. Then
$$M_{S_{\rm mul}}(t)^{25}\mid f\qquad\text{and}\qquad h(t)\le A_{\rm ht}\,|f|^{24/25}.$$

This is where the sound direction uses the six-contact estimate, with $S=S_{\rm mul}$ and the
fixed $R=\max(D,H_{\max},c_*,10^{12})$.

**Proof sketch.** $M_{S_{\rm mul}}(t)$ is a product of distinct primes $p\notin S_{\rm mul}$, each an
odd contact prime of $t$, so $p^{25}\mid f$ by the local congruence; the prime powers are
pairwise coprime, so $M_{S_{\rm mul}}(t)^{25}\mid f$, and since $f\ne0$,
$M_{S_{\rm mul}}(t)^{24}\le|f|^{24/25}$. The slope predicate gives $t\notin\mathcal C$. The
properties of the constants show that $S_{\rm mul}$ and $R$ are admissible in the six-contact
estimate and that its constant is $A_{\rm ht}$; hence
$h(t)\le A_{\rm ht}M_{S_{\rm mul}}(t)^{24}\le A_{\rm ht}|f|^{24/25}$.

## Depends on

- [The slope predicate](../certificate/slope-predicate.md)
- [Prime sets and clearing exponents of the multiplication certificate](../certificate/constants.md)
- [The six-contact height estimate](../../main/six-contact-estimate.md)

## Proof depends on

- [The congruence at an odd contact prime](local-congruence.md)
- [Properties of the multiplication constants](../certificate/constants-properties.md)

## Sources

- [Finite-box deduction](../../../sources/multiplication-locators.md#finite-box-deduction)
