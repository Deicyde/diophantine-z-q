---
article_id: af_6916b8dfc1aa12a1a25d2c7a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Mult.local_congruence
---

# The congruence at an odd contact prime

Let $n_1,n_2,n_3\in\mathbb Z$, put
$c=(c_*,c_*n_1,c_*n_2,c_*n_3)$, and let $t\in\mathbb Q$ satisfy $\mathrm{Slope}(t,\ell_0;c)$. If
$p\notin S_{\rm mul}$ is a prime such that $v_p(t-c')$ is positive and odd for some
$c'\in\mathcal C$, then
$$n_1n_2\equiv n_3\pmod{p^{25}} .$$

This is the local divisibility statement of Section 6. It uses the pole obstruction, but
neither the six-contact estimate nor pole completeness.

**Proof sketch.** Since $p\notin S_{\rm mul}\supseteq S_b$, the trace argument gives a group $g$
and a prime $\mathfrak p$ above $p$ at which the first eight tests of group $g$ have valuation at
least $1$ and the last four at least $25$. These are the test values
$\tau(h_g,z_g;c)$ with $h_g\ne0,c_*$. As $p>324$ and $p\nmid c_*$, the passage from the tests
to the congruence gives $p^{25}\mid n_1n_2-n_3$.

## Depends on

- [The slope predicate](../certificate/slope-predicate.md)
- [Prime sets and clearing exponents of the multiplication certificate](../certificate/constants.md)

## Proof depends on

- [The trace forces one common group and place](common-group.md)
- [From the local tests to the congruence](tests-to-congruence.md)
- [Properties of the multiplication constants](../certificate/constants-properties.md)

## Sources

- [Local congruence](../../../sources/multiplication-locators.md#local-congruence)
