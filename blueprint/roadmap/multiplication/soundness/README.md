---
article_id: af_52305b67e76e99d13d5538c5
---

# Soundness: accepted triples are true

Soundness says that every rational triple accepted by the multiplication template consists
of codes $\iota(n_1),\iota(n_2),\iota(n_3)$ with $n_3=n_1n_2$. It uses the generator
certificate (hence Mordell-Weil) to give the inputs indices, the pole obstruction at single
primes, and the six-contact height estimate H. It does not use pole completeness or the
prime pattern.

## The congruence at odd contact primes

Fix an accepted slope $t$ and a prime $p\notin S_{\rm mul}$ at which some $v_p(t-c)$,
$c\in\mathcal C$, is positive and odd. Then $v_p(R_0)=v_p(t-c)$ is odd and $v_p(R)$ is odd and
no larger.

- [Valuations of the normalization at an odd contact prime](contact-valuations.md)

Each factor $1+RC_{gj}^2$ then has valuation $\min(0,\text{odd})$ at both places above $p$, so
every summand of the trace $\Theta$ is integral, and the pole obstruction applied to
$R/\Theta^2$ forces one group and one place at which the first eight tests have valuation at
least $1$ and the last four at least $25$. The manuscript's argument is written as if $p$
split; it works verbatim for inert $p$, where the conjugated tests refer to the same place.

- [The trace forces one common group and place](common-group.md)

At that place the first tests put $H,U_i$ in the formal group at $\mathfrak p$ and $V_0,V_i$ in
the formal group at the conjugate place. The full-log ratios are the rational numbers
$z_i/h$ and $(z_i-c_*n_i)/(h-c_*)$; one of $h,h-c_*$ is a unit at $p$, which makes its
truncated ratio integral; the difference test transfers integrality to the other ratio, and
only then do the relative errors of valuation $28$ become absolute congruences. Subtracting
the two congruences and dividing by $c_*$, which is prime to $p$, gives $n_i\equiv A_i$, and the
product test gives the congruence.

- [From the local tests to the congruence](tests-to-congruence.md)
- [The congruence at an odd contact prime](local-congruence.md)

## The finite-box deduction

For a false triple, $f=n_1n_2-n_3\ne0$ is divisible by $M_{S_{\rm mul}}(t)^{25}$ for each of the
$27$ slopes, so the six-contact estimate bounds every slope height by $A_{\rm ht}|f|^{24/25}$.

- [The height of an accepted slope](contact-support.md)

The sum and quotient bounds carry this to the rational components of the three abscissas,
the coordinate change to $C$ and the canonical height carry it to the indices, and an
elementary inequality bounds the indices by $T$. Two explicit numerical constants enter:
$B_0<10$ and $2\widehat h(P_0)>1$.

- [Sum and quotient bounds for rational heights](rational-height-bounds.md)
- [Height bounds in $K_0$](field-height-bounds.md)
- [The integer inequalities behind the height constants](height-constant-integers.md)
- [Explicit height constants](height-constants.md)
- [The canonical height of multiples of $P_0$](generator-height.md)
- [The final inequality of the finite-box deduction](box-inequality.md)
- [The finite-box deduction](finite-box.md)

## The guard closes the gap

A false triple accepted by the unguarded certificate lies in $[-T,T]^3$, where the guard
rejects it.

- [Soundness of the multiplication template](soundness.md)
