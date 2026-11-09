---
article_id: af_f409a876f4ee828ed69ca8a4
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.slope_complete
---

# Completeness of the slope certificate for a true triple

Assume pole completeness. Let
$n_1,n_2\in\mathbb Z$, $n_3=n_1n_2$ and $c=(c_*,c_*n_1,c_*n_2,c_*n_3)$. If $t\in\mathbb Q$
satisfies conditions 1-4 of the slope representation (for some $B_0$), then
$$\mathrm{Slope}(t,\ell_0;c).$$

This is where pole completeness is used: it supplies the eleven pole witnesses once the
pole input is shown to satisfy its hypotheses, including all nonzero guards.

**Proof sketch.** Condition 1 gives $t\notin\mathcal C\cup\{1\}$, and $\ell_0\ne0$. Choose $\eta$
with $R_0=\eta F(t)/(t-1)^8>0$. Let $p_1,\dots,p_m$ ($m\le6$) be the odd contact primes of $t$
outside $S_b$; each $p_g$ is a good slope prime with orders $d_1,d_2$, $\gcd(d_1,d_2)=4$,
and $p_g>324$. For $g\le m$ the shift choice gives $h_g>c_*$ with $M_0\mid h_g$, $d_1\mid h_g$
and $d_2\mid h_g-c_*$; for $g>m$ put $h_g=2c_*$. Put $z_{g,i}=n_ih_g$ and
$D_{gj}=\tau_j(h_g,z_g;c)$. Each $h_g\ne0,c_*$. The tests are integral at every prime above
$S_b$, and the group of $p_g$ has $v_{\mathfrak p_1}(D_{gj})\ge1$ ($j\le8$) and $\ge28\ge25$ ($j\ge9$)
at $\mathfrak p_1=(p_g,s-r_g)$. The $C_{gj}$ are now fixed; take $\varepsilon$ from the positivity
lemma. By weak approximation choose $q\ne\pm R_0^{-1/2}$ with $v_p(q)\ge C_p$ on $S_b$,
$v_{p_g}(q)\ge0$, and $q$ so close to $R_0^{-1/2}$ that $0<|a|<\varepsilon$ for $a=1-R_0q^2$. Then
$W_g\ne0$, $\Theta\ne0$ and $0<B<1/2$ for $B=R/\Theta^2$; the valuation lemma gives
$v_p(B)\ge4$ for $p\in S_0$ and a square reduced denominator. Pole completeness gives
$\Phi(B)$, which completes the slope predicate.

## Depends on

- [The slope predicate](../certificate/slope-predicate.md)
- [The slope representation](slope-representation.md)
- [Prime sets and clearing exponents of the multiplication certificate](../certificate/constants.md)
- [Pole completeness](../../main/pole-completeness.md)

## Proof depends on

- [Choice of the shift at a selected prime](shift-choice.md)
- [Integrality of the tests at the old primes](sb-integrality.md)
- [Precision of the tests at a selected prime](selected-prime-precision.md)
- [Weak approximation for the parameter $q$](weak-approximation.md)
- [Positivity and smallness of the pole input](pole-input-positivity.md)
- [Valuations of the pole input of a completed slope](pole-input-valuations.md)
- [Properties of the multiplication constants](../certificate/constants-properties.md)

## Sources

- [Choice of shifts](../../../sources/multiplication-locators.md#choice-of-shifts)
- [Pole input of a completed slope](../../../sources/multiplication-locators.md#pole-input-of-a-completed-slope)
- [Pole completeness](../../../sources/multiplication-locators.md#pole-completeness)
