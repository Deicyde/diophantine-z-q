---
article_id: af_ee3deb61dc82f812eeea2a77
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.slope_complete_AP
---

# Completeness of the slope certificate under field 2′

Assume pole completeness. Let $n_1,n_2\in\mathbb Z$, $n_3=n_1n_2$ and
$c=(c_*,c_*n_1,c_*n_2,c_*n_3)$. If $t\in\mathbb Q$ satisfies conditions 1, 2′, 3, 4 (for some
$B_0$), then
$$\mathrm{Slope}(t,\ell_0;c).$$

**Proof sketch.** As for the completeness of the slope certificate for a true triple, except for
the choice of $q$. Choose $\eta$ with $R_0=\eta F(t)/(t-1)^8>0$, the shifts $h_g$ at the
selected odd contact primes, the test values $D_{gj}$ and $\varepsilon$ from the positivity lemma,
exactly as before. Let $S_{\rm pole}\subseteq S_b$ be the old primes at which field 2′ uses its
second alternative; there $F(t)>0$, so $\eta=1$. For $p\in S_{\rm pole}$ Lemma P(2) with
$N=23e_p+v_p(12)+2$, $e_p=v_p(\text{denominator of }t)$, gives a rational ball
$|q-m_p/p^{k_p}|_p\le p^{-n_p}$ on which $v_p(1-R_0q^2)\ge N$. Weak approximation with residue
targets chooses a nonzero $q\notin\{\pm R_0^{-1/2}\}$ in these balls, with $v_p(q)\ge C_p$ at the
other primes of $S_b$ (target $0$), $v_p(q)\ge0$ at the selected primes, and $q$ so close to
$R_0^{-1/2}$ that $0<|a|<\varepsilon$. Then $W_g\ne0$, $\Theta\ne0$ and $0<B<1/2$; the tests
are integral above $S_b$ because every shift is a multiple of $M_0$; and the valuations of the
pole input under field 2′ give $v_p(B)\ge4$ on $S_0$ and a square reduced denominator, with
Lemma P(1) supplying $v_p(R_0)=2e_p$ and $v_p(t-1)=-e_p$ at $S_{\rm pole}$. Pole completeness
gives $\Phi(B)$.

## Depends on

- [The slope predicate](../multiplication/certificate/slope-predicate.md)
- [Slopes with poles at the old primes: field 2′](good-slope-ap.md)
- [Pole completeness](../main/pole-completeness.md)

## Proof depends on

- [Lemma P: a pole at an old prime is absorbed by the parameter $q$](lemma-p.md)
- [Weak approximation with residue targets](weak-approximation-targets.md)
- [Valuations of the pole input under field 2′](pole-input-valuations-ap.md)
- [Choice of the shift at a selected prime](../multiplication/completeness/shift-choice.md)
- [Integrality of the tests at the old primes](../multiplication/completeness/sb-integrality.md)
- [Precision of the tests at a selected prime](../multiplication/completeness/selected-prime-precision.md)
- [Positivity and smallness of the pole input](../multiplication/completeness/pole-input-positivity.md)
- [Properties of the multiplication constants](../multiplication/certificate/constants-properties.md)

## Sources

- [The modified completeness argument](../../sources/route-ap-locators.md#the-modified-completeness-argument)
- [Pole input of a completed slope](../../sources/multiplication-locators.md#pole-input-of-a-completed-slope)
