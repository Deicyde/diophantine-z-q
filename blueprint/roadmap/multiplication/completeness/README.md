---
article_id: af_264464403ceb2da5ad9eaf75
---

# Completeness: true triples are accepted

Completeness says that the multiplication template accepts
$(\iota(a),\iota(b),\iota(ab))$ for all integers $a,b$. It uses the slope representation, a
consequence of the twenty-two-prime pattern 22P, to choose the slopes, pole completeness PC to
supply the pole witnesses, and the generator certificate (hence Mordell-Weil) through the
fixed-scalar and guard semantics. It does not use the six-contact estimate.

## Slopes from the prime pattern

Each of the nine integral homogeneous quantities of a true triple is written as a sum of
three slopes $u_j/v$ whose twenty-two linear forms take values $\pm kp$ with $k$ in the fixed
catalogue multipliers and $p$ a large good prime. Each slope then has bounded valuations at
the old primes $S_b$ and at most six odd contact primes outside $S_b$, each of exact
valuation one and good.

- [Slopes of an integer from the prime pattern](pattern-slopes.md)

The rest of the proof uses only the conclusion with no lower bound on the contact primes:
every integer is a sum of three good slopes. The two-slope pattern gives this too, with the
slopes $u/v$, $A+10-u/v$ and the constant $-10$.

- [The slope representation](slope-representation.md)
- [The twenty-two-prime pattern gives the slope representation](slope-representation-from-pattern.md)
- [The two-slope pattern gives the slope representation](slope-representation-from-two-slope.md)

Neither pattern is needed: [route AP](../../route-ap/README.md) weakens the condition at the old
primes so that a slope may have a pole there when $F(t)>0$, absorbs such a pole in the slope
certificate, and obtains the weakened representation from long progressions of good slope primes.

## The witnesses of a test group

Each odd contact prime of a slope gets its own private test group. At such a prime, with
reduced group orders $d_1,d_2$, $\gcd(d_1,d_2)=4$, the shift $h$ is chosen with
$h\equiv0\pmod{\operatorname{lcm}(M_0,d_1)}$ and $h\equiv c_*\pmod{d_2}$, and $U_i=[n_i]H$.
Then $H,U_i$ lie in the formal group at one place and $V_0,V_i$ at the conjugate place, and
the four $L$-tests are congruent to $n_i-n_i$ and $n_1n_2-n_3=0$ modulo $p^{28}$. Groups not
assigned to a prime use $h=2c_*$; the manuscript leaves them unspecified.

- [Choice of the shift at a selected prime](shift-choice.md)
- [Precision of the tests at a selected prime](selected-prime-precision.md)

Because every shift is a multiple of $M_0$, all eight points of every group lie in the small
formal subgroup at the old primes, so every test is integral there.

- [Integrality of the tests at the old primes](sb-integrality.md)

## The pole input

Weak approximation chooses $q$ small at $S_b$, integral at the selected primes, and close to
a real root of $1-R_0q^2$ without equality, with $\eta$ chosen to make $R_0>0$. In both real
embeddings every $W_g$ is at least $1$, so $\Theta\in(0,12]$ and the pole input
$R/\Theta^2$ is positive and, for $a$ small, below $1/2$. At $S_b$ the clearing exponents of
$\ell_0$ give $v_p(R/\Theta^2)\ge103C_p+8\ge4$; at a selected prime the trace residues give
valuation one; elsewhere the valuation is even. These are exactly the hypotheses of pole
completeness, including all nonzero guards.

- [Weak approximation for the parameter $q$](weak-approximation.md)
- [Positivity and smallness of the pole input](pole-input-positivity.md)
- [Valuations of the pole input of a completed slope](pole-input-valuations.md)
- [Completeness of the slope certificate for a true triple](slope-completeness.md)

## Conclusion

With the scalar graphs, the twenty-seven slope certificates and the guard, which passes
every true triple, the template accepts every true triple.

- [Completeness of the multiplication template](completeness.md)
