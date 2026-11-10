# Locators for the route AP chapter

Route AP is not in the manuscript. It replaces the twenty-two-prime pattern of Proposition 6.2
by long arithmetic progressions of good slope primes, through a change in the completeness proof
of Section 6 that leaves the polynomial unchanged. The mathematics is written in the
project-authored research note `docs/research/nt-22p.md` of this repository, a specification
written for this project, not a published source; it was checked by three model referee runs and
a Lean-statement audit (`docs/research/rv-nt22p-*.md`, `docs/research/aud-ap.md`). The published
theorem it uses is cited at the end.

## Lemma P

`docs/research/nt-22p.md` §3.2, "Lemma P (pole absorption)": the hypotheses (a slope $t=u/v$ in
lowest terms with $e=v_\ell(v)\ge1$, $e\ge3$ at $\ell=2$, and the seven numbers $u-cv$,
$c\in\mathcal C\cup\{1\}$, prime to $\ell$), parts (1)–(3) and their proofs. The numerical check
of the same section (30 samples) motivates the condition $e\ge3$ at $2$.

## The modified completeness argument

`docs/research/nt-22p.md` §3.2, "The modified completeness argument": field 2′ replacing field 2
of the slope conditions, the choice of $q$ in the ball of Lemma P(2) at the primes where field 2′
uses its second alternative, and the valuation bookkeeping at the other primes, which is the
manuscript's (Section 6, the completeness of the slope certificate).

## The progression form

`docs/research/nt-22p.md` §3.3: the statement 22P_AP, Proposition AP and its proof (the slopes
$u/v$, $A+10-u/v$ and $-10$ from a progression of length $K_A+1$), with the remarks on why field
2′ cannot be avoided.

## Green–Tao implies 22P_AP

`docs/research/nt-22p.md` §3.4: Szemerédi's theorem in the primes applied to the good slope primes
above $\max S_b$, which have positive relative density by Proposition D (§2 of the same note,
proved in `docs/research/pd-paper.md`).

## Green–Tao 2008

B. Green and T. Tao, *The primes contain arbitrarily long arithmetic progressions*, Ann. of Math.
167 (2008), 481–547, Theorem 1.2 (Szemerédi's theorem in the primes).
