# Locators for the Proposition D chapter

Proposition D is not in the manuscript. The manuscript's Proposition 6.2 (the twenty-two-prime
pattern) is replaced by route AP, whose input needs long arithmetic progressions of good slope
primes; these come from Szemerédi's theorem in the primes once the good slope primes are known to
have positive relative density. That density statement is Proposition D. Its proof is written in
the project-authored research note `docs/research/pd-paper.md` of this repository (a specification
written for this project, refereed by a model run in `docs/research/rv-pd-paper.md`, not a
published source). Section numbers below are those of `pd-paper.md`. The Selberg sieve is vendored
from PrimeNumberTheoremAnd (last section).

## The target statements

`docs/research/pd-paper.md` §0: the relative upper density statement for the good slope primes
(Proposition D, weak form), Theorem D (a positive lower Dirichlet density) and the route through
Proposition 5.3; the full natural density of `nt-22p.md` §2.2 is not needed.

## Character sums

`docs/research/pd-paper.md` §1.2: Lemmas 1.1 (point count), 1.2 (scaling), 1.3 (shifted
products), 1.4 (Jacobsthal's identity, with evenness) and 1.5 (divisibility by four through the
involution $x\mapsto-D^2/x$).

## The description of good primes

`docs/research/pd-paper.md` §1.3: Proposition 1.6, the description of the good slope primes in the
class $p\equiv1\pmod 8$, $(p/7)=-1$ through $c_p=\varphi_p(1)/2$.

## The residue set

`docs/research/pd-paper.md` §2.1 (the sets $C_L$, $T_L$, $G^*_L$, Lemma 2.1 and remark 3, the
residue set $A_L$ and $\delta_L$) and §2.3 (the Frobenius conditions are congruences).

## The main term

`docs/research/pd-paper.md` §3.2: Lemma 3.1, the lower bound for the Dirichlet series of $C_L$ from
Dirichlet's theorem in residue classes (Mathlib's lower bound for the von Mangoldt series of a
residue class near $s=1$).

## The lattice count

`docs/research/pd-paper.md` §4.2: Proposition 4.1, the primes bad at a large $\ell$, counted by
lattice points.

## The sieve

`docs/research/pd-paper.md` §4.3 (the sieve set-up, inequality (4.1), Lemmas 4.3 and 4.4), §4.4
(the Selberg bound and the error terms) and §4.5 (Lemma 4.5, the lower bound for the Selberg sum,
with Claims A and B). The Lean proof uses a fixed box $[-K,K]\times[-K-1,K]$ and the constant
$A=14402$ in place of the note's interval $I_2$ and $A_1=16003$.

## Assembly

`docs/research/pd-paper.md` §5: Lemma 5.1 (prime tail), Lemma 5.2 (Abel summation),
Proposition 5.3 (Dirichlet density gives upper natural density) and Theorem D.

## The vendored Selberg sieve

The Selberg sieve bound is the theorem `selberg_bound_simple` of the PrimeNumberTheoremAnd project
(https://github.com/AlexKontorovich/PrimeNumberTheoremAnd, files
`Mathlib/NumberTheory/Sieve/{AuxResults,Basic,Selberg,SelbergBounds}.lean`, tag `v4.35.0`, by
Arend Mellendijk), built on Mathlib's `BoundingSieve` and `SelbergSieve` structures. It is vendored
in this repository under the Apache License 2.0 with only its import lines changed; the license is
`ZInQKernel/Sieve/LICENSE`. For the mathematics see
H. Halberstam and H.-E. Richert, *Sieve Methods*, Academic Press, 1974, Chapter 3.
