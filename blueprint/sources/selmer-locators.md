# Locators for the Proposition 0 chapter

Proposition 0 is not in the manuscript. It identifies the explicit linear system of the Route K
chapter with the 2-Selmer group of the congruent number curve $C_d:y^2=x^3-d^2x$, and so lets the
certified rank hypothesis be stated on the Selmer group itself. The mathematics is written in the
project-authored research note `docs/research/nt-prop0.md` of this repository, a specification
written for this project, not a published source; it refines `docs/research/descent-alt.md` §4.1.
The standard facts it relies on without proof (the connecting map of the complete 2-descent) and
the deep theorems behind the hypothesis CR₃^Sel are cited at the end.

## Coverings

`docs/research/nt-prop0.md` §1.1: the 2-covering $D_{a,b}$ of $C_d$, its x-form, and the remarks
(Inv) and (Tor) of §2 used at every place.

## The Kummer map

`docs/research/nt-prop0.md` §1.2, Lemma 1.2: a covering is soluble over a field of characteristic
not $2$ if and only if its pair of classes lies in the image of the Kummer map.

## The Selmer group

`docs/research/nt-prop0.md` §1.3: the definition of $\mathrm{Sel}_2(C_d)$ by local solubility of the
coverings, and the three reasons it agrees with the textbook definition.

## The hypothesis in the literature's form

`docs/research/nt-prop0.md` §1.4: the hypothesis CR₃^Sel, what it says in terms of
$Ш(C_d)[2]$ and the rank, and the elementary derivation of CR₃ from CR₃^Sel and Proposition 0
(steps 1–5).

## Squares in the p-adic numbers

`docs/research/nt-prop0.md` §2.1, Lemma SQ: square classes of $\mathbb Q_p$ for odd $p$ and for
$p=2$, the perturbation rule (P) and the residue test (RT).

## The real place

`docs/research/nt-prop0.md` §2.2, Lemma ∞.

## Odd primes not dividing d

`docs/research/nt-prop0.md` §2.3: Lemmas G1 and G2, Lemma Q, Jacobsthal's bound (Lemma J), the count
of Step 2 and the small primes below $29$.

## Odd primes dividing d

`docs/research/nt-prop0.md` §2.4, Lemma B.

## The place 2

`docs/research/nt-prop0.md` §2.5, Lemma T and its table of rational witnesses.

## From classes to the system

`docs/research/nt-prop0.md` §2.6: the local class conditions as the rows E1, E2, (R) and (D) of
$\Sigma(\mathcal C_d)$.

## Proposition 0

`docs/research/nt-prop0.md` §2.7: Proposition 0 in the form proved in Lean and the count corollary.

## Silverman

J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Springer (2009), Proposition X.1.4
(the connecting map of the complete 2-descent for a curve with full 2-torsion) and §X.4 (the
Selmer group). Used, not formalized, to identify the Selmer group defined here with the textbook one.

## Deep inputs of CR3Sel

The theorems behind CR₃^Sel are those named for CR₃: Tian–Yuan–Zhang, *Genus periods, genus points
and congruent number problem*, Asian J. Math. 21 (2017), Theorem 3.5 and the argument of the proof
of Theorem 3.5(2), as completed by Proposition N (`docs/research/nt-tyz.md` §4), with Gross–Zagier,
Invent. Math. 84 (1986), over an auxiliary imaginary quadratic field (Bump–Friedberg–Hoffstein;
`docs/research/cr3-trust.md` §1, D2); see `docs/research/cr3-trust.md`. As an alternative that is not
needed (`docs/research/nt-tyz.md` §5.1): Kriz, *Supersingular main conjectures, Sylvester's
conjecture and Goldfeld's conjecture* (arXiv:2002.04767), Theorems 10.13 and 10.17(2), with the corank
lemma (the Cassels–Tate pairing on $Ш/Ш_{\rm div}$ is nondegenerate and alternating: Cassels,
J. reine angew. Math. 211 (1962); the manuscript cites Poonen–Stoll, Ann. of Math. 150 (1999)).
