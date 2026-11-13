---
article_id: af_c6be9f76e8285425161078ad
open_statements: allowed
---

# Z is Diophantine in Q

This blueprint formalizes Theorem 1.1 of the 11/5 manuscript *ℤ is Diophantine in ℚ*:
an integer polynomial in 292,890,231,905 variables, of degree below $2\uparrow\uparrow 7$
and with coefficients below $2\uparrow\uparrow 8$, whose rational zero projection to the
first variable is exactly $\mathbb Z$.

The [main theorem](main/main-theorem.md) proves it from five explicitly stated hypotheses, whose
proofs lie far outside current formal libraries: the minimal form of the six-contact height estimate
(the one instance of the manuscript's Theorem 4.1 that the proof uses; not a published theorem, its
proof combines refereed theorems and exact computations with new arguments, the manuscript's and
this project's, reviewed only by AI models), and four statements about L-series of elliptic curves
over $\mathbb Q$. Three of the four are textbook theorems: the positive-rank half of Gross–Zagier,
the functional equation of the L-series of the congruent number curves $C_d$ for squarefree
$d\equiv5\pmod8$, with conductor $32d^2$ and root number $-1$, stated on the strip
$0<\operatorname{Re}s<2$, and Hecke's continuation of $L(C_d,s)$ to an entire function for every
$d\ne0$. No original source of Hecke's continuation was read, and the original source of the
conductor and the functional equation has not been read in full. The fourth is a consequence of
Tian–Yuan–Zhang's Theorem 3.5(2) in one reading of its genus sums, reading A: for squarefree
$d\equiv5\pmod8$, if $L(C_d,s)$ vanishes to order at least $2$ at $s=1$, two genus sums of class
numbers are even. No refereed text found by the project's literature search, which AI agents carried
out, states reading A explicitly; Tian–Yuan–Zhang's introductory theorem with the same parity
criteria, read literally, is false; and their proof passes through their Proposition 3.4, whose
proof is only sketched in the arXiv version; the journal's proof was not assessed on this point. A
new argument written for this project, Proposition N, reviewed twice by AI models and never by a
human, derives reading A from unambiguous results of that version; its derivation from a restatement
of those results is proved here, but no proof checks that the restatement matches the paper, and only AI models have compared it with the paper, and it is supporting evidence, not a hypothesis of the theorem. From the four statements
the proof derives a certified rank hypothesis for congruent number curves, CR₃; the theorem holds
under the height hypothesis and CR₃ alone, and, in the form closest to the manuscript, under those
two and the manuscript's twenty-two-prime pattern. The height hypothesis may also be assumed in its
$j$-form, a bound on the height of the Hauptmodul value (not a published theorem) from which the
minimal form is proved. The manuscript's other inputs are proved. Pole completeness follows from the
certified rank hypothesis for a variant of the manuscript's pole polynomial, and also from positive
rank of the congruent number curves that hypothesis covers, or of only the two curves the descent
constructs; the bound for the prime catalogue follows from an effective Dirichlet theorem; the
Mordell–Weil theorem for the generator curve, first stated as a hypothesis, is proved; and the
twenty-two-prime pattern is not needed: a change in the completeness proof, route AP, uses long
arithmetic progressions of good primes instead, which come from Szemerédi's theorem in the primes
(from a Lean proof of the Green–Tao theorem) and a density theorem for those primes. The passage
from positive rank to points in every Selmer class rests on the complete 2-descent and the
Mordell–Weil theorem for these curves, and Smith's row-5b identity and Rédei's formula let the
hypothesis be stated in Tian, Yuan and Zhang's terms; all four are proved. Everything else is
proved, with every finite computation checked by the Lean kernel.

## Chapters

- [The main theorem and its hypotheses](main/README.md)
- [The finite specification of the polynomial](syntax/README.md)
- [The elliptic model of integer indices](model/README.md)
- [Multiplication and the finite false-triple guard](multiplication/README.md)
- [Exact precision computation and polynomial compilation](compiler/README.md)
- [Assembly and the ordinary-value relation](assembly/README.md)
- [The cutoff and polynomial size](size/README.md)
- [Primes in arithmetic progressions](progressions/README.md)
- [Pole completeness from certified rank (Route K)](route-k/README.md)
- [Long progressions of good primes replace the prime pattern (route AP)](route-ap/README.md)
- [Szemerédi's theorem in the primes (Green–Tao)](green-tao/README.md)
- [The density of good slope primes (Proposition D)](density/README.md)
- [The explicit system is the 2-Selmer group (Proposition 0)](selmer/README.md)
- [The row-5b determinant](rank-5b/README.md)
- [Rédei's formula for the 4-rank of class groups](redei/README.md)
- [The rank hypothesis as positive rank](rank/README.md)
