---
article_id: af_85e6d577c7de0fa238d647e3
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
---

# The main theorem by Elliot's route

Assume the minimal height hypothesis and pole completeness. Then the target statement holds: some
integer polynomial in $292{,}890{,}231{,}905$ variables, of degree below $2\uparrow\uparrow7$ and with
coefficients below $2\uparrow\uparrow8$, has rational zero projection to its first variable exactly
$\mathbb Z$.

The two hypotheses are two of the manuscript's inputs.

- **The minimal height hypothesis** is the one instance $S=S_{\rm mul}$, $R=D$ of the six-contact
  height estimate (the manuscript's Theorem 4.1) that the proof uses. The proof of that estimate
  combines refereed theorems and exact computations with new arguments, the manuscript's and this
  project's, reviewed only by AI models; it is not a published theorem.
- **Pole completeness** is the manuscript's Theorem 5.2, for the manuscript's own pole polynomial.
  For every input $B$ that Theorem 5.2 allows (square reduced denominator, $0<B<1/2$, and $v_p(B)\ge4$ at
  $p=2,3,5,7,13$), that polynomial has a rational zero. A zero puts two rational points
  on curves $y^2=x(x-\ell)(x+3\ell)$.

**The other inputs.** The manuscript assembles Theorem 1.1 from six inputs (Lemma 1.2). The other four
are proved here:
- the generator statement, outright, through the Mordell–Weil theorem for $E$ over $K_0$;
- the compiler semantics and the literal specification with its size bounds, outright;
- multiplication, from the two hypotheses: its soundness uses the minimal height hypothesis, and its
  completeness uses pole completeness.

Two of these proofs depart from the manuscript:
- The manuscript's twenty-two-prime pattern (Proposition 6.2) is not used. [Route AP](../route-ap/README.md)
  proves the completeness of the multiplication template from long arithmetic progressions of good
  slope primes. Those come from Szemerédi's theorem in the primes, proved from a Lean proof of the
  Green–Tao theorem, and from the positive relative upper density of the good slope primes (Proposition D).
- The catalogue bound is proved with the cutoff $2^{W^8}$ in place of the manuscript's $2^{W^3}$, by an
  effective Dirichlet theorem. The size bounds of the target hold with this larger cutoff.

**Where pole completeness comes from.** The manuscript derives Theorem 5.2 from its restricted converse
theorem (Theorem 5.3) by a simultaneous 2-descent (Section 5.1). Theorem 5.3 says: for every positive
squarefree $\ell\equiv11\pmod{12}$, if the $2^\infty$-Selmer group of $y^2=x(x-\ell)(x+3\ell)$ has
$\mathbb Z_2$-corank $1$, then its L-function vanishes to order exactly $1$ at $s=1$. That derivation is
formalized (fork issue #83), from Theorem 5.3, the Cassels–Tate pairing on the curves $E_\ell$ and
Silverman's rank-one implication
([pole completeness from the restricted converse](../pole-completeness-from-5-3/README.md)). This theorem
keeps pole completeness as its hypothesis, and `ZInQ.OneProof.frozenTarget` combines the two. The proof
of Theorem 5.3 itself (Sections 7–9 and Appendices E–G) uses Kato's Euler system, Waldspurger's formula,
Bump–Friedberg–Hoffstein, Nekovář's Selmer complexes and Gross–Zagier–Kolyvagin. In Lean it is reduced
to the results it cites (some in consequence form) and one structure of remaining hypotheses, which are
not proved ([the restricted converse](../restricted-converse/README.md)), so the single proof still takes
Theorem 5.3 as a hypothesis.

**The open statements.** `ZInQ.OneProof.frozenTarget` is this theorem with the minimal height hypothesis
replaced by the statements from the literature that imply it
([the height-decomposition chapter](../height-decomposition/README.md); the current list is
`docs/one-proof/OPEN.md`), and pole completeness replaced by its three inputs: Theorem 5.3, the
Cassels–Tate pairing on the curves $E_\ell$ and Silverman's rank-one implication (the hypotheses `hRC`,
`hCT` and `hRank`).

**The other headline.** The congruent-number route proves the same target statement with a different
pole input:
- a different pole polynomial, whose curves are the congruent number curves $y^2=x(x-\ell)(x+\ell)$;
- a proof of its pole completeness from the certified rank hypothesis CR₃;
- a derivation of CR₃ from statements about L-series: Tian–Yuan–Zhang's Theorem 3.5(2) in reading A and
  the positive-rank half of Gross–Zagier, with Hecke's continuation and the functional equation, which
  are proved.

Its headline is [the main theorem by the congruent-number route](main-theorem-reading-a-gross-zagier.md).
The project used that route here until fork issue #77. Its Lean is kept at the tag `route-k-final` and
pinned upstream in elliotglazer/diophantine-z-q, and nasqret/z-in-q-lean builds on it; the project note
`docs/research/rs-pole.md` records why it was adopted.

**Proof sketch.** Route AP needs the progression hypothesis 22P_AP, which follows from Szemerédi's
theorem in the primes and Proposition D, both proved. Route AP then gives the slope representation
under field 2′. With it, the minimal height hypothesis and pole completeness, the assembly lemma under
field 2′ gives the target.

## Depends on

- [The target statement](../statements/frozen-target.md)
- [The minimal height hypothesis](../multiplication/certificate/six-contact-min.md)
- [Pole completeness](../statements/pole-completeness.md)

## Proof depends on

- [The assembly lemma under field 2′](../route-ap/assembly-ap.md)
- [22P_AP from Green–Tao and Proposition D](../route-ap/good-prime-ap-from-green-tao.md)
- [Szemerédi's theorem in the primes holds](../green-tao/dense-theorem.md)
- [Proposition D: the good slope primes have positive relative density](../density/proposition-d.md)

## Sources

- [Theorem 1.1 and Lemma 1.2](../../sources/manuscript.md#theorem-11)
- [Theorem 4.1](../../sources/manuscript.md#theorem-41)
- [Theorem 5.2](../../sources/manuscript.md#theorem-52)
- [Proposition 6.2](../../sources/manuscript.md#proposition-62)
- [The trust statement for H](../../sources/height-locators.md#the-trust-statement-for-h)
