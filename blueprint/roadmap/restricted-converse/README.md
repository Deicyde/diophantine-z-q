# The restricted converse (Theorem 5.3)

For a positive squarefree $\ell$ write $E_\ell:y^2=x(x-\ell)(x+3\ell)$. The manuscript's Theorem 5.3,
the restricted converse, states:

> For every positive squarefree $\ell\equiv11\pmod{12}$,
> $$\operatorname{corank}_{\mathbb Z_2}\mathrm{Sel}_{2^\infty}(E_\ell/\mathbb Q)=1\quad\Longrightarrow\quad\operatorname{ord}_{s=1}L(E_\ell,s)=1.$$

The curves have $c_4=208\ell^2$, $\Delta=2304\ell^6$ and $j=35152/9$; the $j$-invariant is not an
integer, so they have no complex multiplication, and they differ from the CM generator curve of the
elliptic model.

- [Theorem 5.3: the restricted converse](restricted-converse.md)

## How the theorem is used

Section 5.1 of the manuscript derives [pole completeness](../main/pole-completeness.md), its Theorem 5.2,
from Theorem 5.3 by a simultaneous 2-descent. The descent builds positive squarefree $n$ and $n\theta$,
both $\equiv11\pmod{12}$, whose curves $E_n$ and $E_{n\theta}$ have 2-Selmer groups of dimension three
containing a prescribed Kummer class. Lemma 5.4 (dimension three gives corank one, through the
Cassels–Tate pairing) puts both curves in the hypothesis of Theorem 5.3; Theorem 5.3 gives analytic rank
one; and Lemma 5.5, the forward theorem (modularity with Kolyvagin's Theorem 1), gives rank one and a
finite Tate–Shafarevich group. These are the only two applications of Theorem 5.3, which is why the
theorem is stated for this family only. Its proof fixes one $\ell$; its constants may depend on that
curve and are not uniform in $\ell$.

## The structure of the proof

The proof occupies Sections 7–9, about 4,000 lines, and Appendices E–G, about 4,100 lines. It follows the
manuscript's own dependency order (L1816–1823):

1. **The opening reduction.** Selmer parity gives root number $-1$, so the analytic rank is odd and at least
   one. The rest of the proof shows that it is one.
2. **The even coefficient bound.** One Iwasawa scalar built from Kato's Euler system, for every binary family
   of quadratic twists at once, has central valuation $v_2L_*(h)-2\omega(h)-s(h)+O(1)$ (3.2). With a weight
   $3/2$ form from Waldspurger's theorem and a finite address argument on coefficient symbols, this bounds
   $v_2L_*$ above at partitionable parameters (3.3).
3. **The genus lower bound.** The explicit Gross–Zagier formula of Cai–Shu–Tian, applied twice, compares a
   genus point with a ring-class point (3.4). A uniform lower bound for an arithmetic coordinate, proved in
   Sections 8–9 by a finite Heegner descent at $2$ and two ultrafilter limits (5.5), then gives the
   lower bound (3.6) for the genus index.
4. **The odd normalization.** Weighted ternary theta forms on a definite quaternion algebra have
   coefficients that read genus points (3.8), (O.7). Their visibility statement (O.8) turns a visible
   coefficient into a simple zero. The lower bound fixes a minimum depth $\delta_o$. If the odd symbol is a
   unit at the empty configuration, (O.8) at $D=1$ already proves Theorem 5.3.
5. **The common family.** Otherwise a companion field $K=\mathbb Q(\sqrt k)$ with $L(E^{(k)},1)\ne0$ is fixed,
   $E/K$ has Selmer corank one, and the address networks produce a binary family $h_x$ of twists with
   controlled valuations at every $x\ne0$ (3.9).
6. **The determinant argument.** Over the fixed field $K$, determinant clearing and a Boolean-degree count
   find an address $x\ne0$ whose corrected coordinate agrees with the base coordinate to high $2$-adic
   precision (5.11). If $L'(E/K,1)$ vanished the base coordinate would be zero, contradicting the upper
   bound at $x$. So $L'(E/K,1)\ne0$, and with $L(E^{(k)},1)\ne0$ the curve $E$ has a simple zero.

The articles record each appendix result with the statement it proves, and fall into four parts, listed in
the manuscript's order of Sections 7, 8 and 9; the third part supplies the uniform bound (5.5) that the genus
bound in the second part uses.

- [The opening reduction](opening-reduction.md)
- [The coefficient sources (Sections 7.1, 7.2, 7.5; Appendices E and F)](coefficient-sources/README.md)
- [Coefficient symbols, the genus bound and the common family (Sections 7.3, 7.4, 7.6; Appendix G)](common-family/README.md)
- [Heegner classes and the uniform bound (Sections 8 and 9.1–9.4)](heegner-limits/README.md)
- [The fixed-field determinant argument (Sections 9.5 and 9.6)](determinant/README.md)

## The literature it rests on

The proof cites the following statements, in the form and with the theorem numbers the manuscript gives.

- **Kato**, *$p$-adic Hodge theory and values of zeta functions of modular forms*, Astérisque 295 (2004):
  Theorem 13.4(2), with the nonzero-class input of Theorem 13.5(2), for Euler-system divisibility at the
  height-one primes not containing $2$ (part (3) is not used); Theorems 6.6 and 9.7 for explicit reciprocity;
  Proposition 8.12 for the norm relations. Corollary 14.3 also gives the rank-zero case of Lemma 5.5.
- **Waldspurger**, *Sur les coefficients de Fourier des formes modulaires de poids demi-entier*, J. Math.
  Pures Appl. 60 (1981): Proposition 18 and Corollary 2 (pp. 483–484), comparing squarefree coefficients of
  a weight $3/2$ form for two indices in one $2$-adic squareclass; Proposition 2. Also *Correspondances de
  Shimura*, ICM 1983, Theorem 1 and Proposition 1.
- **Ramsey**, *Geometric and $p$-adic modular forms of half-integral weight*, Ann. Inst. Fourier 56 (2006):
  Definition 3.1, Theorem 4.2 and Remark 4.4, an algebraic model of weight $3/2$ forms, used over fields.
- **Bump–Friedberg–Hoffstein**, Invent. Math. 102 (1990), clauses (i) and (ii), pp. 543–544: in a filter of
  odd root number a twist with a simple zero, and in an even one a negative fundamental discriminant with
  nonzero central value.
- **Hoffstein–Luo**, Math. Res. Lett. 4 (1997), p. 436: fundamental discriminants with nonzero central value,
  at most four prime factors, and an arbitrary finite splitting set.
- **Nekovář**, *Selmer complexes*, Astérisque 310 (2006): Selmer complexes and their duality (Sections 5.1–5.4,
  6.2–6.4, Theorem 6.3.4), support change (Proposition 7.8.8(ii)), Shapiro and transfer (Sections 8.1, 8.6).
- **Kolyvagin**, *On the Mordell–Weil group and the Shafarevich–Tate group of modular elliptic curves*, MPIM
  preprint MPI/90-69 (1990), Theorem 1, pp. 4–5, with Theorems 3–5: through Lemma 5.5, analytic rank
  $r\le1$ gives rank $r$ and a finite Tate–Shafarevich group. It is used at known nonzero central values and
  known simple zeros.
- **Cai–Shu–Tian**, *Explicit Gross–Zagier and Waldspurger formulae*, Algebra Number Theory 8 (2014),
  Theorem 1.1: the height of an unaveraged Heegner or ring-class point equals $L'(E/K,\chi,1)$ up to a fixed
  constant and the factor $c\sqrt{|\operatorname{disc}K|}$. It is used quantitatively in (3.4) and
  qualitatively (height zero exactly when the derivative vanishes) for the witness, in (O.8) and at the base.
- **Cornut–Jetchev**, *Liftings of reduction maps for quaternion algebras*, 2010 preprint, Theorem 3.1 (with
  Corollary 3.2, Sections 3.1–3.3, 3.6, 4.9–4.10 and Lemma 2.1(ii)): reduction of CM points at an inert
  prime as a bijection onto oriented optimal embeddings, for (O.7).
- **Dokchitser–Dokchitser**, *Root numbers and parity of ranks of elliptic curves*, J. Reine Angew. Math. 658
  (2011), Theorem 1.8: $2^\infty$-Selmer parity, so corank one gives root number $-1$.

Gross–Zagier enters only through Theorem 1.1 of Cai–Shu–Tian and through Kolyvagin's Theorem 1, as
cited; the manuscript's table of applications also names Gross–Zagier beside Kolyvagin for forward
finiteness (L6803). No argument or citation of Tian–Yuan–Zhang occurs in
the proof. The proof also cites Breuil–Conrad–Diamond–Taylor (Theorem A), Milne's *Modular functions and
modular forms* (Theorem 11.19) and *Arithmetic duality theorems*, Serre's open image theorem, Desjardins
(Proposition 3.3), Cai–Chen–Liu (Theorem 2.15), Elkik, Edixhoven, Weil (Acta Math. 111), Voight, Carayol
(Theorem A), Casselman and Jetchev–Kane.

## Status

None of this proof is formalized in Lean. The project's main theorem takes Theorem 5.3 as a hypothesis,
stated over the corank of the genuine $2^\infty$-Selmer group.

## Sources

- [The 11/5 manuscript](../../sources/manuscript.md#theorem-52): `hyp:RC` (L1005–1011), `sec:rc`, `sec:arithmetic`
  and `sec:limits` (L1760–5744), `app:even-source`, `app:odd-source` and `app:endpoints` (L6825–10935)

## Manuscript check

The whole proof was mapped step by step by AI review: Sections 7–9 with 43 arithmetic checks by script,
and Appendices E–G with 15 more. Four ranges were then checked line by line: the finite Heegner descent and
the uniform bound (5.5) (46 checks by script, some with negative controls), the paired functional and the
residual bound (5.1) (46 checks, each with a negative control), and the theta forms and the comparison (O.7)
of Appendix F (101 checks with negative controls, and a global model). No check found a false step, and
none found a circularity: the order of choices is consistent (L9981–9994, L10151–10256, L10814–10861).
Small gaps of presentation were filled; each article records its own. Not yet checked: every cited theorem
against its print, since no print was read; in particular whether Theorem 1.1 of Cai–Shu–Tian carries no
factor depending on the conductor beyond $c\sqrt{|\operatorname{disc}K|}$, which (3.4) needs, the exact
statement of Kolyvagin's Theorem 1 (both $r=0$ and $r=1$, and its meaning of "modular"), and the hypotheses
of Cornut–Jetchev's Theorem 3.1. The manuscript cites Kolyvagin as an MPIM preprint, attributes to its
Theorems 3–5 the auxiliary field and the nonzero Heegner height (whether these are the preprint's own or
quoted from Bump–Friedberg–Hoffstein, Murty–Murty and Gross–Zagier is not yet checked), and its
bibliography entry for Cai–Shu–Tian gives no issue or pages. The largest constructions of the
appendices were read for structure only and are not yet checked line by line: the uniform Kato class
(K1)–(K3) with its normalization (K14), the positive complex and calibration (E.3)–(E.9), the coefficient
rules (O.9)–(O.12) and the address networks (G.1a). Some TeX comments in these sections (L2832–2833, L3923,
L4975, L7428, L7789–7790, L8222–8223, L8407) record how the file was assembled; they are not typeset.
