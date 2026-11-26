---
article_id: af_b47d87e0687b086aa9b06a94
---

# The restricted converse (Theorem 5.3)

This chapter belongs to Elliot's route to the pole input. For a positive squarefree $\ell$ write
$E_\ell:y^2=x(x-\ell)(x+3\ell)$. The manuscript's Theorem 5.3, the restricted converse, states: for every
positive squarefree $\ell\equiv11\pmod{12}$,
$$\operatorname{corank}_{\mathbb Z_2}\mathrm{Sel}_{2^\infty}(E_\ell/\mathbb Q)=1\quad\Longrightarrow\quad\operatorname{ord}_{s=1}L(E_\ell,s)=1.$$
The curves have $c_4=208\ell^2$, $\Delta=2304\ell^6$ and $j=35152/9$; the $j$-invariant is not an integer, so
they have no complex multiplication.

- [Theorem 5.3: the restricted converse](restricted-converse.md)

## How the theorem is used

[Pole completeness from the restricted converse](../pole-completeness-from-5-3/README.md) applies
Theorem 5.3 to the two curves $E_n$ and $E_{n\theta}$ of the simultaneous 2-descent, after Lemma 5.4 has
turned their 2-Selmer dimension three into corank one. These are its only applications, which is why the
theorem is stated for this family only.

## The structure of the proof

The proof occupies Sections 7–9 and Appendices E–G of the manuscript, in its own dependency order:

1. **The opening reduction.** Selmer parity gives root number $-1$, so the analytic rank is odd and at least
   one. The rest of the proof shows that it is one.
2. **The even coefficient bound.** An Iwasawa scalar built from Kato's Euler system, with a weight $3/2$
   form from Waldspurger's theorem and a finite address argument on coefficient symbols, bounds the
   $2$-adic valuation of the central values above.
3. **The genus lower bound.** The explicit Gross–Zagier formula of Cai, Shu and Tian compares a genus point
   with a ring-class point. A uniform lower bound for an arithmetic coordinate, proved in Sections 8 and 9
   by a finite Heegner descent at $2$ and two ultrafilter limits, then bounds the genus index below.
4. **The odd normalization.** Weighted ternary theta forms on a definite quaternion algebra have
   coefficients that read genus points, and a visible coefficient gives a simple zero. If the odd symbol is a
   unit at the empty configuration, this already proves Theorem 5.3.
5. **The common family.** Otherwise a companion field $K=\mathbb Q(\sqrt k)$ with $L(E^{(k)},1)\ne0$ is fixed,
   $E/K$ has Selmer corank one, and the address networks produce a binary family of twists with controlled
   valuations.
6. **The determinant argument.** Over $K$, determinant clearing and a Boolean-degree count find an address
   whose corrected coordinate agrees with the base coordinate to high $2$-adic precision. If $L'(E/K,1)$
   vanished the base coordinate would be zero, contradicting the upper bound. So $L'(E/K,1)\ne0$, and with
   $L(E^{(k)},1)\ne0$ the curve $E$ has a simple zero.

The proof cites, among others, Kato's Euler system, Waldspurger's formula, Bump–Friedberg–Hoffstein,
Hoffstein–Luo, Nekovář's Selmer complexes, Kolyvagin's Theorem 1, the explicit Gross–Zagier formula of
Cai–Shu–Tian, Cornut–Jetchev and the parity theorem of Dokchitser–Dokchitser.

## The Lean

The Lean for this proof is on main, in three places:
- `ZInQKernel/Contrib/CloudB3RC53/`, the top layer, with its dependency graph `DAG.md`. That file lists every
  node of Sections 7–9 and Appendices E–G with its TeX lines and inputs; its status column dates from when
  each row was written, and the module headers are authoritative. Each numbered statement of
  Sections 7–9 and Appendices E–G has a page in this chapter.
- `ZInQKernel/Contrib/OneProof/RC/`, which wires the steps together and collects what remains.
- `ZInQKernel/Contrib/RC53Assist/`, supporting developments for individual steps.

Theorem 5.3 is reduced in Lean to the results it cites (some in consequence form) and one structure of
remaining hypotheses, which are not proved, so `ZInQ.OneProof.frozenTarget` still takes Theorem 5.3 as
one hypothesis, `hRC`.

- [The cited results](printed-results.md)
- [The remaining hypotheses](remaining-hypotheses.md)
- [The opening reduction: root number $-1$](opening-reduction.md)
- [Theorem 5.3 from the cited results and the remaining hypotheses](reduction.md)

## The proof, section by section

One page per numbered statement of the manuscript that a Lean declaration states. Each page says what
it assumes, how the Lean statement differs from the manuscript's, and whether the reduction of
Theorem 5.3 takes the statement from that page's theorem or from a field of the remaining hypotheses.

- [Section 7: the restricted converse and its dependency order](section-7/README.md)
- [Section 8: actual classes, local conditions and central comparison](section-8/README.md)
- [Section 9: the two limits and determinant transfer](section-9/README.md)
- [Appendix E: the even coefficient source](appendix-e/README.md)
- [Appendix F: the odd theta forms and their operators](appendix-f/README.md)
- [Appendix G: nonvanishing, normalization and the final family](appendix-g/README.md)
