---
article_id: af_07b61cae8c50eaaa6ef18746
declaration: def
origin: cited
statement: formalized
lean: ZInQ.PoleCompleteness, ZInQ.polePoly, ZInQ.PoleSoluble, ZInQ.poleS0
---

# Pole completeness

For $B\in\mathbb Q$ and witnesses $b_0,\ldots,b_5,e,z,r_1,r_2,w\in\mathbb Q$ put
$m=(1-2b_0)(1+b_1)(1+2b_2)(1+4b_3)(1+6b_4)(1+12b_5)$, $A=mB$, $H=A(A-B^2)$,
$T_1=A(A-e)(A+3e)$, $T_2=A(Az^2-eH)(Az^2+3eH)$ and
$$Q_{\rm pole}=B\Bigl(\sum_{i=0}^5(b_i^2-b_i)^2+(eHzw-1)^2+(r_1^2-T_1)^2+(r_2^2-T_2)^2\Bigr).$$
Write $\Phi(B)$ when $Q_{\rm pole}$ has a rational zero with input $B$. For $B\ne0$, a zero makes
every $b_i$ equal to $0$ or $1$, so $m$ is a signed divisor of $2730$, and it gives $eHz\ne0$. It puts
$(A,r_1)$ on the curve $y^2=x(x-e)(x+3e)$ and $(Az^2,zr_2)$ on $y^2=x(x-eH)(x+3eH)$.

Pole completeness is the assertion that every rational $B$ with square reduced denominator,
$0<B<1/2$ and $v_p(B)\ge4$ for every $p\in S_0=\{2,3,5,7,13\}$ satisfies $\Phi(B)$.

This is the manuscript's Theorem 5.2, for the manuscript's polynomial, and it is a hypothesis of
[the main theorem](main-theorem.md). The manuscript derives it from its restricted converse theorem
(Theorem 5.3) by a simultaneous 2-descent (Section 5.1). Write $E_\ell:y^2=x(x-\ell)(x+3\ell)$. For an
input $B$ as above, the descent works in four steps:
- It chooses a positive divisor $m$ of $2730$ so that $A=mB$ is a square at $2$ and lies in a nonsquare
  unit square class at $3$. Let $\beta$ and $\theta$ be the positive squarefree parts of $A$ and $H$.
- It builds a positive squarefree $n$ with $n\theta$ squarefree and $n,n\theta\equiv11\pmod{12}$, such that
  the 2-Selmer groups of $E_n$ and $E_{n\theta}$ have dimension $3$ and contain the Kummer class $(\beta,1)$,
  in the coordinates $(x+3\ell,x-\ell)$.
- Lemma 5.4 turns dimension $3$ into Selmer corank $1$, so the restricted converse gives analytic rank $1$.
  Lemma 5.5 (modularity with Kolyvagin's theorem, which rests on Gross–Zagier) then gives rank $1$ and a
  finite Tate–Shafarevich group for both curves.
- So the 2-part of the Tate–Shafarevich group vanishes, and the class $(\beta,1)$ comes from a rational
  point on each curve. Rescaled to abscissas $A$ and $Az^2$, those points give the witnesses.

That derivation is formalized here (fork issue #83), with Lemma 5.4 proved from the Cassels–Tate
pairing on the curves $E_\ell$. It leaves four inputs: Theorem 5.3; that pairing, as Poonen and Stoll restate
Cassels' theorem; the modularity theorem of Breuil, Conrad, Diamond and Taylor; and a consequence of
Kolyvagin's theorem. Theorem 5.3 is the manuscript's own theorem, proved in its Sections 7–9 and
Appendices E–G. The [pole obstruction](../multiplication/pole-obstruction.md),
the manuscript's Lemma 5.1, is proved for this polynomial.

Until fork issues #76 and #77 the project used another polynomial here, with the factors $A+e$ and $Az^2+eH$
and the congruent number curves $y^2=x(x-\ell)(x+\ell)$. Its pole completeness was proved from the
certified rank hypothesis CR₃ (Route K). That route is retired; its Lean is kept at the tag
`route-k-final`.

## Depends on

None.

## Sources

- [Theorem 5.2](../../sources/manuscript.md#theorem-52)
- [Pole predicate](../../sources/multiplication-locators.md#pole-predicate)
