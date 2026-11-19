# Pole completeness from the restricted converse

Section 5.1 of the manuscript (L1019-1122) derives [pole completeness](../main/pole-completeness.md), its
Theorem 5.2, from the restricted converse, Theorem 5.3, by a simultaneous 2-descent on the curves
$E_\ell:y^2=x(x-\ell)(x+3\ell)$.

- For an input $B$ it chooses a positive divisor $m$ of $2730$ so that $A=mB$ is a square at $2$ and lies in a
  nonsquare unit square class at $3$, and takes the positive squarefree representatives $\beta$ and $\theta$ of
  $A$ and $H=A(A-B^2)$.
- It builds a positive squarefree $n$, with $n\theta$ squarefree and $n,n\theta\equiv11\pmod{12}$, such that the
  2-Selmer groups of $E_n$ and $E_{n\theta}$ have dimension $3$ and contain the Kummer class $(\beta,1)$ in the
  coordinates $(x+3\ell,x-\ell)$. The local equations at the primes of the support and at $3$ leave at most
  eight classes, and the class $(\beta,1)$ is checked to be local at every place, $2$ included.
- Lemma 5.4 turns dimension $3$ into $2^\infty$-Selmer corank $1$ through the Cassels–Tate pairing, so
  Theorem 5.3 gives analytic rank $1$; Lemma 5.5 (modularity with Kolyvagin's theorem) then gives rank $1$ and
  a finite Tate–Shafarevich group for both curves.
- So the 2-part of the Tate–Shafarevich group vanishes, the class $(\beta,1)$ comes from a rational point on
  each curve, and rescaling the two points gives the eleven witnesses of the pole polynomial.

This derivation is formalized from Theorem 5.3, the Cassels–Tate pairing on the curves $E_\ell$ (from which
Lemma 5.4 is proved) and consequences of the modularity theorem and of Kolyvagin's Theorem 1 (the inputs of
Lemma 5.5); proving Theorem 5.3 itself in Lean is fork issue #83. [The main
theorem](../main/main-theorem.md) keeps pole completeness as its hypothesis. The pages below state proved facts
that this formalization uses: the square-class relation, squarefree representatives of square classes, squares
in $\mathbb Q_p$, and the count of $A/2A$ for a finitely generated abelian group whose 2-torsion has four
elements and which has an element of infinite order.

- [Square classes in a field](square-classes.md)
- [Squarefree representatives of rational square classes](squarefree-representatives.md)
- [Squares in the p-adic numbers](padic-squares.md)
- [Counting $A/2A$](counting.md)
