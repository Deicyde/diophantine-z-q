---
article_id: af_af027210b01bb05cf98b4f05
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.GlueSweep.Even.E10_of_waldspurgerCor2_of_bcdt, ZInQ.Manuscript.RC.Even.E10_of_waldspurgerCor2
---

# (E.10): Waldspurger's ratio of squared coefficients

Assume Waldspurger's Corollaire 2 in weight $3/2$ (`WaldspurgerCor2`, GLUE: a restatement of Purkait's
Corollary 5.2, Waldspurger's print unread; not an input of the reduction of Theorem 5.3) and Theorem A
of Breuil, Conrad, Diamond and Taylor (one of [the cited results](../printed-results.md)). The absolute
convergence of $L(E,s)$ on $\operatorname{Re}s>3/2$, also a hypothesis of the Lean theorem, is proved.

Let $E/\mathbb Q$ be an elliptic curve with a normalization $L_*$ of its twisted central values, let
$4\mid N$, $\sigma=\pm1$, and let $\psi,\eta$ be Dirichlet characters modulo $N$ with $\eta=\psi\chi_{-\sigma}$
on integers prime to $N$. Let $g$ be a cusp form of weight $3/2$, level $N$ and character $\psi$ with
$T(p^2)g=\eta(p)a_p(E)g$ for every prime $p\nmid N$. Let $D_0,D$ be positive, squarefree, prime to $N$
and in one unit squareclass at every prime dividing $N$, with $a_g(D_0)\ne0$ and $L_*(\sigma D_0)\ne0$.
Then
$$\Bigl(\frac{a_g(D)}{a_g(D_0)}\Bigr)^2=\psi(D)\psi(D_0)^{-1}\,\frac{L_*(\sigma D)}{L_*(\sigma D_0)}.\tag{E.10}$$

The manuscript writes the identity with $\sqrt D\,L(E^{(\sigma D)},1)$ and $\sqrt{D_0}\,L(E^{(\sigma D_0)},1)$
and then notes that the period cancels; Lean states the quotient of $L_*$-values directly. The
manuscript's (E.10) is multiplicative, $a_f(D)^2=\psi(D/D_0)\cdots a_f(D_0)^2$, and needs no
$a_f(D_0)\ne0$; Lean divides by $a_g(D_0)$ and adds that hypothesis. The manuscript applies the
corollary to its reference form and checks the corollary's hypotheses at its level; in Lean the
corollary is stated for every form in the full good-Hecke eigenspace at every level $N$ with $4\mid N$,
without Purkait's hypotheses that the level $M_\varphi$ of the newform divides $N/2$, that (H1) holds,
and that the form is orthogonal to the unary theta series. The manuscript argues (H1) and the
orthogonality for its space; in Lean all three are dropped from the assumed statement.

**Proof sketch.** The corollary, in its printed order, gives
$a_g(D_0)^2L(E^{(\sigma D)},1)\,\psi(D)\psi(D_0)^{-1}\sqrt D=a_g(D)^2L(E^{(\sigma D_0)},1)\sqrt{D_0}$. Since
$\sigma D$ and $\sigma D_0$ have the same sign, $L_*$ uses the same period at both, and dividing by the
nonzero reference value gives (E.10). The entire continuations of the twisted $L$-functions come from
modularity.

In the Lean proof of Theorem 5.3 this theorem is not used.

## Depends on

- [The cited results](../printed-results.md)

## Sources

- [Appendix E](../../../sources/manuscript.md#appendix-e)
