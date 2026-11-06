---
article_id: af_5d08c2cbdf6ccdd63700fce2
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.Natural.NForm, ZInQ.Compiler.Natural.NM, ZInQ.Compiler.Natural.alpha, ZInQ.Compiler.Natural.power, ZInQ.Compiler.Natural.binomial, ZInQ.Compiler.Natural.orthogonal, ZInQ.Compiler.Natural.mask, ZInQ.Compiler.Natural.bitAnd
---

# Natural constructions and their macros

Polynomials live in $\mathbb Z[X_i:i\in\mathbb N]$ and formulas are those of the
specification chapter: atoms $a\doteq b$ and $\langle f\rangle$, conjunctions and disjunctions,
with the compilation $\kappa$ (difference, sum of squares, product; empty conjunction $0$,
empty disjunction $1$). A formula *holds naturally* at $x:\mathbb N\to\mathbb N$ when it holds
at the integer point $(x_i)_i$, atoms being read in $\mathbb Z$.

**Constructions.** A *natural construction with $k$ inputs* keeps a variable counter $c$,
initially $k$ (the inputs are $X_0,\dots,X_{k-1}$), and a list of *explicit variables*
(index and kind, the inputs first). It may

1. take a *fresh variable*: record $X_c$ as an explicit witness and increase $c$ by one;
2. in *hierarchical mode* over a fixed template $\mathcal P$ with three parameters and $79$
   witnesses (in this chapter always the power template), *call* $\mathcal P$ on
   polynomials $P,Q,R$: take the block $X_c,\dots,X_{c+78}$, increase $c$ by $79$, and
   return the atom $\langle\mathcal P[P,Q,R;c]\rangle$ (block variables are not explicit
   variables).

The result of a construction is a formula $\varphi$ and the final counter $v$; its
*polynomial* is $\kappa(\varphi)$, with no further squaring, and its node list is the
hash-consed node encoding of the specification chapter (an atom $a\doteq b$ becomes
$a+(-1)\cdot b$, sums and products of lists are left-nested, the empty sum is the constant
$0$ and the empty product the constant $1$, $n\cdot x$ is the product node of the constant
$n$ and $x$, $x^2$ is the product node $x\cdot x$, and structurally equal nodes and formulas
are created once).

**Gadgets and macros.** Each of the following is a construction step sequence returning a
formula; fresh variables are taken in the order listed, and the witnesses of inner gadgets
are taken when those gadgets are created, in the order in which they occur in the formula.

- $\mathrm{lt}(a,b)$: fresh $d$; the atom $b\doteq a+1+d$.
- $\mathrm{divides}(a,b)$: fresh $d$; the atom $b\doteq a\cdot d$.
- $\mathrm{congruent}(a,M,b)$: fresh $u,v$; the atom $a+Mu\doteq b+Mv$.
- $\mathrm{odd}(x)$: fresh $h$; the atom $x\doteq2h+1$.
- $\mathrm{alpha}(X,b,N)$: fresh $r,s,t,u,v,w,x,y$; the conjunction, in this order, of
  $\mathrm{lt}(3,b)$, $1+b\,u\,t\doteq u^2+t^2$, $1+b\,s\,r\doteq s^2+r^2$, $\mathrm{lt}(r,s)$,
  $\mathrm{divides}(u^2,s)$, $v+2r\doteq bs$, $\mathrm{congruent}(b,v,w)$,
  $\mathrm{congruent}(2,u,w)$, $\mathrm{lt}(2,w)$, $1+w\,x\,y\doteq x^2+y^2$,
  $\mathrm{lt}(2X,u)$, $\mathrm{lt}(2X,v)$, $\mathrm{congruent}(x,v,X)$, $\mathrm{lt}(2N,u)$,
  $\mathrm{congruent}(x,u,N)$.
- $\mathrm{power}(P,Q,R)$ in *flat mode*: fresh $b,m,a_0,a_1,a_2$; the disjunction of
  $\bigwedge(Q\doteq0,\ R\doteq0,\ P\doteq1)$, $\bigwedge(Q\doteq0,\ \mathrm{lt}(0,R),\ P\doteq0)$
  and $\bigwedge\bigl(\mathrm{lt}(0,Q),\ \mathrm{alpha}(a_0,Q+4,R+1),\ b\doteq a_0+Q^2+2,\
  m+Q^2+1\doteq bQ,\ \mathrm{lt}(P,m),\ \mathrm{alpha}(a_1,b,R),\ \mathrm{alpha}(a_2,b,R+1),\
  \mathrm{congruent}(P+ba_1,m,Qa_1+a_2)\bigr)$. In hierarchical mode, $\mathrm{power}(P,Q,R)$
  is the call of step 2.
- $\mathrm{binomial}(C,N,K)$: fresh $\beta,\tau,\pi,q,r$; the conjunction of
  $\mathrm{power}(\beta,2,N+1)$, $\mathrm{power}(\tau,\beta+1,N)$, $\mathrm{power}(\pi,\beta,K)$,
  $\mathrm{lt}(C,\beta)$, $\mathrm{lt}(r,\pi)$, $\tau\doteq\pi(\beta q+C)+r$.
- $\mathrm{orthogonal}(a,b)$: fresh $c$; $\bigwedge(\mathrm{binomial}(c,a+b,a),\mathrm{odd}(c))$.
- $\mathrm{mask}(a,b)$: fresh $c$; $\bigwedge(\mathrm{binomial}(c,b,a),\mathrm{odd}(c))$.
- $\mathrm{bitAnd}(z,x,y)$: fresh $a,b$; the conjunction of $x\doteq z+a$, $y\doteq z+b$,
  $\mathrm{orthogonal}(z,a)$, $\mathrm{orthogonal}(z,b)$, $\mathrm{orthogonal}(a,b)$.

This is a definition, a transcription of the compiler's builder. The intended meanings
are proved in the macro semantics; the arguments are always polynomials in variables
allocated before the macro, so a macro's own variables occur only inside its formula.

## Depends on

- [Formulas and their polynomial compilation](../../../syntax/language/formula-compilation.md)

## Sources

- [Compiler specification](../../../../sources/compiler-natural-locators.md#compiler-specification)
- [Compiler source](../../../../sources/compiler-natural-locators.md#compiler-source)
- [Section 10.2 alpha formula](../../../../sources/compiler-natural-locators.md#section-102-alpha-formula)
