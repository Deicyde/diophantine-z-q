---
article_id: af_e4f9b68fbf3164e279d44472
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.Precision.decide5
---

# The exact decision program

The *decision program* is the total function $\mathrm{decide}:\mathbb N^5\to\{\mathrm{true},\mathrm{false}\}$
computed by the following steps on $c\in\mathbb N^5$; every quantity is an integer, an element
of $\mathbb Z[s]$ (a pair of integers) or a natural number, and every test is exact.

1. Decode $(n,\kappa,a,l,j)$. Return false unless $n\notin\mathcal C$, $\kappa\ne0$, $a\ge1$,
   $l\ge1$ and $j=na$.
2. For $k\in\{l,a,j\}$ compute the Jacobian representative $(X_k,Y_k,Z_k)=\mathrm{mul}(k)$.
   Return false if some $Z_k=0$ or some $Y_k=0$.
3. For $k\in\{l,a,j\}$ put $\nu_k=-X_kZ_k\bar Y_k\in\mathbb Z[s]$ and $N_k=Y_k\bar Y_k\in\mathbb Z$, so
   that $z_k=\nu_k/N_k$, with $N_k\ne0$. Write $\nu_l=p+p's$ and put $U=|p|+|p'|$, $V=|N_l|$, so
   that $\epsilon_l=U/V$ with $U,V>0$.
4. Put $\delta=N_j\operatorname N(\nu_a)\in\mathbb Z\setminus\{0\}$ and let $\theta$ be the rational
   component of $\nu_j\bar\nu_aN_a\in\mathbb Z[s]$, so that $r(a,j)=\theta/\delta$. Return false
   unless $|\theta-n\delta|\cdot V<U\cdot|\delta|$.
5. Put $L=\lfloor(V-1)/(4U)\rfloor$. Return false if $L=0$. Otherwise, with
   $M=|\kappa F(n)|$, compute $\beta=\mathrm{cmul}_L(\langle e_A\rangle_L,\mathrm{cpow}_L(\sigma_L(M),24))$
   and run the division-by-four loop from $L$ for $\beta$ steps; return true if and only if
   the final value is at least $1$.

This is a definition. It follows the description of the reference program S21: exact
quadratic-field arithmetic on integer pairs, capped integer operations, a halving scalar
loop, a precision loop dividing by four and a bounded factorial iteration. The source S21
itself is not available in this repository, so this program is specified here rather than
transcribed.

## Depends on

- [The signed encoding of integers](signed-encoding.md)
- [Scalar multiplication by halving](jacobian-scalar-multiplication.md)
- [The capped precision test](capped-height-test.md)

## Sources

- [Section 10 decision predicate](../../../../sources/compiler-natural-locators.md#section-10-decision-predicate)
- [Section 10 reference program and IR](../../../../sources/compiler-natural-locators.md#section-10-reference-program-and-ir)
- [Section 10.3 precision IR](../../../../sources/compiler-natural-locators.md#section-103-precision-ir)
- [Appendix B sources](../../../../sources/compiler-natural-locators.md#appendix-b-sources)
