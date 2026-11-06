---
article_id: af_9cb49d02fce99e2aefcb9729
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.AlphaPower.alphaMat_pow, ZInQ.AlphaPower.alphaZ_quadratic, ZInQ.AlphaPower.alphaZ_addition
---

# Matrix powers and the quadratic identity

Let $b$ be a natural number, $U_n=\alpha_b(n)$ and $M=M_b$. Then:

1. for every $n\ge1$,
   $$M^n=\begin{pmatrix}U_{n+1}&-U_n\\U_n&-U_{n-1}\end{pmatrix},\qquad\det M^n=1;$$
2. for every $n\in\mathbb N$, $U_n^2+U_{n+1}^2-b\,U_nU_{n+1}=1$; equivalently, for $n\ge1$,
   $U_n^2-bU_nU_{n-1}+U_{n-1}^2=1$;
3. for every $n$, $U_n$ and $U_{n+1}$ are coprime in $\mathbb Z$ and are not both even;
4. (addition formula) for all $m,n\in\mathbb N$, $U_{m+n+1}=U_{m+1}U_{n+1}-U_mU_n$.

**Proof sketch.** Item 1 by induction on $n$ from $M^{n+1}=M\cdot M^n$ and the recurrence;
$\det M=1$. The determinant reads $U_n^2-U_{n+1}U_{n-1}=1$, and substituting
$U_{n+1}=bU_n-U_{n-1}$ gives item 2 (which can also be proved directly by induction, the
left side being invariant under $(U_n,U_{n+1})\mapsto(U_{n+1},bU_{n+1}-U_n)$). Item 3:
item 2 is the Bezout relation $U_n(U_n-bU_{n+1})+U_{n+1}\cdot U_{n+1}=1$, and reducing it
modulo $2$ excludes two even terms. Item 4 by two-step induction on $n$, or from the
lower-left entry of $M^{m+n}=M^mM^n$.

## Depends on

- [The alpha sequence](alpha-sequence.md)

## Sources

- [Section 10.2 alpha recurrence](../../../../sources/compiler-natural-locators.md#section-102-alpha-recurrence)
