---
article_id: af_9eceba7b573f0f61e2a43c75
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Syntax.exists_mul_eq_one_iff, ZInQ.Syntax.exists_mul_pairNorm_eq_one_iff
---

# Inverse witnesses

Inverses are expressed by equations $uv=1$, never by partial division.

1. For $a\in\mathbb Q$: $a\ne0\iff\exists w\in\mathbb Q,\ aw=1$, and then $w=1/a$.
2. For $a_0,a_1\in\mathbb Q$ and $s=\sqrt2$: $a_0+a_1s\ne0\iff a_0^2-2a_1^2\ne0\iff
   \exists w\in\mathbb Q,\ (a_0^2-2a_1^2)\,w=1$.

Consequently the gadget $\mathrm{NZ}(a)$ is satisfiable by a choice of its fresh variable
exactly when $a\ne0$, and $\mathrm{NZ}(a_0^2-2a_1^2)$ exactly when the pair $(a_0,a_1)$ is
not $(0,0)$.

**Proof sketch.** Part 1 is the field structure of $\mathbb Q$. For part 2, if
$a_0^2=2a_1^2$ with $a_1\ne0$ then $(a_0/a_1)^2=2$, contradicting the irrationality of
$\sqrt2$; so $a_0^2-2a_1^2=0$ forces $a_1=0$ and then $a_0=0$. Conversely $(0,0)$ has norm
$0$. Then apply part 1 to the norm. Since $1,s$ are linearly independent over $\mathbb Q$,
$a_0+a_1s=0$ exactly when $a_0=a_1=0$.

## Depends on

- [Formulas and their polynomial compilation](language/formula-compilation.md)

## Sources

- [Section 2.1](../../sources/syntax-locators.md#section-21-literal-operations)
