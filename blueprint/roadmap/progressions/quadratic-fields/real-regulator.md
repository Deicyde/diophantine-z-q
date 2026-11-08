---
article_id: af_62005a99b7d7ae05446f0c9c
declaration: theorem
origin: background
---

# The regulator of a real quadratic field

Let $d>1$ be a squarefree integer and $K=\mathbb Q(\sqrt d)$. The regulator of $K$
satisfies
$$R_K\ge\log\frac{1+\sqrt5}{2}.$$

**Proof sketch.** By the signature, the unit rank is $1$, and $R_K=|\log|\sigma(\varepsilon_0)||$
for a fundamental unit $\varepsilon_0$ and either real embedding $\sigma$. Replacing
$\varepsilon_0$ by $\pm\varepsilon_0^{\pm1}$, let $\varepsilon=\sigma(\varepsilon_0)>1$, and
let $\varepsilon'$ be its conjugate. Then $\varepsilon\varepsilon'=N=\pm1$ and
$a=\varepsilon+\varepsilon'$ is a rational integer, the trace of an algebraic integer. If
$N=-1$, then $a=\varepsilon-1/\varepsilon>0$, so $a\ge1$; since $t\mapsto t-1/t$ is
increasing and equals $1$ at $\phi=(1+\sqrt5)/2$, $\varepsilon\ge\phi$. If $N=1$, then
$a=\varepsilon+1/\varepsilon>2$, so $a\ge3$ and $\varepsilon\ge(3+\sqrt5)/2=\phi^2>\phi$. In
both cases $R_K=\log\varepsilon\ge\log\phi$.

## Depends on

- [The quadratic field $\mathbb Q(\sqrt d)$](quadratic-field.md)

## Proof depends on

- [The signature of $\mathbb Q(\sqrt d)$](signature.md)

## Sources

- [Marcus, Chapter 5](../../../sources/progressions-locators.md#marcus-chapter-5)
