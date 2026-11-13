---
article_id: af_9d77191e4615f3496925481c
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.Qsqrt.nrRealPlaces_of_neg, ZInQ.Progressions.Qsqrt.nrComplexPlaces_of_neg, ZInQ.Progressions.Qsqrt.nrRealPlaces_of_pos, ZInQ.Progressions.Qsqrt.nrComplexPlaces_of_pos, ZInQ.Progressions.Qsqrt.isTotallyReal, ZInQ.Progressions.Qsqrt.isTotallyComplex
---

# The signature of $\mathbb Q(\sqrt d)$

Let $d$ be an integer that is not the square of a rational number and $K=\mathbb Q(\sqrt d)$,
with $r_1$ real and $r_2$ complex places. If $d<0$, then $r_1=0$ and $r_2=1$, and $K$ is
totally complex; if $d>0$, then $r_1=2$ and $r_2=0$, and $K$ is totally real.

**Proof sketch.** Every embedding of $K$ into $\mathbb C$ sends $x+y\sqrt d$ to $x+y\beta$ with
$\beta^2=d$. The embeddings are real exactly when $d>0$; when $d<0$ none is real, and the two
complex conjugate embeddings form one complex place. In both cases $r_1+2r_2=2$.

## Depends on

- [The quadratic field $\mathbb Q(\sqrt d)$](quadratic-field.md)

## Sources

- [Marcus, Chapter 2](../../../sources/progressions-locators.md#marcus-chapter-2)
