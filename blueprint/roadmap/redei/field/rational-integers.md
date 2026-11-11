---
article_id: af_0f0a0eed165af3f84e639c3a
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.exists_int_of_coe_eq_algebraMap, ZInQ.RouteK.Redei.intCast_injective, ZInQ.RouteK.Redei.intCast_dvd_intCast_iff, ZInQ.RouteK.Redei.isUnit_intCast_iff, ZInQ.RouteK.Redei.rat_unit_eq, ZInQ.RouteK.Redei.natCast_dvd_natCast_iff, ZInQ.RouteK.Redei.span_natCast_eq_span_natCast_iff
---

# Rational integers in the ring of integers

Let $n\ge1$ and let $\mathcal O$ be the ring of integers of $K=\mathbb Q(\sqrt{-n})$. Then
$\mathcal O\cap\mathbb Q=\mathbb Z$: a rational number that lies in $\mathcal O$ is an integer.
The map $\mathbb Z\to\mathcal O$ is injective, and:

- for integers $a,b$, $a$ divides $b$ in $\mathcal O$ if and only if $a$ divides $b$ in
  $\mathbb Z$, and likewise for natural numbers;
- an integer $m$ is a unit of $\mathcal O$ if and only if $m=\pm1$, and a unit of $\mathcal O$
  that is a rational number is $\pm1$;
- for natural numbers $a,b$, $a\mathcal O=b\mathcal O$ if and only if $a=b$.

**Proof sketch.** A rational number that is integral over $\mathbb Z$ is an integer, because
$\mathbb Z$ is integrally closed. If $b=ay$ in $\mathcal O$ with $a\ne0$, then $y=b/a$ is a
rational number in $\mathcal O$, hence an integer; if $a=0$, then $b=0$ by injectivity. An
integer $m$ is a unit exactly when $m\mid1$ in $\mathcal O$, that is, in $\mathbb Z$. Finally
$a\mathcal O=b\mathcal O$ means $a\mid b$ and $b\mid a$ in $\mathcal O$, hence in $\mathbb N$, so
$a=b$.

## Depends on

- [The genus class number](../genus-class-number.md)

## Sources

- [Step 1: the field](../../../sources/redei-locators.md#step-1-the-field)
