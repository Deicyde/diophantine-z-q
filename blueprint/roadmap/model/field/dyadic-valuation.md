---
article_id: af_960e0383740cd6108b391665
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.vS_sq_add_one, ZInQ.val_s_sq_add_delta_sq
---

# A dyadic valuation computation

1. Let $A,B\in\mathbb Q$ with $v_2(A)=0$ and $v_2(B)\ge0$ (so $A+Bs$ is a unit at the prime
   $(s)$). Then $v_s\bigl((A+Bs)^2+1\bigr)=2$ if $v_2(B)\ge1$, and $=3$ if $v_2(B)=0$.
2. Consequently, for $a,b\in\mathbb Z[s]$ with $s\nmid a$ and $s\nmid b$,
   $$v_s\bigl(a^2+\delta^2b^2\bigr)\in\{2,3\}.$$

**Proof sketch.** (1) $(A+Bs)^2+1=(A^2+2B^2+1)+2ABs$. A $2$-adic unit has
$A^2\equiv1\pmod 8$. If $B$ is even, the rational part is $\equiv2\pmod8$, of $2$-adic
valuation $1$, while $v_2(2AB)\ge2$; by the valuation formula at $(s)$ the valuation is
$\min(2,\ge5)=2$. If $B$ is a $2$-adic unit, the rational part is $\equiv4\pmod8$ (valuation
$2$) and $v_2(2AB)=1$, giving $\min(4,3)=3$. (2) $\delta b$ is prime to $s$ since
$v_s(\delta)=0$. Put $w=a/(\delta b)=a\,\overline{\delta b}/\operatorname N(\delta b)$; here
$\operatorname N(\delta b)$ is odd and $a\,\overline{\delta b}\in\mathbb Z[s]$ is prime to $s$, so
its rational component is odd. Hence $w=A+Bs$ as in (1), and
$a^2+\delta^2b^2=(\delta b)^2(w^2+1)$ with $v_s((\delta b)^2)=0$.

## Depends on

- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](special-primes.md)

## Sources

- [Duplication bounds](../../../sources/model-locators.md#duplication-bounds)
