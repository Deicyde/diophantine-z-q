---
article_id: af_0c38b320bd18901e180fd198
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.IR.cantor_pair_props, ZInQ.Compiler.IR.cantor_unpair_props, ZInQ.Compiler.IR.cantor_pairing_equation, ZInQ.Compiler.IR.pairing_system_iff, ZInQ.Compiler.IR.pairing_system_encode
---

# Unique Cantor unpairing

1. For all natural $a,b$: $2\operatorname{pair}(a,b)=(a+b)(a+b+1)+2b$, and
   $\frac{(a+b)(a+b+1)}2\le\operatorname{pair}(a,b)<\frac{(a+b+1)(a+b+2)}2$ (triangular
   intervals). Hence $\operatorname{pair}$ is a bijection $\mathbb N^2\to\mathbb N$.
2. $\operatorname{unpair}(\operatorname{pair}(a,b))=(a,b)$ and
   $\operatorname{pair}(\operatorname{unpair}(x))=x$; likewise
   $\operatorname{dec}_5\circ\operatorname{enc}_5=\mathrm{id}$ and $\operatorname{enc}_5\circ\operatorname{dec}_5=\mathrm{id}$.
3. For natural $a,b,t$: $2t-(a+b)(a+b+1)-2b=0$ (in $\mathbb Z$) if and only if
   $t=\operatorname{pair}(a,b)$.
4. Consequently, for $c\in\mathbb N^5$ and $t_4=c_4$, the four pairing equations
   $$2t_i=(c_i+t_{i+1})(c_i+t_{i+1}+1)+2t_{i+1}\qquad(0\le i<4)$$
   have exactly one natural solution $(t_0,t_1,t_2,t_3)$, namely
   $t_i=\operatorname{pair}(c_i,t_{i+1})$, and then $t_0=\operatorname{enc}_5(c)$.

**Proof sketch.** (1) $(a+b)(a+b+1)$ is even; the interval bounds follow from $0\le b\le a+b$,
and disjointness of consecutive intervals gives injectivity (equal pairs have equal
$a+b$, then equal $b$); surjectivity from (2). (2) The loop invariant
$\operatorname{pair}(\mathrm{loop}(s,\varrho))=s(s+1)/2+\varrho$, by strong induction on
$\varrho$; at exit $0\le\varrho\le s$, so $b=\varrho$ and $a=s-b$ lie on diagonal $s$. (3) Divide
by two. (4) Solve from $i=3$ down to $i=0$ with (3).

## Depends on

- [Cantor pairing and its decoder](cantor-pairing.md)

## Sources

- [Section 10.1 wrapper specialization](../../../../sources/compiler-natural-locators.md#section-101-wrapper-specialization)
- [Section 10.3 unpairing and wrapper](../../../../sources/compiler-natural-locators.md#section-103-unpairing-and-wrapper)
