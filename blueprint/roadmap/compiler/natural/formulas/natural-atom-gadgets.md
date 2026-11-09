---
article_id: af_57d71df8bedf7007961f009c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Natural.lt_gadget_iff, ZInQ.Compiler.Natural.dvd_gadget_iff, ZInQ.Compiler.Natural.congr_gadget_iff, ZInQ.Compiler.Natural.odd_gadget_iff
---

# The equational gadgets over the naturals

For all natural numbers $a,b,M,x$:

1. $(\exists d\in\mathbb N,\ b=a+1+d)\iff a<b$;
2. $(\exists d\in\mathbb N,\ b=ad)\iff a\mid b$;
3. $(\exists u,v\in\mathbb N,\ a+Mu=b+Mv)\iff a\equiv b\pmod M$, where for $M=0$ the right
   side means $a=b$;
4. $(\exists h\in\mathbb N,\ x=2h+1)\iff x$ is odd.

There is no exception at zero modulus: for $M=0$ the equation in item 3 says $a=b$.

**Proof sketch.** Items 1, 2 and 4 are the definitions of $<$, $\mid$ and oddness in
$\mathbb N$. Item 3: if $a\equiv b\pmod M$ with $M>0$, say $a\le b$, then $M\mid b-a$; take
$u=(b-a)/M$, $v=0$ (symmetrically if $b<a$). Conversely $a+Mu=b+Mv$ gives
$a\bmod M=b\bmod M$. For $M=0$ both sides say $a=b$.

## Depends on

None.

## Sources

- [Section 10.2 alpha formula](../../../../sources/compiler-natural-locators.md#section-102-alpha-formula)
- [Compiler specification](../../../../sources/compiler-natural-locators.md#compiler-specification)
