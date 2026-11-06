---
article_id: af_dda6bb3dae964f27f7d15d17
declaration: lemma
origin: cited
---

# Cantor pairing and unpairing

Let $\operatorname{pair}(a,b)=(a+b)(a+b+1)/2+b$ on $\mathbb N$ and
$\operatorname{encode}_5(c_0,c_1,c_2,c_3,c_4)=\operatorname{pair}(c_0,\operatorname{pair}(c_1,\operatorname{pair}(c_2,\operatorname{pair}(c_3,c_4))))$.

1. $\operatorname{pair}:\mathbb N^2\to\mathbb N$ is a bijection.
2. *Unpairing loop.* Starting from $s=0$ and $\mathrm{rem}=x$, while $s<\mathrm{rem}$ replace $s$ by
   $s+1$ and $\mathrm{rem}$ by $\mathrm{rem}-(s+1)$. The loop terminates, keeps
   $\mathrm{rem}=x-s(s+1)/2$, ends with $0\le\mathrm{rem}\le s$, and $(a,b)=(s-\mathrm{rem},\mathrm{rem})$ is
   the unique pair with $\operatorname{pair}(a,b)=x$.
3. $\operatorname{encode}_5:\mathbb N^5\to\mathbb N$ is a bijection; its inverse $\operatorname{decode}_5$ applies the
   unpairing loop four times, each time to the second component of the previous result.
4. For natural $a,b,t$: $2t=(a+b)(a+b+1)+2b$ iff $t=\operatorname{pair}(a,b)$.
5. For $\mathbf c\in\mathbb N^5$ and natural $t_0,t_1,t_2,t_3$, with $t_4=c_4$, the four equations
   $$2t_i=(c_i+t_{i+1})(c_i+t_{i+1}+1)+2t_{i+1}\qquad(0\le i<4)$$
   hold iff $t_3=\operatorname{pair}(c_3,c_4)$, $t_2=\operatorname{pair}(c_2,t_3)$, $t_1=\operatorname{pair}(c_1,t_2)$ and
   $t_0=\operatorname{pair}(c_0,t_1)$; in particular they force $t_0=\operatorname{encode}_5(\mathbf c)$ and have
   exactly one natural solution.

**Proof sketch.** With $T(s)=s(s+1)/2$, $\operatorname{pair}(a,b)$ lies in the triangular interval
$[T(a+b),T(a+b+1))$ at offset $b\le a+b$, which gives injectivity, and the loop finds the
interval containing $x$ (remainder decreasing, invariant preserved), which gives surjectivity
and item 2. Item 3 composes item 1 four times. Item 4: $2\operatorname{pair}(a,b)=(a+b)(a+b+1)+2b$
since $(a+b)(a+b+1)$ is even. Item 5 applies item 4 from $i=3$ down to $i=0$.

## Depends on

None.

## Sources

- [Section 10.3 unpairing wrapper](../../../../sources/compiler-translation-locators.md#section-103-unpairing-wrapper)
- [Section 10.1 Cantor wrapper](../../../../sources/compiler-translation-locators.md#section-101-cantor-wrapper-and-acceptance)
