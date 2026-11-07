---
article_id: af_496f44c864138e067b934eb0
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Mult.clearing_arithmetic, ZInQ.Mult.clearing_identities
---

# The clearing inequalities

For every $B\in\{1,4\}$ and every $v\in\{0,1,2\}$, with $C=14B$, $D=51C$ and $E=52C+v+4$,
$$2E-C-2D>v\qquad\text{and}\qquad 2E-C-2v=103C+8\ge4 .$$
Moreover $52\cdot56+4=2916$, $52\cdot14+4=732$, $v_2(12)=2$, $v_3(12)=1$ and $v_p(12)=0$ for
every prime $p\ge5$.

This is a finite computation (six cases of linear integer arithmetic). With $B=B_p$ and
$v=v_p(12)$ it gives, for every $p\in S_b$, $2E_p-C_p-2D_p>v_p(12)$ and
$2E_p-C_p-2v_p(12)=103C_p+8\ge4$, and identifies $E_p$ with the exponent of $p$ in $\ell_0$.

**Proof sketch.** $2E-C-2D=104C+2v+8-C-102C=C+2v+8>v$, and $2E-C-2v=103C+8\ge111$. The
remaining items are evaluations.

## Depends on

None.

## Sources

- [Fixed local clearing](../../../sources/multiplication-locators.md#fixed-local-clearing)
- [Pole input of a completed slope](../../../sources/multiplication-locators.md#pole-input-of-a-completed-slope)
- [Six-contact finite checks](../../../sources/multiplication-locators.md#six-contact-finite-checks)
