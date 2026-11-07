---
article_id: af_4b765c1343582fef4fbabb8c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.psi_uniform, ZInQ.Size.guard_uniform, ZInQ.Size.const_uniform
---

# Uniform bounds for the finite constructors

Let $B\ge2^{20}$ be an integer.

1. For $n\in\mathbb Z$ with $|n|+1\le B$ and $c\in\{0,1\}$:
   $\deg\Psi_{n,c}\le B^4$ and $\|\Psi_{n,c}\|_1\le2^{B^8}$.
2. For an integer $T$ with $0\le T\le B-1$: $\deg G_T\le B^4$ and $\|G_T\|_1\le2^{B^8}$.
3. For an integer $c$ with $|c|\le B-1$, the constant polynomial $c$ (the value of a
   $\mathrm{fixed}$ node) has degree $0\le B^4$ and norm $|c|\le2^{B^8}$.

**Proof sketch.** (1) $2(|n|+1)^3\le2B^3\le B^4$ and $101(|n|+1)^3\le101B^3\le B^8$. (2)
$16(T+1)^3\le16B^3\le B^4$ and $2^{39}(T+1)^6\le2^{39}B^6\le B^8$ because $B^2\ge2^{40}$. (3) is
immediate.

The manuscript states these bounds with $B_*=T+1$; the companion proof uses the maximum of
$2^{20}$, $T+1$ and one plus every occurring constant and index, which is shown to equal
$T+1$.

## Depends on

- [Normalized division polynomials and their components](../../syntax/division-polynomials.md)
- [The finite false-triple product](../../syntax/constants/guard-product.md)
- [Coefficient norms and degrees](l1-norm.md)

## Proof depends on

- [Size of the division polynomials](division-polynomial-size.md)
- [Size of the guard polynomial](guard-size.md)

## Sources

- [Section 12.1 constructor bounds](../../../sources/size-locators.md#section-121-constructor-bounds)
- [Companion size proof](../../../sources/size-locators.md#companion-size-proof)
