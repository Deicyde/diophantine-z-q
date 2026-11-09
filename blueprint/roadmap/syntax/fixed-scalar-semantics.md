---
article_id: af_80899a526cd564b32f084333
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Syntax.scalarTemplate_rel_iff_pointCode, ZInQ.Syntax.scalarTemplate_rel_iff_iota
---

# Semantics of the fixed-scalar templates

Let $e$ be a fixed integer expression with
$n=\mathrm{val}(e)\ge1$, let $p$ be the code of a point $P\in2E(K_0)$ and $r\in\mathbb Q^5$.
Then
$$\mathrm{Rel}_{S_e}(p,r)\iff r\text{ is the code of }[n]P .$$
In particular, on codes of $2E(K_0)=\mathbb ZP_0$, $\mathrm{Rel}_{S_e}(\iota(a),r)\iff r=\iota(na)$.

**Proof sketch.** By the compilation theorem the polynomial vanishes exactly when one of
the two branches holds. If $P=O$ then $p_0=1$, the second branch fails, and the first holds
exactly when $r=O=[n]O$. If $P\ne O$ the first branch fails since $p_0=0$. As
$2E(K_0)=\mathbb ZP_0$ with $P_0$ of infinite order, $[n]P\ne O$, so by the
multiplication formulas $\psi_n(P)\ne0$ and
$[n]P=(x-\psi_{n+1}\psi_{n-1}/\psi_n^2,\ \psi_{2n}/(2\psi_n^4))$, where the components of $\psi_k(P)$
are $\Psi_{k,0},\Psi_{k,1}$ evaluated at the coordinates of $p$. By the pair arithmetic, the
inverse witness exists exactly because $\psi_n(P)\ne0$, and the two pair equations, after
division by $\psi_n^2\ne0$ and $2\psi_n^4\ne0$, say that $x(r)$ and $y(r)$ are the coordinates of
$[n]P$, while $r_0=0$ says $r$ is affine. Clearing these denominators is reversible.

## Depends on

- [The fixed-scalar templates](templates/template-fixed-scalar.md)
- [The codes of multiples of the generator](../model/point-codes.md)

## Proof depends on

- [Division polynomials compute multiples](../model/field/division-polynomial-multiples.md)
- [The generator](../model/generator.md)
- [Pair arithmetic represents the quadratic field](field-pair-arithmetic.md)
- [Sums of squares and products over the rationals](sum-of-squares-semantics.md)
- [Template construction from formulas](language/builder-soundness.md)

## Sources

- [Section 2.2](../../sources/syntax-locators.md#section-22-division-polynomials)
- [Section 10.4](../../sources/syntax-locators.md#section-10-translation)
