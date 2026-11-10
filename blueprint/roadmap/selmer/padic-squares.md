---
article_id: af_41c386d85ab89aa202fa4b5a
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Selmer.isSquare_padic_iff, ZInQ.RouteK.Selmer.isSquare_two_adic_iff, ZInQ.RouteK.Selmer.unitPart, ZInQ.RouteK.Selmer.unitPart_spec, ZInQ.RouteK.Selmer.isSquare_of_norm_sub_one_lt, ZInQ.RouteK.Selmer.sqEq_add_of_norm_lt, ZInQ.RouteK.Selmer.sqEq_add_of_norm_le_two_adic, ZInQ.RouteK.Selmer.isSquare_intCast_div_of_residue, ZInQ.RouteK.Selmer.isSquare_ratCast_of_residue, ZInQ.RouteK.Selmer.isSquare_intCast_div_two_adic, ZInQ.RouteK.Selmer.isSquare_ratCast_two_adic
---

# Squares in the p-adic numbers

Let $p$ be a prime and $x\in\mathbb Q_p$ nonzero, $x=p^ku$ with $u$ a unit of $\mathbb Z_p$.

1. *(SQ)* For odd $p$, $x$ is a square if and only if $k$ is even and the residue of $u$ in
   $\mathbb F_p$ is a square. For $p=2$, $x$ is a square if and only if $k$ is even and
   $u\equiv1\pmod8$.
2. *(Hensel)* Every $u\in\mathbb Q_p$ with $|u-1|<|2|^2$ is a square.
3. *(P)* For odd $p$ and $|y|<|x|$, $x+y\equiv x$ modulo nonzero squares; for $p=2$ the same holds
   when $|y|\le|x|/8$.
4. *(RT)* For odd $p$, a quotient $m/n$ of integers prime to $p$ with $mn$ a square modulo $p$ is
   a square in $\mathbb Q_p$, and so is a rational number whose numerator and denominator are prime
   to $p$ and whose product is a square modulo $p$. For $p=2$, $m/n$ with $n$ odd and
   $m\equiv n\pmod8$ is a square in $\mathbb Q_2$, and so is a rational number with odd denominator
   and numerator congruent to the denominator modulo $8$.

**Proof sketch.** (2) is Hensel's lemma for $X^2-u$ at $1$: $|F(1)|=|u-1|<|F'(1)|^2=|2|^2$. A square
has even valuation; a unit square root of a unit reduces modulo $p$, resp. an odd square is
$\equiv1\pmod8$; conversely a unit with square residue is a square by Hensel's lemma at a lift of
the residue square root (odd $p$), resp. by (2) at $1$ ($p=2$, since $|u-1|\le2^{-3}<2^{-2}$). This
gives (1). (3) applies (2) to $1+y/x$. (4) applies (1) to the unit $m/n$.

## Depends on

- [The 2-coverings of a congruent number curve](coverings.md)

## Sources

- [Squares in the p-adic numbers](../../sources/selmer-locators.md#squares-in-the-p-adic-numbers)
