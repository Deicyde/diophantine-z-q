---
article_id: af_a94e934a85998bca9239cff7
---

# Fixed constants and the guard product

A fixed integer expression is built from literals, references, arithmetic, powers,
maxima, factorials, the prime catalogue and the least formal multiple. Its value is a
constant, never a quantified witness, and the astronomical values are never computed.

- [The prime catalogue](prime-catalogue.md)
- [The least formal multiple](least-formal-multiple.md)
- [Fixed integer expressions](fixed-integer-expressions.md)

The specification binds eighteen named constants, from the primorial $P_s$ through the
guard cutoff $T$; only the two primorial literals are checked numerically.

- [The prescribed fixed constants](fixed-constants.md)
- [Decimal values of the primorial constants](primorial-literal.md)

The constructor `finite_guard_product` inserts the product, over the false triples
$(a,b,c)\in[-T,T]^3$ with $ab\ne c$, of the denominator-cleared squared distances to
$(\iota(a),\iota(b),\iota(c))$.

- [The finite false-triple product](guard-product.md)
