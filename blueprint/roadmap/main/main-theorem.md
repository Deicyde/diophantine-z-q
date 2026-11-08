---
article_id: af_0be94ccf3fca69a8d9322f8c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.exists_bounded_integer_polynomial_defining_integers_of, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_addMulBound
---

# The main theorem

Assume the six-contact height estimate, pole completeness, the twenty-two-prime pattern
and the catalogue bound (every unit class modulo $W$ contains twenty-two primes $p$ with
$324<p<2^{W^8}$). Then the target statement holds: some integer polynomial in $292{,}890{,}231{,}905$ variables, of degree below
$2\uparrow\uparrow7$ and with coefficients below $2\uparrow\uparrow8$, has rational zero
projection to its first variable exactly $\mathbb Z$.

The fourth hypothesis is proved in the progressions chapter
([the catalogue bound holds](../progressions/catalogue-instance.md)); combined with it, the
target follows from the first three hypotheses.

## Depends on

- [The target statement](frozen-target.md)
- [The six-contact height estimate](six-contact-estimate.md)
- [Pole completeness](pole-completeness.md)
- [The twenty-two-prime pattern](prime-pattern.md)
- [The catalogue bound](catalogue-bound.md)

## Proof depends on

- [The assembly lemma](../assembly/assembly-lemma.md)

## Sources

- [Theorem 1.1 and Lemma 1.2](../../sources/manuscript.md#theorem-11)
