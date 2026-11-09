---
article_id: af_9b95d8a52f57c305c07cc12d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.templateHeightTable, ZInQ.Size.LibraryAdmissible, ZInQ.Size.templateLibrary_maj
---

# Template heights

Let $B\ge2^{20}$, and suppose that the constructors satisfy the uniform bounds at $B$, that
every index $n$ of a division-polynomial constructor of the library satisfies $|n|+1\le B$,
and that $|\ell|+1\le B$ and $0\le T$, $T+1\le B$. Then the polynomial of every template of
the constructed library has a majorant of order $B$ at the following height:

| Template | Height | Template | Height |
| --- | ---: | --- | ---: |
| member | 18 | multiply.guard | 4 |
| raw_add | 21 | multiply | 214 |
| raw_z | 12 | natural | 223 |
| raw_inverse_x | 12 | value.signed_encode | 230 |
| log25 | 25 | value.abs | 9 |
| pole | 24 | value.close_coordinates | 34 |
| test_group | 79 | value.test | 249 |
| slope | 169 | value.exceptions | 43 |
| height_certificate | 207 | scalar.integer_constant_$k$ ($k=0,\dots,4$) | 17 |
| multiply.scalar | 17 | | |

The division-polynomial constructors of the library occur only in the fixed-scalar
templates $S_\varepsilon$, with indices $\varepsilon$, $\varepsilon+1$, $\varepsilon-1$ and
$2\varepsilon$ for $\varepsilon\in\{c_*,4,2,3,c_3,1399\}$; the guard constructor occurs at
$T$, and the fixed constant $\ell$ only in multiply. Every other constant of the library is
an explicit integer literal and needs no hypothesis.

The manuscript states the table for the intrinsic heights of the node lists of the saved
specification, with $173$ constant nodes below $2^{69}$ and $50$ constructor nodes. The
templates here are explicit constructions without node lists, so the statement is made for
their polynomials.

**Proof sketch.** Apply the majorant rules to each template in library order, along its
construction, with the bounds of the templates it calls and the constructor bounds. Each
literal constant $c$ is bounded as $|c|\le2^{2^k}$ for a small explicit $k$, and $B\ge2^{20}$
absorbs these bounds; no fixed value is computed. The construction gives much
smaller heights, at most $8$ ($1$ for the templates without calls, $6$ for multiply); the
tabulated heights follow by monotonicity.

## Depends on

- [The template library](../../syntax/templates/template-library.md)
- [Syntax heights](syntax-height.md)
- [Uniform bounds for the finite constructors](../norms/constructor-bounds.md)
- [The prescribed fixed constants](../../syntax/constants/fixed-constants.md)

## Sources

- [Section 12.1 checked facts](../../../sources/size-locators.md#section-121-checked-facts)
- [Height traversal](../../../sources/size-locators.md#height-traversal)
