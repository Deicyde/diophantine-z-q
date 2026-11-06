---
article_id: af_9b95d8a52f57c305c07cc12d
declaration: theorem
origin: cited
---

# Template heights

For the constructed template library:

1. the intrinsic heights are at most the following values:

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

2. there are $173$ nodes $\mathrm{const}\ c$, and each has $|c|<2^{69}$;
3. there are $50$ constructor nodes: one $\mathrm{fixed}\ e$, whose expression $e$ is the
   reference to $\ell$; one $\mathrm{guard}\ e\ a$, whose expression is the reference to $T$; and
   $48$ nodes $\mathrm{psi}\ e\ a\ c$, whose index expressions are, syntactically, among
   $\varepsilon$, $\mathrm{add}(\varepsilon,1)$, $\mathrm{add}(\varepsilon,-1)$ and $\mathrm{mul}(2,\varepsilon)$
   for $\varepsilon$ the reference to one of $c_*$, $\mathrm{integer\_constant}_0,\dots,\mathrm{integer\_constant}_4$.

This is a finite computation: one pass over the node lists of the twenty-three constructed
templates, about $7100$ nodes in all, computing heights by the rules and comparing
expressions syntactically. No fixed expression is evaluated.

**Proof sketch.** Evaluate the height function node by node in library order, and inspect
the constant and constructor nodes. The values in the table are those recorded for the
saved specification; since the construction produces the same node lists, they are
expected to be attained.

## Depends on

- [The template library](../../syntax/templates/template-library.md)
- [Syntax heights](syntax-height.md)
- [The prescribed fixed constants](../../syntax/constants/fixed-constants.md)

## Sources

- [Section 12.1 checked facts](../../../sources/size-locators.md#section-121-checked-facts)
- [Height traversal](../../../sources/size-locators.md#height-traversal)
