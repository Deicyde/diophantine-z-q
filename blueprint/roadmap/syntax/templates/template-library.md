---
article_id: af_992a403e0ad362f5f8ed0ae8
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.templateLibrary, ZInQ.Syntax.templateLibrary_witnesses, ZInQ.Syntax.templateLibrary_wf
---

# The template library

The template library is the list of $23$ templates, in this order (index: name):
$0$ $\mathtt{member}$, $1$ $\mathtt{raw\_add}$, $2$ $\mathtt{raw\_z}$, $3$
$\mathtt{raw\_inverse\_x}$, $4$ $\mathtt{log25}$, $5$ $\mathtt{pole}$, $6$
$\mathtt{test\_group}$, $7$ $\mathtt{slope}$, $8$ $\mathtt{height\_certificate}$, $9$
$\mathtt{multiply.scalar}=S_{c_*}$, $10$ $\mathtt{multiply.guard}$, $11$ $\mathtt{multiply}$, $12$
$\mathtt{natural}$, $13$ $\mathtt{value.signed\_encode}$, $14$ $\mathtt{value.abs}$, $15$
$\mathtt{value.close\_coordinates}$, $16$ $\mathtt{value.test}$, $17$ $\mathtt{value.exceptions}$,
and $18+k$ $\mathtt{scalar.integer\_constant}_k=S_{\mathrm{integer\_constant}_k}$ for
$k=0,\dots,4$.

The constants $\mathrm{integer\_constant}_k$ are the distinct integer constants other than
$0,1,-1$ met by the model-evaluation translation, numbered in the order in which they are
first met: first in the power template, then in the precision circuit. They are
$4,2,3,c_3,1399$, where $c_3$ is the program literal of the natural precision polynomial.
Equivalently, the list $(4,2,3,c_3,1399)$ is fixed in advance and the translation looks up
each constant's index in it; the shape of the natural precision circuit shows that these five
values are exactly the constants met, in order of first occurrence.

Every call in a template refers to a template of smaller index, so the library is denoted
in this order. The parameter and witness counts are as follows. The manuscript's table also
lists the root node index of each template's node list ($149,308,68,54,229,106,515,2681,260,136,22,83,79,138,23,271,775,487$
and $136$ for each scalar-constant template); these are properties of the node encoding,
checked by the external comparison with the saved specification, and play no role in the
proof.

| Index | Template | Parameters | Witnesses |
| --- | --- | ---: | ---: |
| 0 | member | 5 | 7 |
| 1 | raw_add | 15 | 6 |
| 2 | raw_z | 7 | 1 |
| 3 | raw_inverse_x | 7 | 0 |
| 4 | log25 | 4 | 0 |
| 5 | pole | 1 | 11 |
| 6 | test_group | 44 | 162 |
| 7 | slope | 22 | 1,298 |
| 8 | height_certificate | 36 | 35,106 |
| 9 | multiply.scalar | 10 | 1 |
| 10 | multiply.guard | 15 | 1 |
| 11 | multiply | 15 | 35,134 |
| 12 | natural | 5 | 140,604 |
| 13 | value.signed_encode | 10 | 140,654 |
| 14 | value.abs | 2 | 4 |
| 15 | value.close_coordinates | 16 | 53 |
| 16 | value.test | 11 | 35,282 |
| 17 | value.exceptions | 6 | 406 |
| 18-22 | scalar.integer_constant_0..4 | 10 | 1 |

This is a definition.

## Depends on

- [The membership template](../template-member.md)
- [The raw addition template](../template-raw-add.md)
- [The local parameter template](template-raw-z.md)
- [The inverse abscissa template](template-raw-inverse-x.md)
- [The truncated logarithm template](template-log25.md)
- [The pole template](template-pole.md)
- [The test-group template](template-test-group.md)
- [The slope template](template-slope.md)
- [The height certificate template](template-height-certificate.md)
- [The fixed-scalar templates](template-fixed-scalar.md)
- [The guard template](template-guard.md)
- [The multiplication template](template-multiply.md)
- [The natural-code template](template-natural.md)
- [The signed-encoding template](template-signed-encode.md)
- [The absolute-value template](template-abs.md)
- [The coordinate-window template](template-close-coordinates.md)
- [The value-test template](template-value-test.md)
- [The exceptional-values template](template-exceptions.md)
- [Translation of a natural circuit into a model-evaluation recipe](../recipes/model-evaluation-translation.md)

## Informally uses

- [Shape of the natural precision circuit](../../compiler/natural/universal/circuit-node-counts.md)
- [Node statistics of the halting circuit and the power template](../../compiler/natural/universal/halting-node-check.md)

## Sources

- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
- [Saved specification](../../../sources/syntax-locators.md#saved-specification)
