---
article_id: af_b151a7b9eaa5551d199767a1
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.multiplication_exact_AP
---

# Correctness of the multiplication template under field 2′

Assume the minimal height hypothesis, pole completeness and the slope representation under
field 2′. For all $Y_1,Y_2,Y_3\in\mathbb Q^5$,
$$\mathrm{Rel}_{\mathtt{multiply}}(Y_1,Y_2,Y_3)\iff\exists\,a,b\in\mathbb Z:\quad
(Y_1,Y_2,Y_3)=\bigl(\iota(a),\iota(b),\iota(ab)\bigr).$$

**Proof sketch.** Soundness is the soundness of the multiplication template, which uses neither
pole completeness nor any slope representation. Completeness is the completeness of the
multiplication template under field 2′.

## Depends on

- [The multiplication template](../syntax/templates/template-multiply.md)
- [Point codes](../model/point-codes.md)
- [The minimal height hypothesis](../main/six-contact-min.md)
- [Pole completeness](../main/pole-completeness.md)
- [The slope representation under field 2′](slope-representation-ap.md)

## Proof depends on

- [Soundness of the multiplication template](../multiplication/soundness/soundness.md)
- [Completeness of the multiplication template under field 2′](completeness-ap.md)

## Sources

- [The modified completeness argument](../../sources/route-ap-locators.md#the-modified-completeness-argument)
- [Multiplication input M](../../sources/multiplication-locators.md#multiplication-input-m)
