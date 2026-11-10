---
article_id: af_98f7f4277ba89db8a533f9d6
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.multiply_complete_AP, ZInQ.Mult.slopes_of_int_AP, ZInQ.Mult.completeness_core_AP
---

# Completeness of the multiplication template under field 2′

Assume pole completeness and the slope representation under field 2′. For all $a,b\in\mathbb Z$,
$$\mathrm{Rel}_{\mathtt{multiply}}\bigl(\iota(a),\iota(b),\iota(ab)\bigr).$$

This is the completeness of the multiplication template with the slope representation weakened
to field 2′. The template, and hence the polynomial, is the same; only the proof changes, and
only in the choice of the parameter $q$ of each slope certificate.

**Proof sketch.** The proof of the completeness of the multiplication template, word for word:
the guard holds at a true triple; for each of the nine integers $a_{i0},a_{i1},b_i$ of the
height certificate, the slope representation under field 2′ gives three slopes with that sum,
and each of the $27$ slopes satisfies the slope predicate by the completeness of the slope
certificate under field 2′.

## Depends on

- [The multiplication template](../syntax/templates/template-multiply.md)
- [Point codes](../model/point-codes.md)
- [Semantics of templates and recipes](../syntax/template-semantics.md)
- [Pole completeness](../main/pole-completeness.md)
- [The slope representation under field 2′](slope-representation-ap.md)

## Proof depends on

- [Unfolding the multiplication template](../multiplication/certificate/multiply-unfolding.md)
- [Semantics of the height certificate template](../multiplication/certificate/height-certificate-semantics.md)
- [The guard passes true triples and rejects false triples in the box](../multiplication/certificate/guard-true-triples.md)
- [Completeness of the slope certificate under field 2′](slope-completeness-ap.md)

## Sources

- [The modified completeness argument](../../sources/route-ap-locators.md#the-modified-completeness-argument)
- [Conclusion of the multiplication proof](../../sources/multiplication-locators.md#conclusion-of-the-multiplication-proof)
