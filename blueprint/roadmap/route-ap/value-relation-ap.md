---
article_id: af_6f8979d1f7bac23ec5a3951a
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Assembly.exists_value_relation_iff_AP
---

# The ordinary-value relation under field 2′

Assume the minimal height hypothesis, pole completeness and the slope representation under
field 2′. Then for every $t\in\mathbb Q$,
$$\bigl(\exists\,N\in\mathbb Q^5:\ \mathrm{Rel}_{\mathtt{value}}(N,t)\bigr)\iff t\in\mathbb Z .$$

**Proof sketch.** The proof of the exact ordinary-value relation uses the slope representation
only through the correctness of the multiplication template (input M), directly and through the
soundness and completeness of Close. Supply M from the correctness of the multiplication template
under field 2′.

## Depends on

- [The minimal height hypothesis](../main/six-contact-min.md)
- [Pole completeness](../main/pole-completeness.md)
- [The slope representation under field 2′](slope-representation-ap.md)

## Proof depends on

- [The exact ordinary-value relation](../assembly/ordinary-value-relation.md)
- [Correctness of the multiplication template under field 2′](multiplication-exact-ap.md)

## Sources

- [The modified completeness argument](../../sources/route-ap-locators.md#the-modified-completeness-argument)
