---
article_id: af_2459ec66a3941590bbc825e6
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.multiply_sound
---

# Soundness of the multiplication template

Assume the minimal height hypothesis. For all
$Y_1,Y_2,Y_3\in\mathbb Q^5$, if $\mathrm{Rel}_{\mathtt{multiply}}(Y_1,Y_2,Y_3)$, then there are
$a,b\in\mathbb Z$ with $(Y_1,Y_2,Y_3)=(\iota(a),\iota(b),\iota(ab))$.

This direction is sound on arbitrary rational inputs. It uses the generator certificate and
the six-contact estimate in its minimal form, but neither pole completeness nor the prime
pattern.

**Proof sketch.** By the unfolding of the template, $Y_i=\iota(n_i)$ for some integers $n_i$,
the unguarded certificate accepts $(\iota(n_1),\iota(n_2),\iota(n_3))$ with the shift points
$\iota(c_*),\iota(c_*n_i)$, and the guard holds. If $n_1n_2\ne n_3$, the finite-box deduction
gives $|n_i|<T$ for all $i$, so the triple is a false triple in $[-T,T]^3$ and the guard
fails, a contradiction. Hence $n_3=n_1n_2$; take $a=n_1$, $b=n_2$.

## Depends on

- [The multiplication template](../../syntax/templates/template-multiply.md)
- [Point codes](../../model/point-codes.md)
- [Semantics of templates and recipes](../../syntax/template-semantics.md)
- [The minimal height hypothesis](../../main/six-contact-min.md)

## Proof depends on

- [Unfolding the multiplication template](../certificate/multiply-unfolding.md)
- [The finite-box deduction](finite-box.md)
- [The guard passes true triples and rejects false triples in the box](../certificate/guard-true-triples.md)

## Sources

- [Finite guard](../../../sources/multiplication-locators.md#finite-guard)
- [Finite-box deduction](../../../sources/multiplication-locators.md#finite-box-deduction)
- [Conclusion of the multiplication proof](../../../sources/multiplication-locators.md#conclusion-of-the-multiplication-proof)
