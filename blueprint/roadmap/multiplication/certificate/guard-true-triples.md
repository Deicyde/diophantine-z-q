---
article_id: af_73428d409a7c5a4fb7036cc3
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Mult.guard_true_triple, ZInQ.Mult.guard_false_triple, ZInQ.Mult.guard_rel_iff, ZInQ.Mult.guardPoly_zero_set
---

# The guard passes true triples and rejects false triples in the box

1. For all $a,b\in\mathbb Z$, $\mathrm{Rel}_{\mathtt{multiply.guard}}(\iota(a),\iota(b),\iota(ab))$.
2. For all $n_1,n_2,n_3\in\mathbb Z$ with $|n_i|\le T$ and $n_1n_2\ne n_3$,
   $\mathrm{Rel}_{\mathtt{multiply.guard}}(\iota(n_1),\iota(n_2),\iota(n_3))$ fails.

That is: a false accepted triple in the box would make its own guard factor zero, while at a
true triple every factor is positive by injectivity of codes, so the inverse exists. The
cutoff $T$ is used symbolically.

**Proof sketch.** By the guard semantics, the guard holds exactly when the input triple is
not $(\iota(a'),\iota(b'),\iota(c'))$ for a false triple $(a',b',c')\in[-T,T]^3$. (1) If
$(\iota(a),\iota(b),\iota(ab))=(\iota(a'),\iota(b'),\iota(c'))$, injectivity of $\iota$ gives
$a=a'$, $b=b'$, $ab=c'$, so $a'b'=c'$ and the triple is not false. (2) The triple itself is
such a false triple.

## Depends on

- [The guard template](../../syntax/templates/template-guard.md)
- [Point codes](../../model/point-codes.md)
- [Prime sets and clearing exponents of the multiplication certificate](constants.md)

## Proof depends on

- [Semantics of the guard template](../../syntax/templates/guard-semantics.md)
- [The generator certificate](../../model/generator.md)
- [Mordell-Weil for $E/K_0$ from the descent](../../model/descent/mordell-weil-from-descent.md)

## Sources

- [Finite guard](../../../sources/multiplication-locators.md#finite-guard)
