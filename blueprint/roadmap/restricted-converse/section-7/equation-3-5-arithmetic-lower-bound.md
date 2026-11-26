---
article_id: af_c9828e66ba91073d9845ebd9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Wiring.eq35Target_of_inputsAR, ZInQ.Manuscript.RC.Wiring.Eq35Target
---

# (3.5): the arithmetic lower bound

Assume the field `PreLeaves.eq35` of [the remaining hypotheses](../remaining-hypotheses.md) (ELLIOT and
GLUE): the primitive coordinates at the companion pairs with their switch data, over configuration
families of genuine Galois Selmer data, and (4.6) at the companion pairs; then, for every $A$, retained
switched models over $\mathscr O$ for the companion pairs with $\omega(k')\le A$, of size at most the
cap of (5.1). Then for every $A$ there is $C_R(E,A)$ such that for every prepared $h$ with
$\operatorname{ord}_{s=1}L(E^{(h)},s)=1$ and every companion $k'$ of $h$ with $\omega(k')\le A$,
$$2j_{\rm rc}(h,k')\ge4\omega(h)+s(h)+s(hk')-C_R(E,A).\tag{3.5}$$

The prepared filter and $j_{\rm rc}$ are interface data of the remaining hypotheses, constrained only by
their fields; the companion relation is the definition `WData.IsRoughCompanion`, built from interface
data. The docstrings of `ZInQKernel/Contrib/OneProof/RC/Wiring/Leaves.lean` record that the
field is close to the conclusion: its configuration families and outer models are existential, and a
full equivalence with (3.5) would also need genuine realizations of the outer models.

**Proof sketch.** In the manuscript (3.5) is a forward reference to the uniform lower bound of Section 9
with the central identity of Section 8. The Lean proof follows it: from the field it proves the
primitive kernel vectors, the regularity of the primitive coordinates, the equal inner valuations and
the terminal step of the switch argument, and deduces (3.5) over the genuine valuation. The reduction
of Theorem 5.3 uses this theorem.

## Depends on

- [The remaining hypotheses](../remaining-hypotheses.md)
- [Proposition 7.14: a bounded companion (3.3)](proposition-7-14-rough-companion.md)

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
