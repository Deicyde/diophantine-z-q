---
article_id: af_d4a54d42e27c947b6b5ecdfd
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Uniform.uniform_lower_bound_of_switchProcess, ZInQ.Manuscript.RC.Wiring.eq55_of_inputsAR
---

# (5.5): the uniform lower bound

Assume, for every sequence of instances, an outer switching process along the fixed nonprincipal
ultrafilter whose starting configuration has the valuations of the primitive coordinates
(`OuterSwitchProcess`, ELLIOT; its fields are listed on [the page of Proposition
9.6](proposition-9-6-uniform-lower-bound.md)).

Then there is $C=C(E,A)$ such that every known simple-zero ring instance with $\omega(k)\le A$ has
$$v_2u_{\rm prim}\ge-C(E,A).\tag{5.5}$$

Lean states this for any field with a valuation and any family of coordinates: the instances, $A$ and
the hypotheses of [Proposition 8.9](../section-8/proposition-8-9-central-calibration.md) enter only
through the input, whose fields stand for the steps of the manuscript's proof that use (5.1), (5.3),
(5.4) and Lemma 9.5. As in the manuscript, the constant comes from an ultrafilter contradiction and is
not effective. From the field `PreLeaves.eq35` of [the remaining
hypotheses](../remaining-hypotheses.md), `eq55_of_inputsAR` gives (5.5) over the actual $\mathscr O$,
for coordinates fixed before $A$, at every companion pair $(h,k')$ with $\omega(k')\le A$.

The reduction of Theorem 5.3 uses only `uniform_lower_bound_of_switchProcess`, through
`exLimitsUniformLowerBound`, the theorem of [Proposition 9.6](proposition-9-6-uniform-lower-bound.md), in
its proof of [(3.5)](../section-7/equation-3-5-arithmetic-lower-bound.md); `eq55_of_inputsAR` is off the
reduction path.

**Proof sketch.** If no constant works, choose instances with $v_2u_j\to-\infty$ and take their process.
Finitely many switches reach outer dimension one without changing the inner valuations on a set in the
ultrafilter. There $u=\pm\alpha\beta/\Delta$ gives $v_2u_j\ge-a-b$ on such a set, where $b$ bounds the
valuation of $\Delta$, a contradiction.

## Depends on

- [The remaining hypotheses](../remaining-hypotheses.md)

## Sources

- [Section 9](../../../sources/manuscript.md#section-9)
