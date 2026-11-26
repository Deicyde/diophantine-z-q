---
article_id: af_ee1197a75800e7bc37f8ba63
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Uniform.exLimitsUniformLowerBound, ZInQ.Contrib.CloudB3RC53.SwitchInputs.switchDimsOfSES_proof, ZInQ.Manuscript.RC.Uniform.QuadraticCase.eval_tau_h_sq
---

# Proposition 9.6: the uniform lower bound and height-one regularity

Assume:

- that $v$ is the valuation of $\mathscr O$, read on $\operatorname{Frac}\Lambda$ through an embedding
  (`ValuationOfO`, GLUE; proved for the actual $\mathscr O$ as `valuationOfO_genuine`);
- for every sequence of instances, an outer switching process along the fixed nonprincipal
  ultrafilter that starts at the primitive coordinates (`OuterSwitchProcess`, ELLIOT): the outer kernel
  dimension is at least one, a switch lowers it by two and keeps the inner valuations, and at dimension
  one the coordinate is $\pm\alpha\beta/\Delta$ with $\alpha$ integral, $v(\beta)\ge-a$ and $\Delta$
  integral and not negligible;
- at every height-one prime $\mathfrak p\ne(2)$ of $\Lambda$, unless the coordinate is zero, a switching
  process over $\Lambda_{\mathfrak p}$ that starts at it (`RegularitySwitchProcess`, ELLIOT): the fiber
  dimension is at least one, a switch lowers it by two (after at most one switch that mixes the signs)
  and changes the coordinate by a regular factor, and the terminal coordinate is regular.

Fix $A$. For the known simple-zero ring instances with $\omega(k)\le A$ and primitive coordinates
$u_{\rm prim}\in\operatorname{Frac}\Lambda$, there is $C=C(E,A)$, independent of the active support and
the companion field, such that every instance has
$$v_2u_{\rm prim}\ge-C,\qquad u_{\rm prim}\in\Lambda[1/2],$$
and indeed $2^Cu_{\rm prim}\in\Lambda$. Consequently, if $u_{\rm prim}(0)\ne0$ and
[(4.6)](../section-8/proposition-8-9-central-calibration.md) holds with error $C_0$, local terms
$0\le t_p\le2$ and at most $A$ primes $p$, then $2j_{\rm rc}\ge4\omega(h)+s(h)+s(hk)-(C+C_0+2A)$, which
is (3.5).

In the regularity argument, let $K_0$ be the strict fiber cohomology, $V$ and $V'$ the finite and the
switched fiber cohomology, and $U\subset F\oplus S$ the relaxed localization image. The cone triangles
give
$$0\to K_0\to V\to U\cap F\to0,\qquad0\to K_0\to V'\to U\cap S\to0.\tag{5.5a}$$
Lean states the dimension form $\dim V=\dim K_0+\dim(U\cap F)$, for any two short exact sequences of
cochain complexes over a field with the stated local facts, so it also gives the second sequence with
$S$ in place of $F$ (`switchDimsOfSES_proof`). For $h$ in the exact
kernel of Lemma 9.4 and a cocycle $c_\delta$ of sign $\delta=\pm1$,
$$c_\delta((\tau h)^2)=(1+\delta J)c_\delta(h)\tag{5.5b}$$
(`eval_tau_h_sq`, with no input).

The Lean theorem takes the instances as an abstract family with coordinates in
$\operatorname{Frac}\Lambda$: the hypotheses of [Proposition
8.9](../section-8/proposition-8-9-central-calibration.md) and the bound $\omega(k)\le A$ enter only
through the two process inputs, and in the last clause (4.6), $j_{\rm rc}$, $\omega$ and $s$ are free
variables. Regularity at the unknown full-corank-one base is `mem_lambdaHalf_of_regularity`, which needs
no lower bound.

The reduction of Theorem 5.3 uses this theorem, over the actual $\mathscr O$, in its proof of
[(3.5)](../section-7/equation-3-5-arithmetic-lower-bound.md), with both process inputs built from the
field `PreLeaves.eq35` of [the remaining hypotheses](../remaining-hypotheses.md). The regularity of the
coordinates $\widetilde u_x$ used in [Proposition 9.8](proposition-9-8-common-denominator.md) comes
instead from the field `PostLeaves.prim_regular` (through `heightOneTarget_of_HPK`). The docstrings
record that, granted one residue-fibre complex at each height-one prime (true, not formalized), this
field is equivalent to the regularity itself, and that it is asserted at the base of every final
family, while the manuscript proves the base case only at full Selmer corank one over $K$.

**Proof sketch.** The bound is [(5.5)](equation-5-5-uniform-lower-bound.md). For regularity, at each
height-one prime $\mathfrak p\ne(2)$ finitely many switches reach fiber dimension one, where the
coordinate is regular, and each switch changes it by a regular factor; the intersection formula
$\Lambda[1/2]=\bigcap_{\mathfrak p\ne(2)}\Lambda_{\mathfrak p}$ gives $u_{\rm prim}\in\Lambda[1/2]$. With
$v_2u_{\rm prim}\ge-C$ this gives $2^Cu_{\rm prim}\in\Lambda$, so the central value has valuation at
least $-C$, and (4.6) with $\sum_pt_p\le2A$ gives (3.5).

## Depends on

- [The remaining hypotheses](../remaining-hypotheses.md)

## Proof depends on

- [(5.5): the uniform lower bound](equation-5-5-uniform-lower-bound.md)

## Sources

- [Section 9](../../../sources/manuscript.md#section-9)
