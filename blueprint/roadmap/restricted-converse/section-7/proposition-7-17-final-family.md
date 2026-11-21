---
article_id: af_717b3fcd958db37e0f795da0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Wiring.finalFamilyTarget_of, ZInQ.Manuscript.RC.Wiring.FinalFamilyTarget, ZInQ.Manuscript.RC.RCData.FinalFamilyAt
---

# Proposition 7.17: one family for the two coefficient tests (3.9)

Work with the interface data of [the remaining hypotheses](../remaining-hypotheses.md): the fixed
support $S$, the prepared filter, $L_*$, $j_{\rm gen}$, $j_{\rm rc}$, the theta stages with their
coefficients, the odd minimum $\delta_o$ and the final $k$. Assume:

- the visibility implication (O.8): there is $C_{\rm det}$ such that an admissible $D$ with
  $v_2a_{M_\theta}(D)<M_\theta$ has $\operatorname{ord}_{s=1}L(E^{(D)},s)=1$ and
  $j_{\rm gen}(D)\le v_2a_{M_\theta}(D)+C_{\rm det}$;
- the precisions $M_\theta$ tend to infinity along the ultrafilter of stages;
- [(3.3)](proposition-7-14-rough-companion.md), [(3.4)](equation-3-4-height-comparison.md) at the
  companions and [(3.5)](equation-3-5-arithmetic-lower-bound.md);
- admissible theta parameters lie in the prepared filter (GLUE);
- $\delta_o$ is the attained odd minimum;
- the address input at $\delta_o$ for these constants (`AddressLeaf`), which the reduction of
  Theorem 5.3 derives from the field `PostLeaves.address`.

Suppose that the odd symbol is not a unit at the empty configuration. Then there are $C_o$, $C_e$ and
$b_0$ such that for every $b\ge b_0$ there are a finite set $Q$ of distinct odd primes outside $S$, split
in $K=\mathbb Q(\sqrt k)$, and nonzero linear forms $\lambda_q:\mathbb F_2^b\to\mathbb F_2$, such that the
family
$$h_x=\prod_{q\in Q}(q^*)^{\lambda_q(x)},\qquad q^*=(-1)^{(q-1)/2}q,$$
has $h_0=1$ and, at every $x\ne0$, $h_x$ is prepared and
$$\operatorname{ord}_{s=1}L(E^{(h_x)},s)=1,\quad L_*(h_xk)\ne0,\quad
j_{\rm gen}(h_x)\le\omega(h_x)+C_o,\quad v_2L_*(h_xk)\le2\omega(h_x)+C_e.\tag{3.9}$$

The Lean family need not have a vertex of every nonzero activation, so it may have $h_x=1$ at some
$x\ne0$; the manuscript's families do not. The consequence
$2j_{\rm rc}(h_x,k)\le4\omega(h_x)+C_J$ in the manuscript's last sentence is not part of the statement.

**Proof sketch.** The Lean proof follows the manuscript's order of choices. From (3.3)–(3.5) it gets the
genus lower bound [(3.6)](equation-3-6-genus-lower-bound.md), and with (O.8) the coarse lower bound on
the odd coefficients at every stage, hence the odd minimum inequality at $\delta_o$. The address input
then gives, for each large $b$, one stage in the ultrafilter at which every nonzero address is a unit
of both sources, with $v_2a_{M_\theta}(h_x)=\delta_o+\omega(h_x)<M_\theta$. Visibility (O.8) gives the
simple zero and $j_{\rm gen}(h_x)\le\omega(h_x)+\delta_o+C_{\rm det}$, so $C_o=\delta_o+C_{\rm det}$.

## Depends on

- [The remaining hypotheses](../remaining-hypotheses.md)
- [Proposition 7.14: a bounded companion (3.3)](proposition-7-14-rough-companion.md)
- [(3.4): the height comparison](equation-3-4-height-comparison.md)
- [(3.5): the arithmetic lower bound](equation-3-5-arithmetic-lower-bound.md)

## Proof depends on

- [(3.6): the genus lower bound](equation-3-6-genus-lower-bound.md)

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
