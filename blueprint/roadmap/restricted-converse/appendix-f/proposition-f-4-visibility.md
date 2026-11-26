---
article_id: af_83248f24d8a0c98814952724
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Odd.visibility_O8, ZInQ.Manuscript.RC.Wiring.visibilityTarget_of_inputs, ZInQ.Manuscript.RC.Wiring.VisibilityTarget
---

# Proposition F.4: visibility and the genus index (O.8)

Let $M_\theta$ be the stage precisions, $a_\theta(D)$ the phase-removed integer coefficients,
$\lambda_\theta(D)$ integers, $j_{\rm gen}$ the genus index, $\omega=\omega(N)$ and $C$ a constant, and
call $D$ a simple zero if $\operatorname{ord}_{s=1}L(E^{(D)},s)=1$. Assume, at every stage $\theta$ and
admissible $D$ (named inputs, not proved):

- (O.7) after phase removal, as in [(3.8)](../section-7/equation-3-8-theta-coefficients.md):
  $a_\theta(D)\equiv c_0\,2^{\omega}\zeta\,\lambda_\theta(D)\pmod{2^{M_\theta}}$ for an odd $\zeta$;
- the native-index bound: if $D$ is a simple zero, $2^k\mid\lambda_\theta(D)$ for every
  $k\le\min(M_\theta,\,j_{\rm gen}(D)-C)$;
- the torsion clause: if $D$ is not a simple zero, $2^{M_\theta}\mid\lambda_\theta(D)$.

Then, with $C_{\rm det}=C$, at every stage and admissible $D$: if $D$ is a simple zero,
$v_2a_\theta(D)\ge\min\{M_\theta,\,j_{\rm gen}(D)-C_{\rm det}\}$; if not, $v_2a_\theta(D)\ge M_\theta$;
and
$$v_2a_\theta(D)<M_\theta\ \Longrightarrow\ \operatorname{ord}_{s=1}L(E^{(D)},s)=1,\quad
j_{\rm gen}(D)\le v_2a_\theta(D)+C_{\rm det}.\tag{O.8}$$

In the Lean proof of Theorem 5.3, $\lambda_\theta(D)$ is the integer lift `lamOf` of
$\lambda_{M_\theta}(\overline{LP_D})$ and $j_{\rm gen}(D)$ is the index valuation of $P_D$ in its native
lattice, the $\chi$-eigensubgroup of $E(H_1)$; the Kummer map is applied in that lattice, so the
index-two comparison with the rational line that the manuscript absorbs into $C_{\rm det}$ is not
needed, and $C=0$. The manuscript's torsion clause is for admissible $D$ of odd sign; in the reduction
every admissible $D$ has odd sign.

The reduction of Theorem 5.3 uses the implication (O.8) (`VisibilityTarget`), through
`visibilityTarget_of_inputs`. Its inputs come from `PreLeaves.odd_staged` in
[the remaining hypotheses](../remaining-hypotheses.md) (`visibilityInputs_of_oddInstance`): the
native-index bound is proved from the fixed multiplier $L$ killing the torsion of every native lattice
(a field of that leaf; its kind is ELLIOT with Silverman's AEC VII.3.1 as a print in the leaf's
docstring, and GLUE in the docstring of `MultiplierKillsNativeTorsion`); the torsion clause is proved from Cai, Shu
and Tian's Theorem 1.1 among [the cited results](../printed-results.md), the Artin factorization
(derived from modularity, `RCLeaves.artin`) and the odd sign of admissible parameters (GLUE, a field of
the same leaf); and (O.7) is [Proposition F.3](proposition-f-3-theta-comparison.md) applied to that
leaf's comparison argument.

**Proof sketch.** By (O.7), if $k\le M_\theta$ and $2^k\mid\lambda_\theta(D)$ then
$2^k\mid a_\theta(D)$. This gives the two lower bounds. If $v_2a_\theta(D)<M_\theta$, the second
excludes a non-simple zero, and taking $k=v_2a_\theta(D)+1\le M_\theta$ in the first shows
$j_{\rm gen}(D)-C<v_2a_\theta(D)+1$.

## Depends on

- [(O.1): the conductor-one point](equation-o-1-genus-point.md)
- [(3.8): the odd theta coefficients](../section-7/equation-3-8-theta-coefficients.md)
- [Proposition F.3: the unaveraged theta comparison (O.7)](proposition-f-3-theta-comparison.md)

## Sources

- [Appendix F](../../../sources/manuscript.md#appendix-f)
