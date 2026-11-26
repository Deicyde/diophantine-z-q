---
article_id: af_8d326148c1ddb9cf48c24374
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.CalPoint.centralClassFunctional_v2_a0, ZInQ.Manuscript.RC.CalPoint.centralClassFunctional_v2_b0, ZInQ.Manuscript.RC.CalPoint.centralClassFunctional
---

# Lemma 8.8: central specialization keeps the same class

Assume, for the ordinary compact central Kummer complex $C_K$ of the twist $E^{(h)}$ over $K$ with finitely
generated cohomology:

- its cohomology shape: rank one in degrees one and two, torsion in degree three, nothing elsewhere
  (`CalibrationCohomologyShape`, a hypothesis of the theorem to which its docstring gives no kind;
  `calibrationShape_of_arithmetic` derives it from statements of Milne and other inputs, among them a
  Kummer coefficient comparison, Selmer corank one over $K$ and the integral self-duality below);
- its integral self-duality, a homotopy equivalence of the retained free model with its shifted dual
  (`IntegralCentralKummerDuality`); `bookDuality` derives it from statements of Milne and Nekovář
  (`CalibrationBookProps`, PRINT and GLUE), which are not inputs of the reduction of Theorem 5.3;
- point data (`RetainedPointData`): the fixed multiplier $L\ne0$, the point $P$, a free generator of the
  rank-one lattice with $P\equiv n_P\cdot{\rm gen}$ modulo torsion and $v_2n_P=j$, the Kummer map carrying
  the generator to a generator of the free line of $H^1(C_K)$ (`RetainedPointData.hκ`, GLUE: the Kummer
  sequence with finite Ш), and an involutive conjugate-dual transport $c_K$. In the cited theorems
  $\kappa$ is any additive map satisfying `hκ`; the genuine Kummer map is `centralKummer`, with the
  point data `CentralPointData`.

For $m\ne0$, let $z_0$ be a cycle of class $\kappa(LmP)$ and $\lambda_0$ the image under the duality of a
cycle of class $c_K(\kappa(LmP))$. Then the class and functional coefficients of $z_0$ and $\lambda_0$ in
the retained free lines both have valuation $j+v_2L+v_2m$.

In the manuscript $z_0=i(LmP)$ and $(\lambda_z)_0(ix)=\operatorname{PD}_K(x,c_K(LmP))$ are proved from the
retained class and paired functional by derived base change and (4.5). In Lean they are the definitions
of the central class and functional (`centralClassFunctional`); only the valuation consequence is proved.
The first clause of the lemma, (4.5) for the finite classes, is [(4.5)](equation-4-5-retained-boundary.md),
stated there only at the base.

The reduction of Theorem 5.3 does not use this theorem: the valuations of the class and functional are
part of the triangular Kummer model in the field `PostLeaves.calibration` of [the remaining
hypotheses](../remaining-hypotheses.md), used in [Proposition 8.9](proposition-8-9-central-calibration.md).

**Proof sketch.** The class coefficient of $z_0$ is $Ln_Pm$ times a unit, since $\kappa$ carries the
generator to a free-line generator, so its valuation is $v_2L+j+v_2m$. The duality equivalence identifies
the degree-two free line with the dual of the degree-one free line, and $c_K$ is an involutive
automorphism of a rank-one lattice, so it acts by $\pm1$ and the functional coefficient has the same
valuation.

## Depends on

- [Section 8: actual classes, local conditions and central comparison](README.md)

## Sources

- [Section 8](../../../sources/manuscript.md#section-8)
