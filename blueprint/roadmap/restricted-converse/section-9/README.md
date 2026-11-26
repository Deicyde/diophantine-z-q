---
article_id: af_207cabe760d305727aac8c90
---

# Section 9: the two limits and determinant transfer

Section 9 gives two parts of the proof of [Theorem 5.3](../restricted-converse.md): the varying-companion
estimate behind (3.5), and, in the branch where the odd symbol is not a unit at the empty configuration,
the determinant argument that ends the proof. It works with the actual diagrams of Section 8, keeping
their maps, homotopies, classes and boundary witnesses rather than only their cohomology. In order:

1. **The two limits.** Finite free models of the cochain complexes over Artin rings, with their diagrams
   transported, pass to an inner limit over $\Lambda$ along one ultrafilter (Lemma 9.1). The generic
   residual rank is bounded independently of the active primes (Lemma 9.2, through (5.1)). Evaluation at
   Galois elements satisfies (5.2), stays injective after coefficient change, and passes to the outer
   valuation ring (5.3) (Lemma 9.3).
2. **The varying-companion estimate.** Restriction to the exact kernel detects cohomology, and one new
   prime gives a rank-two test, realized by Chebotarev with the exact identity (5.4) (Lemma 9.4).
   Derivative conditions give a switch that keeps the determinant valuation (Lemma 9.5). The switch
   argument gives the uniform lower bound (5.5) and the height-one regularity of the primitive
   coordinates (Proposition 9.6); with [(4.6)](../section-8/proposition-8-9-central-calibration.md)
   this is [(3.5)](../section-7/equation-3-5-arithmetic-lower-bound.md), which feeds the genus bound of
   Section 7.
3. **The fixed-field count.** With the final field $K$ fixed, the support triangle (5.6) and the budget
   (5.7) bound the old complex independently of the family, and the inverse new local blocks have
   bounded poles (5.8) (Lemma 9.7). A common denominator then clears the corrected coordinate, with the
   bounds (5.9) (Proposition 9.8).
4. **The final contradiction.** With $M$ and $b$ chosen as in (5.10), a Boolean degree count gives a
   nonzero address whose coordinate agrees with the base to high precision, (5.11) (Proposition 9.9).
   With the upper bound at the nonzero addresses and [Lemma 8.11](../section-8/lemma-8-11-base-zero.md)
   this forces $L'(E/K,1)\ne0$, the last step of [the reduction](../reduction.md).

## Definitions

Section 9 has no numbered definitions. Its notation: $\Lambda=\mathbb Z_2[[t]]$ and $\mathscr O$ the
completion of $\Lambda_{(2)}$, as in Section 8; for the final field $K$ and its Kummer Selmer complex
$C_K$, $d_K=\dim_{\mathbb F_2}\mathrm{Sel}_2(E/K)$, $t_K=\operatorname{length}E(K)[2^\infty]$ and
$h_K=\operatorname{length}H^2(C_K)_{\rm tors}$; $c_E$ the constant of the moving character; and
$c_{\det}=a+4(h_K+2c_E+2t_K)$ and $L_T(M)=16(d_K+5)M$, with $a$ the paired-functional exponent. In Lean
$\Lambda$, $\mathscr O$, $c_{\det}$ and $L_T$ are `ZInQ.Manuscript.RC.Limits.Lambda`,
`ZInQ.Manuscript.RC.Determinant.OO` (the completion as an inverse limit of Laurent series rings),
`ZInQ.Manuscript.RC.Boolean.cDet` and `ZInQ.Manuscript.RC.Boolean.LT`. In the reduction of Theorem 5.3
$d_K$, $h_K$, $c_E$ and $t_K$ are existential, free numbers tied only by the counts of the field
`PostLeaves.clearing_model`, and the reduction reads neither `Boolean.cDet` nor `Boolean.LT`:
`ClearingTarget` writes $16(d_K+5)M$ inline, and `MissingAddressNode` takes $L_T$ as a free number.

## The items

- [Lemma 9.2: the reduced generic residual rank bound](lemma-9-2-residual-bound.md), with (5.1a) and
  (5.1b)
- [(5.1): the total rank of the smaller-support cone](equation-5-1-total-rank.md)
- [(5.2): the evaluation identities](equation-5-2-evaluation-identities.md)
- [(5.3): the outer valuation ring](equation-5-3-outer-ring.md)
- [(5.4): the exact matrix identity at a new prime](equation-5-4-exact-matrix-identity.md)
- [Proposition 9.6: the uniform lower bound and height-one regularity](proposition-9-6-uniform-lower-bound.md),
  with (5.5a) and (5.5b)
- [(5.5): the uniform lower bound](equation-5-5-uniform-lower-bound.md)
- [(5.6): the support triangle](equation-5-6-support-triangle.md)
- [(5.7): the fixed-field budget](equation-5-7-fixed-field-budget.md)
- [(5.8): the inverse new local blocks](equation-5-8-inverse-blocks.md)
- [Proposition 9.8: a common denominator for the corrected coordinate](proposition-9-8-common-denominator.md),
  with (5.9)
- [(5.10): the choice of the precision and the address dimension](equation-5-10-choice.md)
- [Proposition 9.9: finite coefficient transfer](proposition-9-9-coefficient-transfer.md), with (5.11)

The displays (5.1a) and (5.1b) are on the page of Lemma 9.2, (5.5a) and (5.5b) on the page of
Proposition 9.6, (5.9) on the page of Proposition 9.8, and (5.11) on the page of Proposition 9.9.

## Items with no single Lean statement

These lemmas have no page: Lean states them in parts.

- Lemma 9.1, finite free models and the inner limit: `ex_limits_inner_limit_finiteFreeModel`,
  `ex_limits_inner_limit_transport`, `ex_limits_inner_limit_cochains`,
  `ex_limits_inner_limit_ultrafilter`, `ex_limits_inner_limit_bounded_ranks` and
  `ex_limits_inner_limit_homotopy_inverse`, for complexes given by their total module.
- Lemma 9.3, evaluation, coefficient change and the outer ring: (5.2) and (5.3) have pages; the crossed
  homomorphism of the product group, the detecting lists, injectivity on $H^1$, injectivity after base
  change and approximate cycles are `ex_limits_outer_evaluation_inner_crossedHom`,
  `ex_limits_outer_evaluation_detecting`, `ex_limits_outer_evaluation_H1_injective`,
  `ex_limits_outer_evaluation_base_change` and `ex_limits_outer_evaluation_approximate_cycles`. The
  comparison of Selmer models on residual $H^0$ and $H^1$ is not formalized.
- Lemma 9.4, the common kernel and a rank-two test: injectivity of restriction to the kernel is
  `isCoboundary_sub_of_restriction_eq`, the rank-two localization at one kernel element is
  `kernel_element_detects_two_classes` (with absolute irreducibility as an ELLIOT hypothesis), and (5.4)
  has a page.
- Lemma 9.5, derivative conditions and the switch, over a field: `derivative_conditions_orthogonal` for
  the four conditions and their orthogonals, `switch_new_H1_spanned` and `switch_equal_valuation`.
- Lemma 9.7, augmentation and the fixed-field budget: (5.6), (5.7) and (5.8) have pages, and the pole
  bound at every sign character is `newLocal_family_pole_genuine`, on the page of (5.8).

## Items with no Lean statement

- (5.7a)–(5.7d), the cohomology of $C_K$ and the triangle $C_K\to D_c\to Q_r$: no declaration proves
  them for $C_K$; they enter as hypotheses of `fixed_field_budget`, the theorem of
  [(5.7)](equation-5-7-fixed-field-budget.md). In the reduction the field `PostLeaves.clearing_model`
  states (5.7d) and the torsion lengths, but replaces (5.7a) by the rank bound of (5.7) itself. The
  bound on $J_r$ of (5.7c) is proved from Frobenius data by `limit_J_length_le_of_moving_character`,
  which the reduction does not use.

## Remaining hypotheses that cover Section 9

These fields of [the remaining hypotheses](../remaining-hypotheses.md) cite lines of Section 9 in their
docstrings, with the kind each docstring gives:

- `PreLeaves.eq35` (ELLIOT and GLUE): the inputs of (3.5), with the size cap of (5.1) and the switch data
  of Proposition 9.6; the reduction builds from it the two process inputs of Proposition 9.6.
- `PostLeaves.prim_regular` (ELLIOT and GLUE): height-one switching data for the primitive coordinates at
  every height-one prime other than $(2)$, the regularity half of Proposition 9.6, asserted also at the
  base of every final family.
- `PostLeaves.clearing_model` (ELLIOT and GLUE): the identification with the full-condition triangle
  (5.6), the cancellation core with the counts of (5.7), and the coordinate identification behind
  Proposition 9.8.

The last two, like every `PostLeaves` field but the address one, are asked in both branches, though the
manuscript builds the final family and its coordinates only in the remaining branch. The missing-address
argument (5.10)–(5.11) needs no field: `missingAddressNode` is proved.

## Sources

- [Section 9](../../../sources/manuscript.md#section-9)
