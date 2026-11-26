---
article_id: af_784b0f3cb252c33f9cb7089a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Determinant.fixed_field_budget, ZInQ.Contrib.CloudB3RC53.RankCounts.budget_rank
---

# (5.7): the fixed-field budget

Fix the final imaginary quadratic field $K$. Let $C_K$ be the Kummer Selmer complex of $T_2E$ over $K$,
$d_K=\dim_{\mathbb F_2}\mathrm{Sel}_2(E/K)$, $t_K=\operatorname{length}E(K)[2^\infty]$,
$h_K=\operatorname{length}H^2(C_K)_{\rm tors}$, $D_c=C_{\rm old}\otimes^{\mathbf L}_\Lambda\mathbb Z_2$, and $c_E$
the constant of the moving character. Assume, as hypotheses of the theorem that no Lean declaration
proves for the actual complexes:

- (5.7a) (ELLIOT): $C_K\otimes^{\mathbf L}\mathbb F_2$ has cohomology of dimensions $(2,d_K,d_K,2)$ in
  degrees $0$ to $3$;
- (5.7b), with the identification before it (ELLIOT): $H^1(C_K)_{\rm tors}$ and $H^3(C_K)$ have length
  $t_K$; and $H^2(C_K)_{\rm tors}$ has length $h_K$ (`hh`, the definition of $h_K$);
- for `budget_rank` also the free ranks one of (5.7b) (`hr₁`, `hr₂`, ELLIOT): $H^1(C_K)$ and $H^2(C_K)$
  have free rank one;
- (5.7c) (ELLIOT): the triangle $C_K\to D_c\to Q_r\to C_K[1]$, used through the exactness of its
  reduction modulo two, the bound eight for the two singular disks, $H^0(D_c)=0$ and
  $\operatorname{length}J_r\le2c_E$ for $J_r=H^2(Q_r)$;
- (5.7d) (ELLIOT): $H^1(D_c)\cong H^1(C_K)$ and the exact sequence
  $0\to H^2(C_K)\to H^2(D_c)\to J_r\to H^3(C_K)\to H^3(D_c)\to0$;
- that the model of $C_{\rm old}$ has total rank at most the total dimension of the cohomology of
  $D_c\otimes\mathbb F_2$ (`hmodel`, ELLIOT);
- that the model has a Smith decomposition with one free generator in each of degrees one and two and
  $m$ disks (`hsmith`, the Smith decomposition).

Then, with $h_1=\sum_i\operatorname{length}H^i(D_c)_{\rm tors}$,
$$\operatorname{rank}_{\rm tot}C_{\rm old}\le2d_K+12,\qquad m\le d_K+5,\qquad h_1\le h_K+2c_E+2t_K.\tag{5.7}$$
These bounds depend only on $K$ and the old data, not on the binary dimension or the graph.

`fixed_field_budget` is linear algebra over abstract vector spaces and modules that carry these
hypotheses. `budget_rank` is the form for the Smith data of the remaining complex: from the rank bound,
(5.7d), the torsion lengths, the bound on $J_r$ and free ranks one in degrees one and two, it gives the
other two bounds, with $h_1$ the sum of the valuations of the Smith entries.

The reduction of Theorem 5.3 does not use `fixed_field_budget`. The first bound of (5.7),
$\operatorname{rank}_{\rm tot}C_{\rm old}\le2d_K+12$, is an ELLIOT input of the reduction, in place of
(5.7a) and the mod-2 count of (5.7c) from which the manuscript derives it: the field
`PostLeaves.clearing_model` of [the remaining hypotheses](../remaining-hypotheses.md) supplies it,
together with (5.7d), the torsion lengths, the free ranks one and the bound on $J_r$, and `budget_rank`
derives only the other two bounds, inside the proof of [Proposition
9.8](proposition-9-8-common-denominator.md).

**Proof sketch.** By (5.7a) and the reduction of (5.7c), the cohomology of $D_c\otimes\mathbb F_2$ has
total dimension at most $(2d_K+4)+8$, which bounds the rank; the rank is $2+2m$, so $m\le d_K+5$. By
(5.7d), $H^1(D_c)_{\rm tors}$ has length $t_K$, the torsion of $H^2(D_c)$ has length at most
$h_K+\operatorname{length}J_r$, and $H^3(D_c)$ is a quotient of $H^3(C_K)$; adding gives the bound on $h_1$.

## Depends on

- [The remaining hypotheses](../remaining-hypotheses.md)

## Sources

- [Section 9](../../../sources/manuscript.md#section-9)
