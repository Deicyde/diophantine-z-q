# The detecting-prime division algebra

**Result.** The construction is the quaternion algebra \(D=(-1,-p)_{\mathbb Q_p}\) for a prime \(p\equiv3\pmod4\), with the order on \(1,i,j,ij\). Its reduced norm is anisotropic, and its integral norm locus is the maximal order. The residue map kills precisely \(j\mathcal O\), with quotient \(\mathbb F_{p^2}\); inverse conjugation by \(j\) induces Frobenius. `coordinates p` and `localModel p` inhabit the division-prime interface and give the weight with compact open support and uniformizer sign \(-1\). The model is local. The isomorphisms from the completed global algebra and order remain the join.

## Known issues

- At tex 8559, the displayed equality for \(Q_B(x)\) needs a reduction bar. By tex 8497, \(Q_B(x)\) itself is a characteristic-zero scalar, while \(-t^2\beta^2\) is in the residue field. The argument proves \(\overline{Q_B(x)}=-t^2\beta^2\) and uses only that residue. The squareclass conclusion is unchanged.
- The Voight reference at tex 8462 (Main Theorem 14.6.1, bibliographic pages 223–224 at tex 11243–11244) is **UNVERIFIED** here. No result from it is used as a print. No other source or manuscript error was identified in the local steps checked here.

## Exact join

Set \(p=\ell_0\) using primality and the congruence in tex 8437. The global lane supplies the quaternion algebra ramified precisely at \(p\) and infinity and its Eichler order of level \(N\). For the explicit rational presentation \((-1,-\ell_0)_{\mathbb Q}\), identify its scalar extension by extending the four coefficients in the basis \(1,i,j,ij\). This must be a \(\mathbb Q_p\)-algebra equivalence, and the corresponding trace and norm must be the polynomial expressions \(2x_0\) and \(x_0^2+x_1^2+p(x_2^2+x_3^2)\). For a different presentation, supply an equivalence to this one.

For the completed order \(R_p=R\otimes\mathbb Z_p\), completed algebra \(B_p=B\otimes\mathbb Q_p\), and their inclusion `incl : R_p →+* B_p`, supply `DivisionIdentification (coordinates p) R_p B_p incl trB nrdB`:

- `order : R_p ≃ₐ[ℤ_[p]] order p` and `ambient : B_p ≃ₐ[ℚ_[p]] D p`;
- `∀ x : R_p, ambient (incl x) = (order x).val`;
- `∀ x : B_p, tr (ambient x) = trB x` and `∀ x : B_p, nrd (ambient x) = nrdB x`.

For instance, identify the image of \(R_p\) as the integral norm locus. The local maximality result can also be used after showing the image is a maximal finite order: every finite subalgebra of the local algebra lies inside this order. Use the transported residue coordinate and the element \(j\) for the model normalization. The split identifications and the action on \(P_M\) are outside this work.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 8343–8345, 8357–8360, 8437 | OK | The determinant is \(-1\) modulo four on the detecting Frobenius. The construction assumes the resulting congruence and does not redo the Galois argument. |
| 8462–8465 | gap filled | The explicit completion is division by the parity calculation; the compact open maximal order is constructed locally. Global ramification and the identification with the global order remain at the join. |
| 8496–8497 | OK | Extend by zero on the ambient trace-zero space; on trace-zero elements the reduced norm equals \(-x^2\). |
| 8551–8553 | gap filled | The maximal-order residue field and its trace-zero coordinate are given by reducing the first two coefficients. |
| 8553–8555 | gap filled | Residue is commutative; conjugation by \(j\) negates the coefficient of \(i\) and induces Frobenius. \(\beta^p=-\beta\) gives the sign. |
| 8556–8558 | OK | Scalar reduction gives the Legendre scaling factor, and \(\beta^2=-1\) is nonsquare in \(\mathbb F_p\). |
| 8559 | error | Insert a reduction bar on \(Q_B(x)\). The calculation of its nonzero square residue is correct. |
| 8560–8561 | OK | With the stated \((m/p)=1\), the square residue gives the indicated character of the extracted index. This work supplies the local norm calculation. |
| 8563–8564 | gap filled | The order is compact open in the product topology; its residue map is locally constant, giving compact open ambient support. |
| 8564–8566 | OK | The inherited squareclass adapter uses the locally constant unit-squareclass test and the norm changes by a square under unit scaling. |

The explicit coordinate algebra, parity argument, integral order, topology, and residue calculations are on-the-spot (provenance (c)). No prints were added.

## Theorem statements and interface fields

The namespace is `ZInQ.Manuscript.RC.LocalDivision`. Write \(K=\mathbb Q_p\), \(A=\mathbb Z_p\), \(F=\mathbb F_p\), and \(\mathcal O=\texttt{order p}\). Norm signs \(\lVert\cdot\rVert\) refer to the ordinary real-valued \(p\)-adic norm. The source contains the exact Lean statements and checks, including private helpers.

[Valuation.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalDivision/Valuation.lean) supplies the division-ring hypothesis and the estimates used in `maximal_order` and `red_nonunit`.

| Theorem | Statement |
| --- | --- |
| `neg_one_nonsquare` | For \(p\equiv3\pmod4\), \(-1\) is not a square in \(F\). |
| `residue_sum_sq_eq_zero` | In \(F\), \(a^2+b^2=0\) iff \(a=b=0\). |
| `padic_red_eq_zero_iff` | For \(a\in A\), \(\bar a=0\) iff \(\lVert a\rVert<1\). |
| `norm_one_add_sq` | If \(\lVert a\rVert\le1\), then \(\lVert1+a^2\rVert=1\). |
| `norm_pair_of_le` | If \(\lVert b\rVert\le\lVert a\rVert\), then \(\lVert a^2+b^2\rVert=\lVert a\rVert^2\). |
| `norm_pair`, `valuation_pair_even` | \(\lVert a^2+b^2\rVert=\max(\lVert a\rVert,\lVert b\rVert)^2\), and its additive valuation is even (using Lean's zero convention at zero). |
| `norm_four` | \(\lVert a^2+b^2+p(c^2+d^2)\rVert=\max(\max(\lVert a\rVert,\lVert b\rVert)^2,\lVert p\rVert\max(\lVert c\rVert,\lVert d\rVert)^2)\). |

[Algebra.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalDivision/Algebra.lean) supplies `tr`, `nrd`, `rank_four`, `tr_continuous`, `tr_conj`, `scalar_compat`, and the division ring and Hausdorff space.

| Theorem or construction | Statement |
| --- | --- |
| `scalar_compat` | The scalar map from \(A\) agrees with its inclusion into \(K\) followed by the scalar map from \(K\). |
| `coordHomeomorph`, `rank_four` | \(D\) is homeomorphic to \(K^4\) by its coordinates, and its \(K\)-dimension is four. |
| `tr_apply`, `tr_continuous` | \(\operatorname{tr}(x)=2x_0\); this linear map is continuous. |
| `tr_mul_comm`, `tr_conj` | \(\operatorname{tr}(xy)=\operatorname{tr}(yx)\); \(\operatorname{tr}(u^{-1}xu)=\operatorname{tr}(x)\) for \(u\in D^\times\). |
| `mul_star_eq`, `star_mul_eq`, `nrd_mul_star` | The products \(x\bar x\) and \(\bar x x\) are the scalar given by the real coordinate of \(x\bar x\), which is the value of `nrd`. |
| `nrd_formula`, `nrd_continuous`, `nrd_conj` | The norm is \(x_0^2+x_1^2+p(x_2^2+x_3^2)\), continuous and invariant under inverse conjugation. Multiplicativity is part of the definition of `nrd`. |
| `nrd_algebraMap`, `nrd_smul` | The norm of a scalar \(a\) is \(a^2\); scalar multiplication by \(a\) multiplies the norm by \(a^2\). |
| `tr_zero_sq` | At trace zero, the norm embedded in \(D\) equals \(-x^2\). |
| `norm_nrd`, `nrd_eq_zero` | `norm_four` applied to the coordinates of \(x\) gives \(\lVert\operatorname{nrd}(x)\rVert\); \(\operatorname{nrd}(x)=0\) iff \(x=0\). |
| `unitOfNonzero`, `inv_formula` | For \(x\ne0\), \(\bar x/\operatorname{nrd}(x)\) is a two-sided inverse, and it equals the inverse of the resulting division ring. |

[Order.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalDivision/Order.lean) supplies `order`, `order_open`, `order_compact`, `finite_order`, `maximal_order`, `norm_units`, and `norm_units_eq`.

| Theorem or construction | Statement |
| --- | --- |
| `includeIntegral_injective`, `coe_orderEquiv`, `includeIntegral_symm` | The coefficientwise inclusion is injective. The equivalence with its image and its inverse recover that inclusion and the underlying ambient element, respectively. |
| `mem_order`, `finite_order` | Membership is the integrality of all four coefficients, and the order is finite over \(A\). |
| `order_open`, `order_compact`, `orderCoord_continuous` | The order is open and compact, and its four \(A\)-valued coordinates are continuous. |
| `norm_le_one_of_weighted_sq` | \(\lVert p\rVert\lVert a\rVert^2\le1\) implies \(\lVert a\rVert\le1\) by discreteness. |
| `mem_order_iff_nrd`, `mem_order_iff_valuation` | \(x\in\mathcal O\) iff \(\lVert\operatorname{nrd}(x)\rVert\le1\), equivalently \(v_p(\operatorname{nrd}(x))\ge0\). |
| `nrd_valuation_mul`, `norm_nrd_add_le_max` | The norm valuation is additive on products of nonzero elements; the real norm of the reduced norm obeys the ultrametric bound on sums. |
| `integral_mem_order`, `maximal_order` | Every element integral over \(A\) lies in \(\mathcal O\); a finite subalgebra containing \(\mathcal O\) equals \(\mathcal O\). |
| `exists_integralTrace` | The reduced trace of an order element is the image of an element of \(A\). |
| `normUnits_eq`, `orderUnit_iff_norm` | The integral norm homomorphism on order units gives the ambient norm after coercion. An order element is a unit iff its reduced norm has norm one. |

[Residue.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalDivision/Residue.lean) supplies `red`, `red_surj`, `red_scalar`, `red_locallyConstant`, `red_nonunit`, `beta`, `beta_ne_zero`, `trace_line`, `uniformizer`, `uniformizer_order`, `uniformizer_conj`, `uniformizer_frobenius`, `uniformizer_norm`, and `beta_frobenius`.

| Theorem or construction | Statement |
| --- | --- |
| `quadReduction_surj`, `quadReduction_zero_iff` | Reduction to \(F[i]\) is onto; it vanishes precisely on elements \(j y\) with \(y\) integral. |
| `padicReduction_locallyConstant` | Ordinary reduction on \(A\) is locally constant: its fibers are open balls of radius one. |
| `residueQuotientEquiv`, `red_surj`, `red_ker_maximal` | The quotient by the kernel of `red` is isomorphic to \(\mathbb F_{p^2}\), `red` is onto, and the kernel is maximal. |
| `red_i`, `beta_sq`, `beta_ne_zero`, `beta_frobenius` | \(\operatorname{red}(i)=\beta\), \(\beta^2=-1\), \(\beta\ne0\), and \(\beta^p=-\beta\). |
| `red_apply`, `red_scalar`, `red_locallyConstant` | \(\operatorname{red}(x)=\overline{x_0}+\overline{x_1}\beta\); scalars reduce ordinarily, and `red` is locally constant. |
| `red_eq_zero_iff`, `red_ker_j` | \(\operatorname{red}(x)=0\) iff both of the first two coefficients reduce to zero, equivalently iff \(x\in j\mathcal O\). |
| `integralNorm_red`, `red_nonunit` | The norm reduces to \(\overline{x_0}^2+\overline{x_1}^2\); the kernel consists exactly of the nonunits of \(\mathcal O\). |
| `trace_line` | If \(\operatorname{tr}(x)=0\), there is \(t\in F\) with \(\operatorname{red}(x)=t\beta\). |
| `nrd_j`, `uniformizer_norm` | \(\operatorname{nrd}(j)=p\), of valuation one. |
| `conjugateInOrder_inverse`, `uniformizer_conj` | Inverse conjugation by \(u\) on the order is undone by inverse conjugation by \(u^{-1}\); the chosen order equivalence is inverse conjugation by \(j\). |
| `uniformizer_coords`, `uniformizer_frobenius` | Inverse conjugation by \(j\) sends \((a,b,c,d)\) to \((a,-b,c,-d)\); it induces \(z\mapsto z^p\) on the residue field. |

[Quadratic.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalDivision/Quadratic.lean) describes \(K(i)\subset D\) and explains the unramified quadratic construction used for the residue coordinates. Its integral closure has maximal ideal generated by \(p\), and its residue extension is separable of degree two. The assembly itself uses the direct coordinate calculation in `Residue.lean`.

| Theorem or construction | Statement |
| --- | --- |
| `padic_neg_one_nonsquare`, `quadratic_rank` | \(-1\) is not a square in \(K\); the resulting quadratic field has dimension two. |
| `quadraticInclusion_apply`, `quadraticInclusion_injective` | The field embeds as the first two coordinates, with the last two zero. |
| `quadraticInclusion_j` | For \(z\in K(i)\), \(jz=\bar z j\). |
| `quadratic_integral_iff` | An element of \(K(i)\) is integral over \(A\) iff both coefficients are in \(A\). |
| `quadraticRed_surj`, `quadraticRed_ker`, `quadraticRed_nonunit` | Coefficient reduction on the quadratic integral model is onto \(F[i]\) and vanishes exactly on \((p)\), the nonunits. |
| `quadratic_maximalIdeal`, `quadraticResidueEquiv` | The maximal ideal is \((p)\); the quotient is \(\mathbb F_{p^2}\). |
| `quadratic_residue_degree`, `quadratic_residue_separable` | \(\mathbb F_{p^2}/F\) has degree two and is separable. |

[Model.lean](../../ZInQKernel/Contrib/OneProof/RC/LocalDivision/Model.lean) assembles `coordinates p : DivisionCoordinates p (D p)` and `localModel p : DivisionLocalModel (coordinates p)`. The resulting claims use only primality and \(p\equiv3\pmod4\). Write \(w\) for the integral weight, \(f\) for its extension by zero, and \(\chi\) for the quadratic character of \(F\).

| Theorem or construction | Statement |
| --- | --- |
| `divisionWeight_eq`, `divisionWeight_nonzero_iff` | If \(\bar x=t\beta\), then \(w(x)=\chi(t)\). On trace-zero elements over a nontrivial coefficient ring, \(w(x)\ne0\) iff \(\bar x\ne0\). |
| `norm_residue_nonzero_square` | For trace-zero \(x\) with \(\bar x\ne0\), the reduced norm has residue \(t^2\) for some \(t\ne0\) in \(F\). |
| `divisionWeight_conj`, `divisionWeight_scale`, `divisionWeight_uniformizer` | \(w(u^{-1}xu)=w(x)\) for order units, \(w(vx)=\chi(\bar v)w(x)\) for scalar units on trace zero, and \(w(j^{-1}xj)=-w(x)\) on trace zero. |
| `divisionSchwartz_compactOpen`, `divisionSchwartz_uniformizer`, `divisionRule` | \(f\) is locally constant with compact open support. Inverse conjugation by \(j\) multiplies it by \(-1\) on the full trace-zero space, and `divisionRule` gives the ambient order-unit and scalar-unit rules. |

All six modules compile individually with `lake env lean`. The 87 new theorems and 8 additional construction checks report only `propext`, `Classical.choice`, and `Quot.sound`.
