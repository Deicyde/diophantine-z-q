# The join at the detecting prime

For a prime \(p=\ell_0\equiv3\bmod 4\), `DivisionJoin.identification` identifies the completion of `explicitOrderAt p h` with the integral quaternion order in \(D_p=(-1,-p)_{\mathbf Q_p}\). The algebra equivalence preserves the four coordinates, reduced trace, and reduced norm, and restricts to the stated order equivalence. `DivisionJoin.ramified_maximal` supplies the exact `IsEichler.ramified_maximal` clause for this order. The completed order also carries the transported residue and integral weight rules.

Both directions of the order comparison are explicit: \(2^{-1}\in\mathbf Z_p\) makes the two half-generators integral, while \(j=2((1+j)/2)-1\) and \(ij=2((i+ij)/2)-i\) recover the standard basis. The four standard basis vectors span over \(\mathbf Q_p\). A finite overorder maps to a finite overorder of the model, so the model's maximality applies, even without using the additional spanning hypothesis on the overorder. These comparisons and the weight transport are on-the-spot (c). No printed leaves were added.

All three modules compile individually with `lake env lean`. Their 30 `#print axioms` checks cover every new theorem and the main constructions; only `propext`, `Classical.choice`, and `Quot.sound` occur.

## Statements and interface fields

Names below are in `ZInQ.Manuscript.RC.DivisionJoin`. Write \(A=\mathbf Z_p\), \(K=\mathbf Q_p\), and let \(B_p\), \(R_p\), and \(\mathcal O\) denote `LocalB p`, `completedOrder p h`, and `LocalDivision.order p`. Let \(e\) and \(e_R\) denote the ambient and order equivalences.

| Lean statement or construction | Statement and use |
| --- | --- |
| `ambientEquiv`, `ambientIntegralEquiv` | Coefficient-preserving algebra equivalences \(B_p\simeq_K D_p\) and \(B_p\simeq_A D_p\); the first supplies `DivisionIdentification.ambient`. |
| `reducedTrace`, `reducedNorm` | On \(B_p\) the reduced trace is \(2x_0\) and the reduced norm is the scalar coefficient of \(x\overline{x}\). |
| `ambient_trace`, `ambient_norm` | \(\operatorname{tr}_{D}(e(x))=\operatorname{tr}_{B_p}(x)\) and \(\operatorname{nrd}_{D}(e(x))=\operatorname{nrd}_{B_p}(x)\). These supply `trace` and `norm`. |
| `reducedNorm_formula` | The reduced norm on \(B_p\) is \(x_0^2+x_1^2+p(x_2^2+x_3^2)\), by transport of the model's norm formula. |
| `mem_explicitOrder_cast`, `mem_explicitOrderAt` | The rational order transported from parameter \(1-4m\), and hence the explicit order at \(p\), consists exactly of the integer combinations of \(1,i,(1+j)/2,(i+ij)/2\). The proof unfolds the global lattice basis. |
| `integral_half` | There is a \(t\in A\) whose image in \(K\) is \(1/2\). |
| `mapped_coordinates` | After diagonal inclusion and the ambient equivalence, the four rational coordinates of a global basis combination are cast into \(K\). |
| `quaternion_sum` | Over any commutative ring, the four coordinates of a quaternion express it as the corresponding linear combination of \(1,i,j,ij\). |
| `completion_map`, `completion_mem_iff` | The image of \(R_p\) under \(e\) is \(\mathcal O\) as an \(A\)-subalgebra, and \(x\in R_p\) iff \(e(x)\in\mathcal O\). |
| `orderEquiv` | The restriction \(e_R:R_p\simeq_A\mathcal O\), supplying `DivisionIdentification.order`. |
| `order_compatible` | For each \(x\in R_p\), \(e(x)=e_R(x)\) in \(D_p\) after the two inclusions. This supplies `compatible`. |
| `completion_span` | The \(K\)-span of \(R_p\) is \(B_p\), the fullness part of maximality. |
| `completion_maximal` | \(R_p\) is finite, spans \(B_p\), and contains every full finite \(A\)-subalgebra containing it, i.e. `IsMaximalLocalOrder p R_p`. |
| `ramified_maximal` | For each prime \(q\) with \(q=p\), the completion at \(q\) of `explicitOrderAt p h` is a maximal local order. This has the shape of `IsEichler.ramified_maximal`. |
| `identification` | All five fields assembled in `DivisionIdentification (coordinates p) Rₚ Bₚ Rₚ.val.toRingHom (reducedTrace p) (reducedNorm p)`. |
| `reduction`, `weight`, `uniformizerAction` | The local model's residue homomorphism and weight pulled back by \(e_R\), and its inverse conjugation by the uniformizer transported as a ring automorphism of \(R_p\). |
| `trace_transferred` | The reduced trace of an order element agrees with the trace of its image in \(\mathcal O\). |
| `divisionWeight_eq`, `divisionWeight_nonzero_iff` | At residue \(t\beta\) the weight is the quadratic character of \(t\). On trace zero over a nontrivial coefficient ring it is nonzero iff the residue is nonzero. |
| `divisionWeight_conj`, `divisionWeight_scale`, `divisionWeight_uniformizer` | Order-unit inverse conjugation fixes the weight; multiplication by a scalar unit on trace zero multiplies it by the quadratic character of that unit's residue; inverse conjugation by the division uniformizer on trace zero negates it. |
| `norm_residue_nonzero_square` | For integral trace-zero \(x\) with nonzero residue, the reduced norm is the image of an \(n\in A\) with \(\overline n=t^2\) for a nonzero \(t\in\mathbf F_p\). |

## Known issues

- Tex 8559 equates the characteristic-zero norm \(Q_B(x)\) with the residue-field quantity \(-t^2\beta^2\). As already recorded in the local division report, the left-hand side needs a reduction bar. The claimed square is the nonzero residue of \(Q_B(x)\); the character conclusion uses that residue.
- The Voight reference at tex 8462 (Main Theorem 14.6.1) is **UNVERIFIED** here. No print from it is used.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 8437–8438 | OK | Use \(p\equiv -1\bmod 4\) as the input at the detecting prime; this join does not redo the determinant argument. |
| 8462–8463 | gap filled | At the detecting prime the two coordinate presentations coincide, and the imported division model applies. Other places and the global ramification predicate are outside this proof. |
| 8464–8465 | gap filled | Prove the ramified completion of the explicit order is the full finite maximal order. The other clauses needed to realize level \(N\) are separate. |
| 8496–8497 | OK | On trace zero the reduced norm is \(-x^2\); the identification preserves trace and reduced norm. |
| 8551–8553 | gap filled | Identify the completed order with the order whose residue field and trace-zero line are constructed in the local model, and pull back the character. |
| 8553–8555 | gap filled | Transport trivial order-unit action and the sign of inverse conjugation by the uniformizer, whose residue action is Frobenius. |
| 8556–8558 | OK | The scalar-unit character is the quadratic character of its residue. In the model \(\beta^2=-1\) is nonsquare. |
| 8559 | error | The displayed square identity needs residue reduction on \(Q_B(x)\); the transported norm theorem states the residue identity. |
| 8560–8561 | OK | With \((m/p)=1\), the nonzero square residue gives the local index character. The extraction of the index is outside this proof. |
| 8563–8566 | OK | The imported model provides the compact open ambient extension and the companion local weights layer provides the squareclass adapter; this join transports the integral weight rules. |
