# Appendix F: explicit ramification and the level-one split profile

For a prime \(\ell_0\equiv3\pmod4\), the explicit algebra \((-1,-\ell_0)_{\mathbb Q}\) has the Appendix F ramification predicate. At every finite prime \(p\ne\ell_0\), an explicit algebra equivalence takes the completion of the order on \(1,i,(1+j)/2,(i+k)/2\) onto \(M_2(\mathbb Z_p)\). The level-one `IsEichler` statement takes the ramified maximality clause as its only additional input.

The constructions are on-the-spot (provenance (c)). Away from \(\ell_0\), choose \(A,B\in\mathbb Z_p\) with \(u=2A-1, v=2B, u^2+v^2=-\ell_0\). For odd \(p\), the residue field represents \(-\ell_0\) as a sum of two squares. At least one coordinate is nonzero, so the derivative in that coordinate is a unit and Hensel lifts it with the other coordinate fixed. At \(p=2\), take \(v\) equal to zero or two so \(-\ell_0-v^2\equiv1\pmod8\). Hensel at one gives a square root \(u\equiv1\pmod2\). The tuple \((u,v,1,0)\) is an isotropic vector at both kinds of prime. At \(\ell_0\) the existing local division norm theorem gives anisotropy, and at infinity the existing positivity proof applies.

The matrix homomorphism sends \(i\) to \(\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)\) and \(j\) to \(\left(\begin{smallmatrix}u&v\\v&-u\end{smallmatrix}\right)\). In the order basis, a vector \((c_0,c_1,c_2,c_3)\) goes to
\[
\begin{pmatrix}
c_0+Ac_2-Bc_3 & -c_1+Bc_2+(A-1)c_3\\
c_1+Bc_2+Ac_3 & c_0+(1-A)c_2+Bc_3
\end{pmatrix}.
\]
The difference of the diagonal entries and sum of the off-diagonal entries recover \(c_2,c_3\) by a two-by-two system with determinant \(u^2+v^2=-\ell_0\). The other coordinates follow from the first column. Since the determinant is a unit at \(p\ne\ell_0\), this gives both inverse directions over \(\mathbb Z_p\), including at two.

## Lean statements

All four Lean files compiled individually with `lake env lean`. All 15 theorem axiom checks report only `propext`, `Classical.choice`, `Quot.sound`.

Names below are in `ZInQ.Manuscript.RC.ExplicitSplit`. Implicit prime instances are suppressed in the descriptions.

| Theorem | Statement and clause supplied |
|---|---|
| `unit_natCast` | If \(p\nmid n\), the image of \(n\) in \(\mathbb Z_p\) is a unit; used for the odd prime parameter construction. |
| `odd_sum_sq` | For \(p\ne2\) every unit \(s\in\mathbb Z_p\) is \(x^2+y^2\) with integral \(x,y\); supports the finite ramification and split clauses. |
| `dyadic_square_near_one` | If \(8\mid1-s\) for \(s\in\mathbb Z\), some \(A\in\mathbb Z_2\) satisfies \((2A-1)^2=s\); supports both clauses at two. |
| `integral_parameters` | For \(\ell_0\) prime, \(\ell_0\equiv3\pmod4\), and \(p\ne\ell_0\), there are integral \(A,B\) with \((2A-1)^2+(2B)^2=-\ell_0\). |
| `anisotropic_at_ell` | `AppF.NormFormAnisotropic ℚ_[ell] (-1) (-ell)`, with rational parameters cast to the local field; the reverse implication of the finite-place clause at the detecting prime. |
| `isotropic_away` | For \(p\ne\ell_0\), negation of `AppF.NormFormAnisotropic ℚ_[p] (-1) (-ell)`, with the same casts; the forward implication of the finite-place clause. |
| `explicit_ramifiedExactlyAtEll0Infty` | `AppF.RamifiedExactlyAtEll0Infty ell (-1) (-(ell : ℚ))` for prime `ell` with `ell % 4 = 3`; all clauses including nonzero parameters and the real place. |
| `completion_span` | The module underlying `(explicitOrder m).completion p` is the local integer span of the coordinate basis `Basis.ofEquivFun (localCoords p (1 - 4 * m))`. |
| `completion_coeffs` | Membership in `(explicitOrderAt ell h).completion p` is equivalent to being the inverse coordinate image of a vector in `Fin 4 → ℤ_[p]`. |
| `decode_encode`, `encode_decode` | Over any commutative ring, if \(r((2A-1)^2+(2B)^2)=1\), the displayed coordinate map and the inverse using \(r\) are mutual inverses on coordinate vectors and matrices. |
| `encode_map` | Applying a ring homomorphism to the entries of the coordinate matrix agrees with applying it to \(A,B,c_0,c_1,c_2,c_3\) first. |
| `lift_eq_encode` | Over a characteristic-zero field, with quaternion parameters \((-1,u^2+v^2)\), the quaternion lift with the displayed generators acts by the displayed matrix formula in the order coordinates. |
| `explicit_split_profile` | For each prime `p ≠ ell`, there is `f : Bp p (-1) (-(ell : ℚ)) ≃ₐ[ℚ_[p]] M2 ℚ_[p]` with `f '' ((explicitOrderAt ell h).completion p : Set _) = standardLevel p 0`; exactly the split field at level one after simplifying `1.factorization p`. |
| `explicit_isEichler_of_ramified_maximal` | Given `∀ (p : ℕ) [Fact p.Prime], p = ell → IsMaximalLocalOrder p ((explicitOrderAt ell h).completion p)`, gives `IsEichler ell 1 (explicitOrderAt ell h)`. |

## Known issues

- No new manuscript error was identified in the steps checked here. The inherited issue at tex 8559 is outside the split calculation: the residue equality needs a reduction bar on \(Q_B(x)\), as recorded in [the local division report](rc-local-division.md).
- Voight Main Theorem 14.6.1 is the locator from the manuscript. Its printed text and locator are **UNVERIFIED** here. The existing `AppF.VoightMainThm1461` remains unchanged and is not used as an assumption.
- Maximality at the detecting prime, levels above one, the adelic identification, and the neighbour indexing are separate work. No new prints are introduced.

## Manuscript check

| Tex lines | Step | Verdict |
|---|---|---|
| 8437 | Use \(\ell_0\equiv-1\pmod4\) for the detecting prime. | OK: the proof takes the congruence furnished by the determinant as input. |
| 8462–8463 | Choose the quaternion algebra with ramification set \(\{\ell_0,\infty\}\). | gap filled: the explicit choice is verified by the norm form at all places; the manuscript uses the general Voight citation. |
| 8464–8465, 8468–8469 | Choose the Eichler order at level one, allowing the local place two. | gap filled: the split profile is constructed at all \(p\ne\ell_0\), including two. The corollary takes the ramified maximality clause; arbitrary level is outside scope. |
| 8465–8466 | Identify the supersingular pairs by the adelic quotient. | unverified: the adelic comparison is outside scope. |
| 9040–9041 | Use the integral matrix model at a good prime. | gap filled: the integral image equality is proved for the explicit level-one order. |
