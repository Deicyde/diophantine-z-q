# The fixed Weierstrass target and Elkik's geometric cusp classes

**Scoped stop at the scheme group law.** The fixed projective Weierstrass model has the chosen period quotient as its space of complex points. The uniformization uses the very same evaluation `weierPt E Lat` as the interior map, including at infinity. On the actual geometric cusp classes of the represented Jacobian, the existing Elkik statement gives a finite generated subgroup. At the given rational scale, a scheme group law inducing Weierstrass addition on the fixed projective model suffices to prove the full comparison required by the Elkik reduction. Extending this group law to scheme morphisms over ℚ remains open.

Here `E = Ecurve ℓ`, `N = newformLevel E`, `J = Additive ((J0 N).Pt Qbar)`, and `[z]` denotes the image of `z` in `ℂ ⧸ Lat.lattice.toAddSubgroup`. The preceding run's model, cusp specializations, and represented Jacobian are unchanged.

The period comparison transports the existing uniformization of the short equation by the change of variables from `(℘,℘′/2)` to the original coefficients of `E`. For the topology, evaluations on the basic affine opens agree on their overlaps. At a lattice point `z₀`, multiplying all three homogeneous coordinates by `(z - z₀)^3` gives the limit `[0:-1:0]` in the chart where the middle coordinate is nonzero. Off the lattice the two ordinary affine coordinates are holomorphic. Compactness of the period quotient and Hausdorffness of the complex points of the fixed projective model make the inverse continuous. All this comparison is on the spot (c), using the proved short-equation uniformization already in the tree.

The remaining algebraic statement concerns the multiplication and inversion morphisms on the fixed projective model. Given this group object, properness is already proved, geometric reducedness follows over the perfect ground field ℚ, and the scheme is smooth by the reduced group-scheme theorem. The rational identity section and integrality of the model give geometric connectedness; smoothness then gives geometric integrality. This passage to the abelian variety package is on the spot (c).

## Statements and consumers

| Declaration | Statement and role |
| --- | --- |
| `shortChange_eq`, `lattice_discriminant`, `shortPointEquiv_toPoint` | The invariant equations in `IsLatticeOf E Lat` identify the short coordinate change with the period-pair equation. Its discriminant is nonzero by ellipticity of `E`. The point equivalence from the change of variables sends the period pair's point of `z` to `weierPt E Lat z`. |
| `weierstrassPeriodEquiv`, `weierstrassPeriodEquiv_mk` | An additive equivalence from `ℂ/Lat` to the usual Weierstrass points of the given `E`, sending the class `[z]` to `weierPt E Lat z`. This fixes the normalization for the interior step of `hAJ`. |
| `weierstrassOrigin_point`, `projectiveValue_eq_zero_iff`, `projectiveValue_bijective` | The specified rational section has underlying point `[0:1:0]`. For any field over ℚ the existing projective evaluation on `Spec F` is bijective onto the Weierstrass points; it is zero exactly above that point. |
| `projectiveValue_vector_affine`, `projectiveValue_vector_origin`, `tendsto_projectiveVectorPoint` | A homogeneous vector in the fixed equation evaluates to `(X/Z,Y/Z)` when `Z ≠ 0` and to zero when `X = Z = 0`. Convergent nonzero solution vectors with nonzero limit give convergent complex scheme points. |
| `projectiveTorusValue_lift`, `projectiveTorusValue_lift_of_eval`, `projectivePeriodHomeomorph`, `continuous_projectiveTorusValue` | The period equivalence yields a homeomorphism with the complex points of the fixed projective model. The inverse on a lifted point is the inverse group equivalence of its coordinate evaluation. Supplies the continuous evaluation and its exact normalization for `hAJ`. |
| `projectiveAbVar`, `projectiveGroup_origin` | A scheme group structure on the fixed Proj makes it an abelian variety over ℚ in the existing package. The underlying object is definitionally that Proj. If its complex points add by the Weierstrass law, its rational identity is the specified section at infinity. |
| `geometricCuspidalSubgroup_finite` | `ElkikPrint.ManinDrinfeldTorsion N (algebraicCuspClass N) → ElkikMD.ManinDrinfeld N (algebraicCuspClass N)`. The existing `algebraicCuspClass_factors` supplies the finite orbit factorization. |
| `hElkikMD_of_geometricTorsion` | Applies `hElkikMD_of_elkikTorsion` with the represented geometric Jacobian group and the actual cusp classes, the orbit factorization, the existing torsion print at those classes, and the weighted comparison. |
| `targetPeriodEquiv`, `targetPeriodEquiv_lift` | For an isomorphism of an abelian variety's underlying scheme with the fixed projective model whose evaluation respects addition, the complex points carry the specified additive period equivalence with its continuous realization. |
| `algebraicCuspClass_comparison_atScale` | At the explicitly rational scale, the at-scale morphism factors through the based Abel–Jacobi map and gives `∃ c : ℚ, c ≠ 0 ∧ (c : ℂ) = κ ∧ ∃ φ : J →+ ℂ/Lat, ∀ r : ℚ, φ (algebraicCuspClass N r) = [(c : ℂ) * ElkikMD.cuspSymbol f.toCuspForm r]`. This supplies `φ` and `hAJ` for every finite rational cusp label, hence for all the weights the reduction uses. |
| `hElkikMD_atScale_of_geometricTorsion`, `hElkikMD_atScale_of_projectiveGroup` | With the explicit scale witness, the existing chosen newform, period pair, genus partner, geometric torsion print, and compatible group realization, the result is `∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar E Lat d`. The last theorem specializes the realization to a law directly on the fixed Proj. |

The chart and topology proofs use the following auxiliary statements. They supply the coordinate and continuity steps of `hAJ`.

| Declaration | Statement |
| --- | --- |
| `evalAway_mk`, `chart_mem_iff`, `evalZero_Y` | If the homogeneous denominator `f` evaluates nonzero under `g`, the localized evaluation of `a/f^n` is `g a/(g f)^n`. On the chart at the coordinate `i`, membership of a homogeneous numerator in the point's ideal is equivalent to vanishing of its localized evaluation. The middle coordinate of `[0:1:0]` evaluates nonzero. |
| `unique_over_origin`, `zOpen_ne_origin`, `range_zOpen` | Every field point over the origin is the base extension of the rational section. The open `Z ≠ 0` is the complement of the origin, and a field point away from the origin factors through that open. |
| `zRingMap_toRingHom`, `value_ne_origin`, `pointInZ_factor` | The coordinate ring map on the affine chart is the one given by `Spec.homEquiv`; `projectiveValue` away from the origin evaluates its two affine generators, and composing the chart point with the open inclusion gives the original point. |
| `vectorEval_coord`, `evalAway_overlap`, `vectorOnChart_independent`, `exists_nonzero_coord`, `projectiveVectorPoint_left` | A vector evaluates each coordinate to its corresponding entry. Restricting evaluation from an overlap to either chart gives that chart's evaluation, so any nonzero coordinate gives the same point; a nonzero vector has such a coordinate. |
| `complexProjection_lift`, `projectiveTarget_t2`, `periodQuotient_compact` | Projection of a lift to the complex base change gives the original morphism over ℚ. The target complex points are Hausdorff and the lattice quotient is compact. |
| `weierstrassCoordinates_nonsingular`, `weierPt_at_lattice`, `weierPt_off_lattice` | On the lattice `weierPt` is zero, and off the lattice it is the affine point with the stated `℘` and `℘′` coordinates, which are nonsingular. |
| `pointVector_equation`, `pointVector_ne_zero`, `pointVector_evaluates`, `complexProjectiveValues_vector` | A Weierstrass point gives a nonzero vector satisfying the homogeneous equation, using any nonzero rescaling on the affine chart. Its associated projective point evaluates back to the same Weierstrass point, and its lift is the inverse of the complex point evaluation. |
| `periodToProjective_continuous` | From the covering plane, the complex projective point corresponding to `weierPt E Lat z` depends continuously on `z`, including at a lattice point. |

No new printed statement or named Prop hypothesis is introduced. The input `GrpObj (projectiveTarget E)` is the algebraic part of tex 1785–1787; it gives morphisms and their algebraic identities, with no smoothness, period identification, or cusp comparison. The separate test on complex points specifies its law independently of all modular data. The optional interface with `A` and a scheme isomorphism gives the same algebraic compatibility as input, and supplies no analytic equality on the source, including at its cusps. The rational-scale witness prescribes only the field of definition of the scalar.

## Exact remaining inputs

| Input | Tex | Owner and size |
| --- | --- | --- |
| The fixed Proj admits a scheme group law inducing its usual Weierstrass addition, as stated below. | 1785–1787 | Missing theory, substantial: represent addition and inversion by regular maps on the fixed Proj over ℚ and prove the group identities. Equivalently one can prove the based Abel–Jacobi identification with its own genus-one Jacobian and identify the transported point law. Field-point group operations alone do not show representability. |
| `hr : ∃ c : ℚ, (c : ℂ) = κ`, with the same `κ` as `hκ : IsParamScale N f.toCuspForm Lat κ`. | 1785–1787, 1825–1828 | Sibling scale-rationality lane. Explicit input of the at-scale construction. |
| `ElkikPrint.ManinDrinfeldTorsion N (algebraicCuspClass N)`. | 2937–2940, 11158–11160 | ELLIOT input through the existing printed statement, subject to the lead's audit. The parameters are now the actual represented Jacobian classes. |
| `[E.IsElliptic]`, `[NeZero N]`, `f : Newform N 2`, `hf : IsNewformOf E f`, `Lat : PeriodPair`, `hLat : IsLatticeOf E Lat`, `hκ : IsParamScale N f.toCuspForm Lat κ`, and `hgp : GenusPartner E d`. | 1761–1787, 1825–1828, 2404–2410, 8247–8254 | Existing curve, modularity, normalization and genus-partner inputs from the ELLIOT assembly. |
| Independently chosen `q_f : J₀(N) → A_f` and `α : A_f → E` over ℚ; on a width-one cusp tail, the projective evaluation of `AJ ≫ q_f ≫ α` equals `weierPt E Lat (κ * eichlerPotential f τ)`. | 1781–1787, 1825–1828 | ELLIOT input for the independent maps and substantial missing theory for their fixed-scale comparison, e.g. its normalized differential and its base value. This is a separate argument. |

The exact remaining Prop for the target uses `X := projectiveTarget E`:
```lean
∃ g : GrpObj X, letI := g
  ∀ p q : AbVar.ptObj (K := ℚ) ℂ ⟶ X,
    projectiveValue (p * q).left = projectiveValue p.left + projectiveValue q.left
```
It has no modular curve, weight, cusp, or scale parameter. Its identity is forced to be the specified projective origin by the evaluated addition law and bijectivity on points. Once the Prop holds, the at-scale comparison gives precisely the remaining geometric input of the Elkik reduction.

The at-scale factor is built after consuming `hr`. The chosen newform has trivial character by `hf`; its existing realization on `Γ₀(N)` has the same underlying function as the newform. This preserves its Fourier coefficients, scale condition, and cusp symbols. Nothing in `RC/ParamJoin` or the AtScale theorems is used to prove rationality of `κ`. The independently specified rational map and its matching tail do not follow from the cusp limit or from factoring the at-scale map. No consequence for the independent rationality reduction on `fc04c16c8` is claimed.

## Known issues

- Inherited source audit: the sources cited at tex 1784 give the quotient and isogeny part, while the normalized-newform statement is covered by Proposition 11.21 in the in-tree Milne audit. The cited pair does not itself give the Hecke equality at tex 1788. The same audit records two unused misprints in Conjecture 11.17.
- The Elkik primary source was not reread. The locator in the manuscript and existing print is taken from the previous audit; it is **UNVERIFIED** here against the primary source. The printed form gives pointwise torsion, from which finiteness follows for the actual finite cusp range.
- As established in the preceding run, rational numbers label geometric cusp orbits; the labels do not assert that all their residue fields are ℚ.
- No additional error was found in the reviewed lines.

## Manuscript check

| Tex | Verdict |
| --- | --- |
| 1779–1784 | Error at 1784, inherited: the cited locator omits the normalized-newform statement; see Known issues. |
| 1784–1787 | Gap filled for the two carriers of the newform: trivial character gives the same function on the `Γ₀(N)` carrier needed by the algebraization. |
| 1785–1787 | Gap filled for the analytic identification: the fixed Proj and the period quotient have compatible complex point evaluation, including at infinity. |
| 1785–1787 | Unverified in Lean: the extension of Weierstrass addition to a scheme group law is the remaining target step. |
| 1781–1787, 1825–1828 | Unverified for the independent map: choosing the maps over ℚ and comparing their composite to the original `κ` on the tail still need the listed input. |
| 2836–2838 | Gap filled given the group law and same scale: the analytic zero limit and faithful point evaluation give algebraic basedness and hence the Albanese factor. |
| 2937–2939 | Gap filled: the represented geometric classes are point-minus-infinity and the class map factors through the cusp orbits. |
| 2940–2942, 11158–11160 | OK as invoked: use the existing torsion print at those classes; finite range gives the finite subgroup. |
| 1825–1828, 7175–7180 | Gap filled given the group law and explicitly rational scale: specialization gives the cusp symbol with the fixed periods and scale, in the form the quadratic reduction uses. |

## Validation

All six new Lean files passed standalone `lake env lean -j1 -DautoImplicit=false` checks after building their imports. All 50 `#print axioms` audits list only `propext`, `Classical.choice`, and `Quot.sound`. The inherited proof files were left unchanged. Per-file outcomes are in `scratch/rc-j0-cusps3/log.md`.
