# Cusp specialization on the normalized modular curve

**The source specialization, geometric cusp assignment, and based Jacobian are proved.** The `S`-translated chart converges in the complex scheme topology to the rational point `zeroPoint N`. Every cusp orbit has an assigned point over the algebraic closure of ℚ in ℂ, characterized by the source limit for any of its integral labels. The cusp classes in the represented Jacobian supply `hCuspFactor` for the Elkik reduction. The weighted identity on these actual classes follows from the compatible target realization and the existing analytic limits; the realization of the fixed elliptic target and the independent rational-map comparison remain open.

The source is `Over.mk (X0Model.overQ N)`, definitionally `Over.mk (X0Branch.model N).overQ`. Its interior point has the same underlying scheme map as `(X0Branch.model N).complexPoint`. The specialization uses only the underlying scheme and chart.

The rational function field of the model is `ℚ(j(q), j(q^N))`. The width-one branch is the given inclusion into `ℚ((q))`. The width-`N` branch for the zero cusp sends the two generators to `j(q^N), j(q)`, respectively. This choice uses the modular polynomial at the triangular representative `(1,0,N)`. The closed point of the valuative lift lies on the normalization; the two poles would give no such identification on their own. For the general orbit, a triangular representative of `diag(N,1) σ` yields the Laurent substitution with a root of unity in the algebraic closure of ℚ inside ℂ.

The topological argument works on an affine open containing the formal limit. The formal arc evaluates sections in power series; the two generator expansions propagate to the function field. Finitely many generators of the affine coordinate ring then land in each interior meromorphic valuation ring on one common tail. The interior arc factors through the affine open by uniqueness of the valuative lift. Each section converges to its constant coefficient, which proves the desired convergence in the complex scheme topology. These are on-the-spot steps (c) for tex 1785–1787 and 2937–2939.

The source statements use the full `atImInfty` filter. In particular, for every `N` with `[NeZero N]`, the limits are

```lean
Tendsto (fun τ : ℍ => complexLift (interior N (ModularGroup.S • τ))) atImInfty
  (𝓝 (complexLift (branchComplex N (Rat.castHom ℂ) (zeroField N))))

Tendsto (fun τ : ℍ => complexLift (interior N (σ • τ))) atImInfty
  (𝓝 (complexLift (extendPoint (algebraicCusp N (orbitOfSL N σ)))))
```

## Statements

| Declaration | Statement and role |
|---|---|
| `powerSeries_analytic_sum`, `tendsto_powerSeries_eval` | Convergence at one nonzero input gives an analytic sum at zero with constant coefficient as value; convergent evaluations along a filter approaching zero have the same limit. Scalar part of the source specialization for `hAJ`. |
| `maps_to_rat_unique`, `sectionMap_factor`, `tendsto_specPoint`, `tendsto_complexLift_of_sections` | Two affine scheme maps to `Spec ℚ` agree. The evaluation on sections factors a point through an affine open. Pointwise convergence of ring maps on an affine scheme gives convergence of their complex lifts; a common eventual affine neighborhood and convergent section evaluations therefore suffice on any ℚ-scheme. Topological part of the source specialization. |
| `triangularField_j`, `triangularField_jN`, `zeroField_j`, `zeroField_jN`, `formalBranch_generic`, `zeroPoint_overQ` | The triangular Laurent realization with `a * d = N` sends `j` to `j(q^N)` and `j_N` to the expansion with exponent multiplier `a^2` and twist `ζ_N^(a*b)`. For the rational width-`N` realization these are `j(q^N)` and `j(q)`. The generic point of a formal arc is the specified field realization, and the zero branch's closed point is a section over ℚ. Supplies the algebraic point in the source hypothesis of `hAJ`. |
| `branch_expansion`, `sourceLimit_of_generator_expansions` | For a filter with nonzero parameter tending to zero, the two scalar generator expansions imply convergent expansions of every rational function, analytic at the interior chart parameters eventually. The complex points of that chart converge to the special point of the indicated formal branch. These hypotheses are about scalar Laurent sums and do not give a scheme limit, cusp evaluation, elliptic curve, or group map. |
| `analyticJ_invariant`, `tendsto_infinity`, `tendsto_zero` | The analytic first coordinate is invariant under the full modular group. The chart and its `S`-translate converge on the normalization to the rational width-one and zero branches, respectively. These are the source inputs for basedness and the weighted `hAJ`. |
| `exists_primitive_triangular`, `exists_algebraic_cusp_limit` | An integral matrix of positive determinant `N` with primitive bottom row reduces on the left to a primitive triangular representative. Every integral modular translate of the chart then converges to the complex extension of the closed point of a branch over the algebraic closure of ℚ in ℂ. Supplies existence of genuine all-cusp data for the print. |
| `t2_of_affine_pair`, `source_t2`, `source_limit_unique` | Complex points are Hausdorff if every pair lies in a common affine open; the modular curve satisfies this condition. Two complex lifts which are limits of the same chart tail determine the same scheme point. Used for endpoint identifications. |
| `model_smooth_one` | The specified source is smooth of relative dimension one, which supplies the curve input to the represented Jacobian construction. |
| `orbitOfSL_surjective`, `orbitOfSL_eq`, `algebraicCusp_limit`, `algebraicCusp_zero`, `algebraicCusp_infinity` | The modular labels map onto the existing cusp orbit quotient, agreeing with the orbit of `σ∞`. Every label tends to the complex extension of the assigned geometric point. The assignments at zero and infinity have the same complex extension as the specified rational points. |
| `extendPoint_injective`, `algebraicCusp_zero_rational`, `algebraicCusp_infinity_rational` | Scalar extension to ℂ is injective for separated targets. The geometric assignments at zero and infinity descend to the specified rational points. |
| `cuspAssignment_zero_limit` | The source chart at `S` converges to the assigned actual point at zero; this discharges the source hypothesis of the previous weighted comparison. |
| `cusp_comparison_of_factor` | For a group morphism with `aj ≫ g = π`, compatible continuous torus evaluation, an interior comparison and the analytic limits, the induced homomorphism on geometric points sends every finite rational cusp label to its prescribed analytic limit. This supplies the specialization used in `hAJ`. |
| `cusp_at_infinity_maps_to_unit` | For an injective additive uniformization with its continuous realization, the interior comparison and the analytic zero limit at infinity imply `X0Model.cusp N ≫ π.left = (η[A.X]).left`. This supplies the basedness equation needed by the Albanese factor. |
| `aj0_classifies`, `isJacobian_aj0` | For any parameter point `p : B ⟶ source N`, `p ≫ aj0 N` represents the pullback of the diagonal-minus-marked-section Picard class. At a geometric cusp this is `[c] − [∞]`. The morphism has the based Jacobian universal property at the rational width-one point. Supplies the actual group `Additive ((J0 N).Pt Qbar)` for the Elkik reduction. |
| `algebraicCuspClass_factors` | `algebraicCuspClass N r = classOfCusp N (aj0 N) (algebraicCusp N) (ElkikPrint.cuspOrbit N r)`. This is `hCuspFactor` with the actual geometric cusp classes. |
| `modularFactor_isMonHom`, `aj0_comp_modularFactor` | A based `π : source N ⟶ A.X` factors as `aj0 N ≫ modularFactor N π hb`; the factor is a group scheme homomorphism. |
| `cusp_comparison`, `weighted_comparison`, `weighted_comparison_from_limits` | The induced additive homomorphism `φ : Additive ((J0 N).Pt Qbar) →+ T` sends `algebraicCuspClass N r` to `lim r` for every finite rational label. The weighted form gives the equality for `r = a/m`, `a < m`, `jacobiSym (a : ℤ) m ≠ 0`. The last theorem derives the required basedness from the analytic zero limit and injectivity of the compatible additive uniformization. Supplies `φ` and the weighted identity for `hAJ`. |

The local theorem statements used by these proofs are:

- `tensorPoint_eq`: base change of an affine point is represented by the tensor evaluation for its ring map.
- `liftEquation`, `triangular_root`, `zero_root`: a root of the specialized modular relation is a root of the transported minimal polynomial of `j_N`; the triangular substitutions give such roots, and the zero substitution does so over ℚ. The two generator evaluations and the compatibility with polynomial evaluation are `liftBranch_j`, `liftBranch_jN`, `firstAtCusp_j`, and `firstAtCusp_eval`.
- `fieldGerm_first`, `germ_inverse`: the first generator evaluates to its meromorphic germ; the inverse germ of an analytic function nonzero at the chart point is analytic there.
- `preimage_top_comp`, `regular_interiorSection`, `chart_mem_of_regular`, `eventually_chart_mem`, `generic_hits_open`, `chart_section_value`, `sectionValue_comp`: a preimage that is the whole scheme remains so under precomposition; analytic representatives of sections give germs in the interior valuation ring; regular substitutions on generators put the chart on the common affine open; the generic point is in the open containing the specialization; evaluation of sections commutes with specialization and scalar extension.
- `qParam_one_zpow`, `qParam_at_cusp`, `dilate_S_dilate`, `dilate_contract`, `tendsto_contract`: integer powers of the width-one parameter are exponential terms; the width parameter tends through nonzero values to zero at infinity; dilation with `S` satisfies the width-`N` change of parameters, and its inverse dilation preserves the cusp filter.
- `exists_cusp_root`, `qParam_level_pow`, `hasSum_first`, `second_form`, `coeffMap_qExpand`, `coeffMap_qTwist`, `translated_generator_expansions`: the root of unity for the triangular substitution is algebraic; the width-one parameter is the `N`-th power of the width-`N` parameter; both coordinates have the convergent triangular expansions; coefficient embeddings commute with their expansion and twist operators.
- `evaluation_eq_sectionMap`, `complexLift_injective`, `rat_label_real`, `translated_limit_congr`, `extend_rationalAsGeometric`, `extendJacobian_class`: evaluating a section by its germ equals evaluating its restriction to the point; the complex lift is injective; modular cusp labels commute with the embedding ℚ → ℝ; equivalent labels yield the same limit; both coordinate extensions of a rational point agree; extending the coordinates of a class commutes with applying Abel–Jacobi.
- `modelPicard_exists`: the degree-zero Picard sheaf of this particular source has a tensor-compatible representation by an abelian variety over ℚ, by the existing Jacobian package.

No theorem takes a new structure or named proposition as a hypothesis. The Laurent sum hypotheses concern two scalar functions, whereas the source limit concerns points and all open neighborhoods. The common affine neighborhood condition is algebraic, whereas the conclusion is topological separation. The target hypotheses give a group morphism, its factorization on the whole curve, an evaluation on the interior, and the limits of an analytic function. They do not identify any algebraic cusp or compare a cusp class with an analytic value. These are the inputs for tex 1785–1787 and 2937–2943.

## Inputs still needed for the manuscript

Use `E = Ecurve ℓ`, `N = newformLevel E`, `m = d.natAbs`, `X = Over.mk (X0Branch.model N).overQ` and `T = ℂ ⧸ Lat.lattice.toAddSubgroup`.

For the exact `hAJ` of `ElkikPrint.hElkikMD_of_elkikTorsion`, take `an = ParamAtScale.torusValue Lat f.toCuspForm κ` and
`lim r = QuotientAddGroup.mk' Lat.lattice.toAddSubgroup ((c : ℂ) * ElkikMD.cuspSymbol f.toCuspForm r)`, with `c : ℚ`, `c ≠ 0`, and `(c : ℂ) = κ`. The zero and finite-cusp limits are the ones provided by `ParamJoin.algebraicParametrizationAtScale_and_cuspLimits`. The character guard is `chiD d a = jacobiSym (a : ℤ) d.natAbs`. The pre-existing ellipticity, level, newform, lattice, and genus-partner binders of the reduction stay in force; the table lists the remaining mathematical inputs.

| Input | Tex | Owner and size |
|---|---|---|
| Realize the given Weierstrass target as `A : AbVar ℚ` with an isomorphism `e : A.X ≅ Over.mk (projectiveOverQ E)` carrying the group identity to the given projective identity. Give `u : Additive (A.Pt ℂ) ≃+ T` with a continuous realization `U : Point ℂ (complexBaseChange.obj A.X) → T` and `U (complexLift p) = u (Additive.ofMul p)`. The compatibility used to identify the interior is: `projectiveValue ((p ≫ e.hom).left) = weierPt E Lat z → u (Additive.ofMul p) = QuotientAddGroup.mk' Lat.lattice.toAddSubgroup z`. | 1785–1787, 1825–1828, 2836–2838 | Missing theory, substantial: extend the projective addition law to the scheme and compare its complex realization to the analytic period quotient. |
| Transport the at-scale map to `A.X` and compare `U (complexLift (interior N τ ≫ π))` with `torusValue Lat f.toCuspForm κ τ`. This is the compatibility above with the interior evaluation already proved by the parametrization lane. The same comparison and the existing analytic zero limit imply the algebraic basedness equation by `cusp_at_infinity_maps_to_unit`. | 1785–1787, 2836–2838 | Small integration after the compatible target is available. |
| Rational scale witness `∃ c : ℚ, (c : ℂ) = κ` for the at-scale existence theorem. That theorem gives the nonzero rational witness and the analytic cusp limits at exactly that same scale. The all-cusp comparison needs neither a separate level-invariance argument on the target nor the coprimality reduction. | 1781–1787, 2937–2943 | Sibling scale-rationality and parametrization lanes. The former still needs the independent map and tail identity below. |
| `ElkikPrint.ManinDrinfeldTorsion N (algebraicCuspClass N)` for the actual geometric cusp classes. | 2937–2940, 11158–11160 | ELLIOT input, supplied by the existing printed form, subject to the lead's audit. |
| The independently specified rational maps `q_f : J₀(N) → A_f` and `α : A_f → E`, and identification of `AJ ≫ q_f ≫ α` on the fixed model with `weierPt E Lat (κ * primitive (f : ℍ → ℂ) τ)` on an eventual cusp tail (as field-valued projective points). | 1781–1787, 1825–1828 | ELLIOT input for the specified maps, plus substantial missing theory for the tail comparison (e.g. compare the differentials and the base value). |

The Albanese factorization of an already constructed `π` does not choose either `q_f` or `α` independently. In particular the at-scale construction cannot supply the independent map for the lemma on `fc04c16c8`, since it takes the rational scale witness as an input. A source endpoint limit imposes no equality on a punctured tail.

## Known issues

- The earlier audit in `RC/PrintsAnalytic/Milne.lean` records a citation scope error at tex 1784. The cited pair covers the quotient and isogeny; Proposition 11.21 handles the normalized newform. It also records that the two cited items do not state the Hecke equality at tex 1788, and two unused misprints in Conjecture 11.17. These locators are from the in-tree audit. Hecke equivariance is outside this patch.
- The wording and page locator for Elkik are **UNVERIFIED** against the primary source here. The manuscript citation at 11158–11160 and the existing printed torsion interface are carried over unchanged.
- An algebraic cusp represented by a rational fraction need not be rational over ℚ. The two specified branches at zero and infinity have rational coefficients. For the other orbits the construction uses algebraic coordinates. It does not compute the minimal residue field or depend on a formula for that field.


## Manuscript check

| Tex | Verdict |
|---|---|
| 1779–1784 | Error at 1784, inherited: the cited proposition and remark do not by themselves provide the normalized-newform statement; see Known issues. |
| 1785–1787 | Gap filled: the normalized model has the required rational base cusp, the represented Abel–Jacobi map has the factorization property, and its geometric cusp limits yield the comparison for a compatible target. The specialization of the source chart is in the complex scheme topology. |
| 1785–1787 | Unverified: the independent maps to the given elliptic curve and their identification with the analytic parametrization still need the target and comparison listed above. |
| 1825–1828 | Unverified for the independent rational-map argument: the interior formula in the at-scale lane assumes the rational scale witness. A source limit does not give the eventual identity. |
| 2836–2838 | Gap filled for a compatible target: the limit of the original chart and the analytic zero limit give the algebraic basedness equation over ℚ. |
| 2937–2939 | Gap filled: the cusp orbit assignment gives actual geometric points; the Abel–Jacobi classifier identifies their point-minus-infinity classes, and the class map factors through the orbit set. Cusp labels alone do not specify the field of definition. |
| 2940–2943, 11158–11160 | OK as invoked: the prior printed torsion statement remains the input. The weighted identity for these geometric classes follows upon specializing the compatible target and existing analytic cusp limits. |

## Validation

All 15 new Lean files passed standalone serial `lake env lean -DautoImplicit=false`, after building their imports, including the represented Picard and Albanese modules. The `#print axioms` audit on 115 declarations reports only `propext`, `Classical.choice`, and `Quot.sound`. No file of the previous run was edited. The imports exclude `ZInQKernel.OneProof.Main`.
