# Results

- Base: `2dbf8921c017f1198ca9406d868ba9d47b7fcbcf`; inherited cusp specialization, represented Abel–Jacobi map, and geometric class factorization. The base source files are unchanged.
- Fixed scale dependency: `ParamJoin.algebraicParametrizationAtScale_and_cuspLimits` takes `∃ c : ℚ, (c : ℂ) = κ`. Its output is never used to obtain that witness.
- The period-pair uniformization has a proved addition law, surjectivity, and lattice kernel for its short equation. The fixed rational Weierstrass model has a proper integral Proj model and a proved affine coordinate chart. The Jacobian package represents degree-zero Picard, but does not identify the fixed model with its own Jacobian.
- A group object on the fixed Proj needs no additional smoothness or geometric integrality hypothesis: use geometric reducedness over a perfect field, smoothness of reduced group schemes, and geometric connectedness from a rational section.
- The prior fixed-scale rationality reduction on `fc04c16c8` requires the tail equality for an independently defined rational map; the at-scale factor cannot supply it.
- Base import build passed: `J0Cusps.WeightedComparison`, `ElkikPrint.Reduction`, `ParamJoin.Cusps`, and the vendored short-equation uniformization.
- `GeometricTorsion.lean`: the actual cusp map has finite generated subgroup given the existing torsion print; the existing Elkik reduction takes the represented group and class map. Standalone check passed; two axiom audits, standard axioms only.
- `WeierstrassPeriods.lean`: `weierstrassPeriodEquiv_mk` sends the class of each `z` to `weierPt E Lat z`; coordinates away from the lattice are nonsingular. Standalone check passed; six axiom audits, standard axioms only.
- Initial proofs committed at `618d27af2`. Additional imports for geometric reducedness, connectedness and group smoothness built successfully.
- `ProjectiveAbelian.lean`: `projectiveAbVar E` packages the fixed model once a scheme group object is given. Standalone check and axiom audit passed.
- `ProjectivePoints.lean`: the existing projective evaluation is bijective over field extensions of ℚ; compatible multiplication fixes the rational identity; homogeneous vector evaluations agree on overlaps and preserve limits with nonzero limit vector. Standalone check and all axiom audits passed.
- Projective field-point and group-object proofs committed at `f382467dd`.
- `ProjectiveUniformization.lean`: the fixed complex Proj is homeomorphic to the chosen quotient; inverse on lifted field points is the inverse additive period equivalence on their projective evaluation. Includes continuity at `[0:1:0]`. Standalone check, axiom audits, and import build passed.
- `FixedScaleComparison.lean`: trivial-character descent preserves the same cusp function. With the explicit rational-scale input and compatible group realization, the actual based Jacobian factor gives the torus-valued symbol for every finite rational cusp label. Specialization to the fixed projective group law supplies the weighted comparison to Elkik. Trivial-character import build, standalone check, and axiom audits passed.
- Validation: six serial standalone checks passed; 50 audits (6 period, 2 torsion, 1 abelian variety, 22 field point, 14 projective uniformization, 5 comparison), all with only `propext`, `Classical.choice`, and `Quot.sound`. No new print or axiom.
- Remaining algebraic Prop: a group object on the fixed Proj with usual Weierstrass addition on its complex points. The independent `q_f`, `α` and fixed-scale comparison on the cusp tail were not supplied.
