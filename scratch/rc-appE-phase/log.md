# rc-appE-phase results log

## Setup
- Base 8a63a360c. `lake build` of the dependency closure (EvenPhaseForm, Bridges, PoleRC.CRM): OK (10652 jobs, cached).

## Findings
- F1 (VERIFIED, read in tree): `WaldspurgerNonvanishing` (RC/PrintsAnalytic/Waldspurger.lean:155) gives N, ψ, η, g, a_g(D₀) ≠ 0 but NOT the two-power order of ψ, η that the manuscript asserts (tex 7920-7922, 7944). `EvenPhaseData.z_root` with `z_sq` (z² = ψ(D)ψ(D₀)⁻¹) forces ψ(D/D₀) ∈ μ_{2^∞}, which fails for a twist g⊗ν by a character ν of order 3 (still in a good-Hecke eigenspace, with ψν², ην²). So EvenPhaseData cannot be built from the tree's print as stated; the two-power conclusion (manuscript's own) must be added.
- F2 (VERIFIED in tree): `evenPhaseData_of_waldspurgerNonvanishing` (RC/GlueSweep/EvenPhaseForm.lean) already fills N..ha₀ from the print given `rest` (EvenPhaseRest) for every output form.

## Compile log
- AppE/Phase.lean: compiles, no warnings (S0Filter, S0Filter.spec, S0Filter.self, isSquare_zmod_of_local [Hensel via Mathlib hensels_lemma + CRT], sqrtRatio, phase, phase_sq_eta, phase_sq, phase_root).
- AppE/Linear.lean: compiles, no warnings (period 1 of a Shimura form, analyticity at ∞, hiwCoeff linear, spaces/eigenspaces closed under +, •, Σ; proportional_of_waldspurgerCor2).
- AppE/Ramsey.lean: compiles, no warnings. PRINT `RamseyAlgebraicModel` (R-span, R-conj); PROVED exists_algebraic_normalized (algebraic g' in V with a(D₀)=1), dirichlet_mem_Qbar, heckeT3_sum, unary_eigenvalue_ne (2√p < p+1).
- AppE/Galois.lean (part 1): compiles, no warnings. GLUE hypothesis `HalfIntegralTwist` (stated, not proved: needs the theta-multiplier formula). PROVED: level raising (hiwForm_changeLevel, eigen_changeLevel), η²=ψ², ψν²=ψ^e, ην²=η^e, exists_odd_exponent (autToPow), tau_dirichlet, conj_mem_eigenspace (from R-conj), twist_mem_eigenspace (from HalfIntegralTwist).
