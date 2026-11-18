# rc-appE-phase results log

## Setup
- Base 8a63a360c. `lake build` of the dependency closure (EvenPhaseForm, Bridges, PoleRC.CRM): OK (10652 jobs, cached).

## Findings
- F1 (VERIFIED, read in tree): `WaldspurgerNonvanishing` (RC/PrintsAnalytic/Waldspurger.lean:155) gives N, ψ, η, g, a_g(D₀) ≠ 0 but NOT the two-power order of ψ, η that the manuscript asserts (tex 7920-7922, 7944). `EvenPhaseData.z_root` with `z_sq` (z² = ψ(D)ψ(D₀)⁻¹) forces ψ(D/D₀) ∈ μ_{2^∞}, which fails for a twist g⊗ν by a character ν of order 3 (still in a good-Hecke eigenspace, with ψν², ην²). So EvenPhaseData cannot be built from the tree's print as stated; the two-power conclusion (manuscript's own) must be added.
- F2 (VERIFIED in tree): `evenPhaseData_of_waldspurgerNonvanishing` (RC/GlueSweep/EvenPhaseForm.lean) already fills N..ha₀ from the print given `rest` (EvenPhaseRest) for every output form.
