# htmult-model results log

Base: fork main 06660f4a + `git merge origin/wip/pb-dimform` (3d69c488), merge commit c06acc95. Nothing else merged.

## Statements (scratch/htmult-model/HTModel.lean, copied to ZInQKernel/Contrib/OneProof/HTModel.lean)

- `HTModel.tensorInvEquiv`: `(A ⊗ L^n)^H ≃ₗ[ℚ_p] Fin d → (A ⊗ E^n)^H`, for an E-basis `b : Basis (Fin d) E L`, `ρ_L = ρ_E ⊗_E L`.
- `HTModel.finrank_tensorInv`: `dim_{ℚ_p}` multiplied by `d`.
- `HTModel.htMultU_eq_of_basis`, `HTModel.htMultE_eq_of_basis`: same multiplicities on E and L.
- `HTModel.htMultE_eq_of_le` (E ≤ L inside ℚ̄_p), `HTModel.htMultE_model_eq` (two models, via E ⊔ E').
- `HTModel.localDistinctHTP_iff_of_model`, `HTModel.localDistinctHTP_iff_forall`, `HTModel.localDistinctHTU_iff_of_model`.

## Compile outcomes
