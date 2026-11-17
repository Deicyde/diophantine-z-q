# htmult-model results log

Base: fork main 06660f4a + `git merge origin/wip/pb-dimform` (3d69c488), merge commit c06acc95. Nothing else merged.

## Statements (scratch/htmult-model/HTModel.lean, copied to ZInQKernel/Contrib/OneProof/HTModel.lean)

- `HTModel.tensorInvEquiv`: `(A ⊗ L^n)^H ≃ₗ[ℚ_p] Fin d → (A ⊗ E^n)^H`, for an E-basis `b : Basis (Fin d) E L`, `ρ_L = ρ_E ⊗_E L`.
- `HTModel.finrank_tensorInv`: `dim_{ℚ_p}` multiplied by `d`.
- `HTModel.htMultU_eq_of_basis`, `HTModel.htMultE_eq_of_basis`: same multiplicities on E and L.
- `HTModel.htMultE_eq_of_le` (E ≤ L inside ℚ̄_p), `HTModel.htMultE_model_eq` (two models, via E ⊔ E').
- `HTModel.localDistinctHTP_iff_of_model`, `HTModel.localDistinctHTP_iff_forall`, `HTModel.localDistinctHTU_iff_of_model`.

## Compile outcomes
- `lake build ZInQKernel.Contrib.OneProof.PstModel`: success (scratch/htmult-model/build0.txt). VERIFIED.
- compile1–3 (scratch/htmult-model/compile{1,2,3}.txt): errors fixed (`zero` alternative not accepted by `TensorProduct.inductionOn`; `include b in` must precede the docstring; local `Module.Free E L` needed for `Module.finBasis`).
- compile4: `lake env lean scratch/htmult-model/HTModelAx.lean` EXIT 0, no sorry, one linter warning (`letI` kept as in PstModel.lean). All 11 new declarations: `[propext, Classical.choice, Quot.sound]`. VERIFIED.
- compile5: `lake env lean ZInQKernel/Contrib/OneProof/HTModel.lean` EXIT 0, 0 errors. VERIFIED.
- `htMultU_eq_of_basis` needs no `FiniteDimensional` hypothesis (omitted); the rest need `[FiniteDimensional ℚ_[p] E]` only through pb-fix3's `htMultE_eq_htMultU`.

## Findings
- No Ax–Sen–Tate finiteness used: every identity holds for `finrank` (zero on infinite-dimensional spaces).
- Manuscript L721–723 ("extend scalars ... to a finite extension containing its image") picks an arbitrary finite coefficient field; model independence (now proved) makes "the two Hodge–Tate weights are 0,−1" (L739) independent of the choice. No error found.
