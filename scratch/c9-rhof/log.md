# c9-rhof results log

Markers: VERIFIED (compiled / read), STANDARD, SPECULATIVE, UNVERIFIED.

## 2026-11-12 23:00 PST
- Built kernel modules `ZInQKernel.HDecomp.ModCurves.Glue`, `I3Linalg.C2`, `I3Linalg.RhoCont`
  (lake build, exit 0, 1m30s).
- `scratch/c9-rhof/C9.lean` §1-§3 compile (VERIFIED, `lake env lean`, warnings only):
  - `C9Rhof.ev`, `quotMap : ℚ̄_ℓ ⊗ V_ℓ(A) →ₗ (eigenFun)^∨`, `quotMap_equivariant` (base change of
    `ρ_ℓ` to `rhoF`), `quotMap_surjective` (eigenFun finite-dimensional).
  - `rhoF_semisimple (hS : FaltingsSemisimple) (hT : TateModuleFree)`: from Faltings Satz 3,
    kernel's proved `GlueI3.isSemisimpleRepresentation_baseChange`, `isSemisimple_of_surjective`.
  - `rhoF_continuous (hT : TateModuleFree) b`: matrix coefficients continuous in any basis.
