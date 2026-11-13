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

## 23:40 PST
- §4-§6 compile (VERIFIED, `lake env lean scratch/c9-rhof/C9.lean`, no errors):
  - `FrobeniusDense` (T18, verbatim copy of `HSyn.FrobeniusDense`), `eq_of_eq_on_arithFrob`.
  - `trace_eq_of_arithFrob` (T18 + continuity ⇒ equal traces everywhere),
    `iso_of_arithFrob` (+ T19 `GlueC10.BrauerNesbittChar0` + semisimplicity ⇒ iso).
  - `c9_core`, `c9`: from R16', FaltingsSemisimple, TateModuleFree, T19, T18: for any continuous
    semisimple `r` over `ℚ̄_ℓ` with `f`'s arithmetic-Frobenius traces outside `S`: rhoF is
    2-dim, semisimple, continuous, `r ≅ rhoF`, `tr r = tr rhoF` everywhere (= `h₅` of
    `GlueC10.c10`), and `tr rhoF(g) = ι(a_p)` at `IsFrobAt g p`, `p ∤ Nℓ` (= `hρ₅`).
- Finding: `h₅` (the only C9 output `GlueC10.c10` consumes) needs T18 and continuity only; T19
  and semisimplicity are needed only for the isomorphism `r₅ ≅ ρ_{f,5}` itself.
- Pitfall: `generalize`/`set` on `embOf ℓ ιC ιL (coeffField f)` times out (whnf); fixed by a
  core lemma over an arbitrary `emb`.
