# c9-rhof results log

Markers: VERIFIED (compiled / read), STANDARD, SPECULATIVE, UNVERIFIED.

## 2026-11-12 22:58 PST
- Built kernel modules `ZInQKernel.HDecomp.ModCurves.Glue`, `I3Linalg.C2`, `I3Linalg.RhoCont`
  (lake build, exit 0, 1m30s).
- `scratch/c9-rhof/C9.lean` §1-§3 compile (VERIFIED, `lake env lean`, warnings only):
  - `C9Rhof.ev`, `quotMap : ℚ̄_ℓ ⊗ V_ℓ(A) →ₗ (eigenFun)^∨`, `quotMap_equivariant` (base change of
    `ρ_ℓ` to `rhoF`), `quotMap_surjective` (eigenFun finite-dimensional).
  - `rhoF_semisimple (hS : FaltingsSemisimple) (hT : TateModuleFree)`: from Faltings Satz 3,
    kernel's proved `GlueI3.isSemisimpleRepresentation_baseChange`, `isSemisimple_of_surjective`.
  - `rhoF_continuous (hT : TateModuleFree) b`: matrix coefficients continuous in any basis.

## 23:08 PST
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

## 23:12 PST
- §7-§9 compile (VERIFIED; `lake env lean scratch/c9-rhof/C9.lean`, exit 0, no warnings; output in
  `scratch/c9-rhof/compile.out`):
  - verbatim copies (checked by substring match against `scratch/h-decomposition/Leaves.lean`):
    `PkgI4.EigenformRepExists` (R14), `EigenformTwist` (T24), `NewformOfEigenform` (T25),
    `GaloisRep.AttachedUpToTwist`; `C9Rhof.FrobeniusDense` (T18).
  - `toRep` (GaloisRep → Representation), `toRep_continuous`, `trace_toRep`,
    `semisimple_of_complements`, `toRep_semisimple` (`GaloisRep.IsSemisimple` ⇒ semisimple module).
  - `c9_R14`: R14's `ρ` for `f` ≅ `rhoF`, equal traces on all of `G_ℚ`.
  - `c9_r5`: C8's `r` (semisimple, `AttachedUpToTwist ψ … g S`, `ψ` = Dirichlet `ψD` at Frobenius)
    ⇒ newform `f`, level `N ∣ M m²`, and for every `J₁(N)`: `r ≅ rhoF`, `h₅`, `hρ₅`.
  - `c10_via_c9`: `GlueC10.c10` instantiated with `ρ₅ := rhoF` and C9's `h₅`, `hρ₅`.
- `#print axioms` for rhoF_semisimple, rhoF_continuous, c9, c9_R14, c9_r5, c10_via_c9:
  [propext, Classical.choice, Quot.sound] (VERIFIED).

## 23:25 PST
- `isSemisimple_of_isIrreducible` (Burnside-irreducible GaloisRep ⇒ IsSemisimple) compiles.
- Model review (one agent, read-only): no faithfulness defects. Its point on `c9`'s `hatt`
  (missing `p ∤ Nℓ` guard) is applied, recompiled exit 0, standard axioms (VERIFIED).
  Its claim that global Kronecker–Weber is not a leaf is wrong: `KroneckerWeber` at Leaves.lean
  L18903, bundle field `t17` (VERIFIED).
