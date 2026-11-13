# c9-rhof fold notes (leaf-adopt3)

Fragment: `scratch/leaf-adopt3/fold/c9-rhof.lean`, section `C9RhofSec`, namespace `C9Rhof`.
Source: `scratch/c9-rhof/C9.lean` lines 27-346 and 397-632. Its §7 (lines 348-395) is deleted, and
the 7 `#print axioms` lines are dropped.

**The `sorry` question.** The single occurrence of `sorry` in C9.lean is at line 22, in the module
docstring ("no `sorry`, no `axiom`"). It is not a real `sorry`, and the docstring is not copied.
Nothing is excluded.

**Order.** The fragment needs the e1-sub fragment before it, for
`GlueI3.isSemisimpleRepresentation_baseChange`, which in turn needs glue-ssbc's `GlueSSBCSec`. The
order x1-belyi, e1-sub, c9-rhof is right.

## Glue row that becomes proved
- **C9** (leaf-modcurves §5 row C9; h-decomposition G13's open items "semisimplicity and continuity of
  `ρ_{f,ι}`" plus C9's `r₅ ≅ ρ_{f,5}`).
- From the bundle fields:
  - **`r16`** (`LeafModCurves.R16_EichlerShimuraJ1'`);
  - **`r9a`** (`PkgI3.FaltingsSemisimple`);
  - **`t26`** (`PkgI3.TateModuleFree`);
  - **`t18`** (`HSyn.FrobeniusDense`, via `frobeniusDense_of_hsyn`);
  - **T19** in module form, `GlueC10.BrauerNesbittChar0`. This is a Leaves.lean leaf def but not
    literally field `t19 : HSyn.BrauerNesbitt`, which is the matrix form. There is no bridge
    `t19 → BrauerNesbittChar0` here, but t-skolem-kw proves both outright
    (`TSkolemKW.brauerNesbittChar0`, `hsynBrauerNesbitt`). With that fragment, the hypothesis disappears.
- Plus, depending on the variant:
  - `c9_R14_hsyn` adds **`r14`** (`HSyn.EigenformRepExists`);
  - `c9_r5_hsyn` adds **`t24`** (`HSyn.EigenformTwist`) and **`t25`** (`PkgI4.NewformOfEigenform`),
    and assumes C8's outputs as hypotheses (`hr`, `hrg`, `hψ`; still open, see the task report §3).
- Pieces:
  - `rhoF_semisimple` needs only `r9a` and `t26` (and glue-ssbc);
  - `rhoF_continuous` needs only `t26`;
  - the trace identity `h₅` of `GlueC10.c10` needs only `t18` plus continuity (no T19 and no
    semisimplicity).
- `c10_via_c9` uses `GlueC10.ChebotarevExists`, a Leaves.lean leaf def and not a bundle field, plus
  `GlueC10.BrauerNesbittChar0`.

## Bridging theorems
These already have only Leaves.lean leaves as hypotheses, unchanged from the task file:
- `C9Rhof.rhoF_semisimple ℓ A θ emb (hS : PkgI3.FaltingsSemisimple) (hT : PkgI3.TateModuleFree) [FiniteDimensional …] : (LeafModCurves.rhoF ℓ A θ emb).IsSemisimpleRepresentation`
- `C9Rhof.rhoF_continuous ℓ A θ emb (hT : PkgI3.TateModuleFree) [FiniteDimensional …] b : Continuous fun σ => LinearMap.toMatrix b b (rhoF ℓ A θ emb σ)`
- `C9Rhof.c10_via_c9 (hC : GlueC10.ChebotarevExists) (hBN : GlueC10.BrauerNesbittChar0) …`
- `C9Rhof.c9`, `c9_R14`, `c9_r5`. These take the local copies `C9Rhof.FrobeniusDense`,
  `PkgI4.EigenformRepExists` and `PkgI4.EigenformTwist`. The last two are Leaves.lean defs (section
  `PkgI4`), but they are not the bundle's `HSyn` versions.

New, added at the end of the fragment (section `HSynBridges`). Hypotheses are in exact bundle-field
form:
- `C9Rhof.frobeniusDense_of_hsyn : HSyn.FrobeniusDense → C9Rhof.FrobeniusDense`
- `C9Rhof.eigenformRepExists_of_hsyn : HSyn.EigenformRepExists → PkgI4.EigenformRepExists`
  (repackages `HSyn.GaloisRep` as `PkgI4.GaloisRep ⟨ρ.toHom, ρ.continuous_toHom⟩`)
- `C9Rhof.eigenformTwist_of_hsyn : HSyn.EigenformTwist → PkgI4.EigenformTwist`
- `C9Rhof.c9_hsyn ℓ (hR16) (hS) (hT) (hBN : GlueC10.BrauerNesbittChar0) (hD : HSyn.FrobeniusDense) …`:
  same conclusion as `c9`.
- `C9Rhof.c9_R14_hsyn ℓ (hR14 : HSyn.EigenformRepExists) (hR16) (hS) (hT) (hBN) (hD : HSyn.FrobeniusDense) …`:
  same conclusion as `c9_R14`.
- `C9Rhof.c9_r5_hsyn ℓ (hTw : HSyn.EigenformTwist) (hNew : PkgI4.NewformOfEigenform) (hR16) (hS) (hT) (hBN) (hD : HSyn.FrobeniusDense) …`:
  same conclusion as `c9_r5`.

The three conversions only unfold defs: `HSyn.Qbar/GQ/LiesOver/IsArithFrob/GaloisRep/CF/coeff/
IsNormalizedEigenform` have the same bodies as `PkgI4`'s, and `HSyn.GaloisRep` has the same fields as
`PkgI4.GaloisRep`.

`#print axioms` dropped: `rhoF_semisimple`, `rhoF_continuous`, `c9`, `c9_R14`, `c9_r5`, `c10_via_c9`,
`isSemisimple_of_isIrreducible`.

## Deleted as duplicates (same full name, same text as Leaves.lean)
`PkgI4.EigenformRepExists` (L4527), `PkgI4.EigenformTwist` (L4560), `PkgI4.NewformOfEigenform`
(L4571), `PkgI4.GaloisRep.AttachedUpToTwist` (L4499).

Kept: `C9Rhof.FrobeniusDense`. It is a word-for-word copy of `HSyn.FrobeniusDense`, but it resolves
to `PkgI4.GQ/LiesOver/IsArithFrob` instead of `HSyn`'s. It is bridged by `frobeniusDense_of_hsyn`.

## Kernel declarations copied in (not in Leaves.lean)
- All of kernel `I3Linalg/RhoCont.lean` §3 (L34-405), verbatim. That is 22 declarations:
  - `PkgI3.RhoCont.{continuous_orbit, continuous_act, stalkClosedPointTo_comp_galois,
    exists_openSubgroup_galAct_eq, galAct_mul, continuous_galT, continuous_one_tmul,
    continuous_galRep, continuous_trace_galRep, continuous_toMatrix_galRep}`;
  - `PkgI3.Tate.{isOpen_coord_eq, pow_smul_shift, coord_eq_zero_iff,
    continuous_of_linearMap_padicInt, coord_eq_zero_of_le, nhds_zero_hasBasis, continuous_map_action}`;
  - **`PkgI3.continuous_galRep_of_tateModuleFree`** (used by C9);
  - the instances `PkgI3.RhoCont.instTopologicalSpacePt`, `instTopologicalSpaceV` (module topology on
    `V_ℓ(A)`, needed by `continuous_coord`'s `IsModuleTopology.continuous_of_linearMap`), plus
    anonymous `DiscreteTopology` and `IsModuleTopology` instances.
- From the e1-sub fragment: `GlueI3.isSemisimpleRepresentation_baseChange`, a wrapper of
  `GlueSSBC.isSemisimpleRepresentation_baseChange`.

## Kernel names used that Leaves.lean has with the same text
- `LeafModCurves`: `rhoF`, `eigenFun`, `frobOn`, `trace_rhoF`, `finrank_rhoF`, `embOf`, `embOf_spec`,
  `IsJ1`, `R16_EichlerShimuraJ1'`, `coeffField`, `coeff_mem_coeffField`, `IsFrobAt`,
  `isFrobAt_of_isArithFrob`.
- `GlueI3`: `repBaseChange`, `isSemisimple_of_surjective`.
- `GlueC10`: `continuous_trace`, `BrauerNesbittChar0`, `ChebotarevExists`, `c10`.
- `PkgI3`: `FaltingsSemisimple`, `TateModuleFree`, the `AbVar` layer.
- `PkgI4`: `Qbar`, `GQ`, `LiesOver`, `IsArithFrob`, `CF`, `coeff`, `IsNewform`,
  `IsNormalizedEigenform`, `GaloisRep(.mat/.IsSemisimple/.IsIrreducible/.AttachedTo/.continuous_toHom)`,
  `GaloisChar`.

## Statement differences and the one textual change
Leaves.lean's `LeafModCurves` has its own copies of `Qbar GQ LiesOver IsArithFrob CF coeff
HasNebentypus IsNormalizedEigenform scaleH oldSpace IsNewform`; the kernel opened `PkgI4`'s.

This has two consequences:
1. **Textual change.** With C9's `open PkgI4 (Qbar GQ … IsNormalizedEigenform …)` and
   `open … LeafModCurves`, every one of these names would be ambiguous. I replaced
   `open PkgI3 PkgI3.AbVar LeafModCurves` (both occurrences) by `open PkgI3 PkgI3.AbVar` plus
   `open LeafModCurves hiding <those 11>`. The names then resolve to `PkgI4`'s, exactly as in the kernel.
   - I chose `PkgI4` over `LeafModCurves` on purpose: `c9_r5`'s `rw [… hα, hcf …, hcoef …]` chain mixes
     `coeff` from c9's statement with `PkgI4.NewformOfEigenform` and `AttachedUpToTwist`. That chain
     works only if `coeff` is `PkgI4.coeff`, since `rw` does not unfold defs.
2. **Defeq crossings, no textual change.** These terms cross from `PkgI4` vocabulary to Leaves'
   `LeafModCurves` vocabulary only through application or `exact`/`rfl`, which unify by
   delta-unfolding of defs with identical bodies:
   - `hR16 N χ f J hN hf hJ`;
   - `(hfr …).1 _ rfl`;
   - `⟨coeff f p, coeff_mem_coeffField f p⟩`;
   - `isFrobAt_of_isArithFrob τ v p hp hv hτ`.

## Expected trouble spots
- `c9`'s proof: the task report notes that `whnf` on `embOf … (coeffField f)` can time out. The extra
  `PkgI4.coeff` ↔ `LeafModCurves.coeff` unifications in `c9` (the `rfl` and the subtype literal) are
  the likeliest place for a heartbeat or defeq problem. Fix:
  `show (… : ℂ) = LeafModCurves.coeff f p; rfl`, or `unfold PkgI4.coeff LeafModCurves.coeff`.
- `eigenformRepExists_of_hsyn` / `eigenformTwist_of_hsyn` / `frobeniusDense_of_hsyn`: `exact` by defeq.
  Fallback: `simpa only [HSyn.GaloisRep.IsSemisimple, PkgI4.GaloisRep.IsSemisimple, PkgI4.GaloisRep.mat, …]`.
- The RhoCont global instances (topology on `Additive (A.Pt Kbar)` and on `A.V ℓ` for `PkgI3.AbVar`)
  become visible to everything after the fragment. Leaves.lean has no other such instance, but HSyn's
  later glue now sees them.
- RhoCont's `universe u`, `local notation "Kbar"` and `omit hℓ in` are copied as is; they compiled in
  the kernel.
