# g8-object results log

## Step 1 (2026-11-13 06:30-06:50 PST): the object and the G15 restatement (Dev.lean)
- Kernel modules built: `lake build` of C2, LadicCond, Different, ModCurves.Glue, RhoCont, TateBC,
  C10.Link, QM.Leaves, WP3, ModCurves.Defs, T32a (2m15s), then JHeight/Height/Constants (builds the
  upstream `lean/` helpers needed by `Hypotheses.Height`).
- `scratch/g8-object/build_dev.sh` assembles `Dev.lean` = `scratch/g15-ram/G15Ram.lean` verbatim
  (+ imports `Descent.ProjRep`, `I3Linalg.C2` after its own) + verbatim g0-mod-galois definitions
  (`part_galois.lean` L27-152: `resQ` … `G8Out`; `part_matrix.lean` L11-21: `BurnsideAbsIrred`)
  + `part_obj.lean` (new, namespace `G8Object`).
- New (part_obj.lean): `DescData A ℓ` (G7Out data + `dim = 4`), `DescData.ofG7Out` (from T26),
  `DescData.rho`, `basis`, `rW`, `m`, **`DescData.r : GaloisRep ℓ 2`** (the object), `DescData.e`,
  `intertwines`, `rho_resQ`, `g8Out` (full `G0Galois.G8Out` from C2's leaves + Burnside);
  `mat_eq_scalar_of_intertwines`, `toHom_eq_one_of_intertwines`, `g11_of_intertwines`;
  `TmWild`, `BetaUpper`, `BetaTame`, `SmallPrimeG`, `LargePrimeG`, `LocalDataG` (on `(Tm, a, β)`);
  `twistShape_of_tmWild`, `localData_of_intertwines`; `ModObj`, `ModObj.toModData`,
  `g15RamG_obj`, `g15RamG_of_intertwines`.
- Compile (VERIFIED): `lake env lean scratch/g8-object/Dev.lean` exit 0, 0 errors, no sorry,
  45 s; `#print axioms` = [propext, Classical.choice, Quot.sound] for `DescData.intertwines`,
  `DescData.g8Out`, `mat_eq_scalar_of_intertwines`, `g11_of_intertwines`,
  `localData_of_intertwines`, `g15RamG_obj`, `g15RamG_of_intertwines` (plus g15-ram's 13).

## Step 2 (06:40-07:00 PST): one environment with g0-mod-field, g14-trace, g15-ram, g0-assemble's Props
- `lake build ZInQKernel.Main` (6m50s; builds the upstream helper `ZInQ.PoleValuation` that
  `G14Trace.lean`'s import `ZInQKernel.Main` needs).
- `scratch/g8-object/build.sh` assembles `G8Object.lean` (6 300 lines): imports (union; G14Trace's
  first: with ModField's first, the E1 copy's `bcPt.map_one'` fails with "No goals", as g15-ram
  noted) + `ModField.lean` L16-1036 in a section + `part_bridge.lean` (TateBridge35) in a section
  re-issuing ModField's file-level opens + `G14Trace.lean` L10-end + G15Ram's G0Galois block and
  §1-§3 + g0-mod-galois definitions + `part_obj.lean` + `87_afterg7.lean` L27-123 (ModelG3G6,
  LocalRamWild, G15RamWild, g15RamG_of_wild, LinkedTateData; ModField's opens re-issued) +
  `part_link.lean` (new).
- New (part_link.lean): `LinkedObj` (descent data at 5 and 3 with the scalar link and
  FrobTraceLink), `galG8Out5/3`, **`interface_obj`** (∃ M : ModObj, M.D5 = Lk.D5 ∧ M.D3 = Lk.D3 ∧
  G12Spec ∧ G14TraceCompat ∧ G15RamG on `M.toModData`), **`modularConstituent_tail_obj`**
  (G13-G16 with the tail's ∃D-hypothesis discharged on the object), `BetaUpperC`, `BetaTameC`,
  `LocalDataC` (β-clauses on G7Data's ℂˣ-valued β), `localDataG_of_C`, `RhoRamWild` (text of
  linked-tate's), **`rhoRamWild_of_localDataG`**, `localRamWild_of_rhoRamWild`,
  **`LinkedTateObj`** (restated GluePieces2 field 28), **`linkedTateData_of_obj`**
  (T7 → LinkedTateObj → g0-assemble's LinkedTateData, verbatim copy).
- Compile (VERIFIED): `lake env lean scratch/g8-object/G8Object.lean` exit 0, 0 errors, no
  sorry, 1m29s; all 45 `#print axioms` reports = [propext, Classical.choice, Quot.sound]
  (`scratch/g8-object/obj.out`).

## Step 3 (07:00-07:05 PST): comparison with linked-tate and g14-trace; non-vacuity
- `part_ltcopy.lean`: verbatim copy of linked-tate's `RhoRamWild`, `LinkedTateCore`,
  `LinkedTateCoreDR` from its commit dae5b706 (`git show`; saved as `lt_95_dae5b706.lean`),
  L218-228, L266-309, L327-361, namespace `HSyn.LinkedTate`, ModField's opens re-issued. My own
  `RhoRamWild` copy removed; part_link uses `HSyn.LinkedTate.RhoRamWild`.
- New: `linkedTateCore_of_obj : LinkedTateObj → HSyn.LinkedTate.LinkedTateCore`,
  `LinkedTateObjDR` (with `dim = 2`, `rank End = 4` hypotheses),
  `linkedTateCoreDR_of_objDR : LinkedTateObjDR → LinkedTateCoreDR`,
  `tateBridge35_of_objDR` (on a fibre context, `LinkedTateObjDR`'s data witness g14-trace's
  `TateBridge35` conclusion over `GaloisCopy.G7Out`, `G14Bridge.FrobTraceLink`; the verbatim
  copies are accepted by unfolding), `ramCard_bot_zero`, `localDataG_triv` (non-vacuity).
- Compile (VERIFIED): `G8Object.lean` exit 0, 0 errors, 0 sorry, 2m03s; 49 axiom reports, all
  [propext, Classical.choice, Quot.sound].

## Step 4 (07:05-07:13 PST): TmWild split (part_split.lean)
- New: `ContainsL p L F` (F ⊇ j(L) for an embedding j intertwining `decomp`),
  `decomp_mem_fixing` (proved: decomp(G_F) ⊆ Fix(L)), `OnL L A Tm a ψ` (G_L-clause on G7's
  operators: through `resQ L`, `a = 1` and `Tm = ψ⁻¹ ∘ tate_A ∘ ψ`), `WildTateTrivial p L A ℓ F`
  (wild inertia of G_F acts trivially on V_ℓ(A/L)), `tmWild_of_split` (proved, uses g0-mod-field's
  `resQ_range`), `LocalDataS` (G15's local data on G7Data's L, A, β only),
  `localDataC_of_S`, `LinkedTateObjS` (split form of the restated field),
  `linkedTateObj_of_S`, `linkedTateData_of_S`.
- Compile (VERIFIED): first run: one `rw [AlgEquiv.smul_def]` failed (goal already unfolded);
  fixed. `G8Object.lean` (6723 lines) exit 0, 0 errors, 0 sorry, 1m53s; 54 axiom reports, all
  [propext, Classical.choice, Quot.sound].

## Step 5 (07:20 PST): text checks
- python string comparison (VERIFIED): the `RhoRamWild`, `LinkedTateCore`, `LinkedTateCoreDR`
  blocks of `part_ltcopy.lean` equal those of linked-tate's current working
  `scratch/linked-tate/parts/95_linked.lean` (07:20) and of its commit dae5b706.
- All other copies in `G8Object.lean` are produced by `sed` line ranges from the source files in
  `build.sh` (verbatim by construction).
