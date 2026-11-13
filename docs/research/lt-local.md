# lt-local: g0-assemble2's GLUE field 39 `LinkedTateLocal` from `TateBridge35`'s data

Task lt-local, 2026-11-13. Lean: `scratch/lt-local/` (results log `scratch/lt-local/log.md`).

Markers: **VERIFIED** = compiled or read here. **STANDARD** = published, with a reference.
**SPECULATIVE** = my judgement. Theorem numbers from memory are **UNVERIFIED** (no network).

## 1. Result

**`LinkedTateLocal` is proved, with its statement unchanged, once `G7Data` carries G4's bound
`[L:ℚ] ≤ D`.** g0-assemble3 has already made that fix for `GluePieces4`. Over g0-assemble2's
`G7Data`, which lacks the bound, this route proves the corrected statement `LinkedTateLocalD`:
`LinkedTateLocal` with the premise `Module.finrank ℚ L ≤ ZInQ.heightD` added. All results below are
VERIFIED (compiled, standard axioms only).

```lean
-- over g0-assemble3's G7Data (variant file LtLocal4.lean): the GLUE field itself
theorem LTLocal.linkedTateLocal_of_tateBridge35 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5)
    (hU3 : G15Ram.UnramRoots 2 3) (hB : G14Bridge.TateBridge35)
    (hFS : HSyn.G0Split.FibreSimple) (hR : HSyn.LinkedTate.QMEndRank) :
    HSyn.G0AssembleMod.LinkedTateLocal
theorem LTLocal.linkedTateLocal_of_algFrobRed (hR6) (hTors) (hU5) (hU3)
    (hT : PkgI3.TateModuleFree) (hA : FrobTrace.AlgFrobRed) (hFS) (hR) :
    HSyn.G0AssembleMod.LinkedTateLocal

-- over g0-assemble2's G7Data (LtLocal.lean): the corrected statement
theorem LTLocal.linkedTateLocalD_of_tateBridge35' (hR6) (hTors) (hU5) (hU3)
    (hB : G14Bridge.TateBridge35) (hFS : HSyn.G0Split.FibreSimple)
    (hR : HSyn.LinkedTate.QMEndRank) : LTLocal.LinkedTateLocalD
```

So field 39 rests on the following inputs:
- the leaves R6 and I2-Tors, already in the bundles as `r.r6` and `t.t5`;
- local-glue's textbook Prop `UnramRoots` at `p = 2`, for `ℓ = 5` and `ℓ = 3`;
- g14-trace's glue `TateBridge35`. frob-trace reduced it to the leaf I3.M0 and the glue `AlgFrobRed`,
  and the parallel task g8-tate works on it;
- `FibreSimple` (derived from `GluePieces4` by g0-assemble3's `fibreSimple_of_gp4`) and
  `QMEndRank` (`GluePieces4` field 43).

`KerWild` and `DescentPts` are discharged by lg-kerwild. TateBridge35's two hypotheses (`dim`,
`rank`), the G7 clauses `G7Clauses` for the transported data, and the passage from local-glue's
`LocalGlue` to g15-ram's `LocalData` for every `r₅`, `r₃` with G8's output are proved here, or
were proved by local-data.

## 2. The inputs

| input | kind | where | status |
|---|---|---|---|
| `ObjBridge.RaynaudCriterion` (R6) | LEAF | `ResearchLeaves4.r6` (as `PkgI2.RaynaudCriterion`) | bundle |
| `ObjBridge.TorsionStructure` (I2-Tors) | LEAF | `TextbookLeaves.t5` (`Iff.rfl` with `PkgI2.TorsionStructure`) | bundle |
| `G15Ram.UnramRoots 2 5`, `UnramRoots 2 3` (local-glue) | textbook statement (Serre, *Local Fields* III §5, IV §2, locators UNVERIFIED), over genuine definitions | not in a bundle yet | open |
| `G14Bridge.TateBridge35` (g14-trace) | GLUE | g8-tate works on it; frob-trace: I3.M0 + `AlgFrobRed` ⟹ it | open |
| `HSyn.G0Split.FibreSimple` (g0-split) | GLUE | `GluePieces` piece; g0-assemble3's `fibreSimple_of_gp4` derives it from `GluePieces4` (FS1-FS5) | supplied |
| `HSyn.LinkedTate.QMEndRank` (linked-tate) | GLUE, literature-backed (Mumford §19 Thm 3; Albert's classification, Mumford §21; numbering UNVERIFIED) | `GluePieces4` field 43 | in `GluePieces4` |

Named Props defined here (namespace `LTLocal`, each with a docstring naming its step and source):

| Prop | kind | status |
|---|---|---|
| `LinkedTateLocalD` | GLUE (corrected field 39) | **proved** from the inputs above |
| `ModelEndRank4` | GLUE (G5-G6: `rank_ℤ End(A_{L'}) = 4` on G7's model; TateBridge35's second hypothesis) | **proved** from `FibreSimple` + `QMEndRank` (`modelEndRank4_of_qmEndRank`). It is also a consequence of `LinkedTateLocal` (`modelEndRank4_of_localD`), so it costs no truth |
| `G7DegreeBound` | GLUE (`[L:ℚ] ≤ D` for every G7 datum) | **proved** over g0-assemble3's `G7Data`, where it is a projection (`g7DegreeBound_gp4`). Over g0-assemble2's `G7Data` it is expected to be false (§4 F1, SPECULATIVE) |

## 3. What is proved

All rows are VERIFIED (compiled; `#print axioms` = `[propext, Classical.choice, Quot.sound]`).

| Lean (`LTLocal.`) | statement | proof |
|---|---|---|
| `qbar_card_le`, `exists_equiv_extending_aux`, **`exists_equiv_extending`** | for `ιC : ℚ̄ →ₐ[ℚ] ℂ` and `j : ℚ̄ →ₐ[ℚ] ℚ̄_ℓ` there is `Φ : ℂ ≃+* ℚ̄_ℓ` with `Φ ∘ ιC = j` | transcendence bases over `ℚ̄` (both of cardinality `𝔠`), `MvPolynomial.renameEquiv`, `IsAlgClosure.equivOfEquiv_algebraMap` |
| **`g7Clauses_of_transport`** | `G7Data`, `[L:ℚ] ≤ D`, `ιC ∘ βQ = β` and `∂(j ∘ βQ) = ε'` give local-data's `G7Clauses (j ∘ βQ) ε' L` | with `Φ` as above, `j ∘ βQ = Φ ∘ β`. The clauses for `Φ ∘ β` follow g8-tate's `g7Clauses_of_g7Data`. `ε' = 1` on `G_L × G_L` because `ε = 1` there (`DescentDatum`) and `j ∘ βQ` has no zero |
| **`dim_bc_of_g7Data`** | `G7Data` ⟹ `dim A_{L'} = 2` | `IsModelOver`, `P.surface`, g0-dim's `pkgI3_dim_baseChange` |
| `localGlue_at` | lg-kerwild's `localGlue_of_transport`, with `UnramRoots` needed only at `p = 2` | its proof, via local-glue's `localGlue_of_descent` |
| **`linkedTateLocalD_of_tateBridge35`** | R6, I2-Tors, `UnramRoots 2 5`, `UnramRoots 2 3`, `TateBridge35`, `ModelEndRank4` ⟹ `LinkedTateLocalD` | `TateBridge35`'s data; `G7Clauses` at 5 and 3; `LocalGlue` at `p ≠ ℓ`; local-data's `localData_of_g7` for every `r_ℓ` with `G8Out` |
| `endDivision_of_fibreSimple` | `FibreSimple` gives `EndDivision` of every number-field model of the fibre | linked-tate's proof, copied |
| **`modelEndRank4_of_qmEndRank`**, `linkedTateLocalD_of_tateBridge35'` | `FibreSimple` + `QMEndRank` ⟹ `ModelEndRank4`, and the main theorem with it | the argument of linked-tate's `linkedTateCore_of` |
| `linkedTateLocal_of_D`, `linkedTateLocalD_of_local`, `modelEndRank4_of_localD` | `LinkedTateLocalD` + `G7DegreeBound` ⟹ `LinkedTateLocal`; the converse direction; `ModelEndRank4` from the Props | trivial |
| (variant) `g7DegreeBound_gp4`, **`linkedTateLocal_of_tateBridge35`**, **`linkedTateLocal_of_algFrobRed`** | over g0-assemble3's `G7Data`: `G7DegreeBound`; `LinkedTateLocal` itself; the same with I3.M0 + `AlgFrobRed` in place of `TateBridge35` | the last clause of `G7Data`; `linkedTateLocal_of_D`; frob-trace's `tateBridge35_of_algFrobRed` |

## 4. Findings

- **F1 (VERIFIED, read and compiled; truth SPECULATIVE). Over g0-assemble2's `G7Data`, this route
  cannot reach `LinkedTateLocal`. It needs `[L:ℚ] ≤ D`.**
  - Where the bound is used: local-data's `G7Clauses` carries `finrank ℚ L ≤ D`, and
    `localData_of_g7` uses it twice. At `p ≤ D` it bounds `[E:ℚ_p] ≤ D·G₀`. At `p > D` it makes the
    closure of `L_v` tame, since `[L_v:ℚ_p] ≤ D < p`.
  - g0-assemble2's `G7Data` drops G4's bound (local-data F3; also g8-object §4.1 and linked-tate §5).
  - `G7DegreeBound` is expected to be false (SPECULATIVE). `G7Data`'s only degree clause is
    `[L':ℚ] ≤ Q_D · M(u)` with `Q_D = D^{D·E₀}` (`ZInQ.heightQ`), which is vastly larger than `D`.
    Enlarging `L` and `L'` by a 2-power cyclotomic field (`2 ∈ T(u)`) seems to keep every clause.
    This is not checked in Lean: it needs a new descent datum for `A_{LM}`.
  - Whether `LinkedTateLocal` itself is false for such oversized `L` is not settled here.
  - The fix is g0-assemble3's: `G7Data` now ends with `Module.finrank ℚ L ≤ heightD`. Over that
    `G7Data`, `LinkedTateLocal` is proved with its statement unchanged (variant file).
- **F2 (VERIFIED, compiled). TateBridge35's hypotheses cost nothing new.**
  - `dim A_{L'} = 2` is proved from `G7Data`.
  - `rank End(A_{L'}) = 4` follows from `FibreSimple` and `QMEndRank`, both already supplied by
    `GluePieces4`.
  - Neither is extra truth: `G7Out`, which `LinkedTateLocal` asserts, contains both.
- **F3 (VERIFIED, compiled). The transport clause of `G7Clauses` needs an isomorphism `ℂ ≅ ℚ̄_ℓ`
  over `ℚ̄`, not just any one.** `β_ℓ = j ∘ βQ` must satisfy `β_ℓ² = ι ∘ χ` for some
  `ι : ℂ^× → ℚ̄_ℓ^×`. g8-tate's `exists_complex_equiv` gives some `Φ`. Here `Φ ∘ ιC = j` is needed,
  and `exists_equiv_extending` proves it from Mathlib (transcendence bases over `ℚ̄`).
- **F4 (VERIFIED, read). Comparison with the routes g0-assemble3 chose or left out.**
  - g0-assemble3 replaced field 39 by linked-tate's route: data constructed in Lean, plus the glue
    `LinkedFrob`, `KernelFieldBreaks`, `TateRamAtThree`, `GoodRedTorsion`, `QMEndRank`.
  - The route here takes the data and the Frobenius link from `TateBridge35`, which is larger than
    `LinkedFrob`. Its ramification half is smaller: R6, I2-Tors and `UnramRoots` (leaves and one
    textbook statement), with no `KernelFieldBreaks` and no `TateRamAtThree`.
  - g8-tate's `TateBridgeOnL` route needs `OnL` in addition to `TateBridge35`. This route does not:
    lg-kerwild's `KerWild`/`DescentPts` replace it.
  - Recommendation: prove linked-tate's `LinkedRam` from local-glue on linked-tate's constructed
    data. lg-kerwild already proved `KerWild` for unram-tate's construction (`tateBridgeK_of_piecesK`).
    That would combine the smaller halves of both routes. Not attempted here.

## 5. Integration (for `GluePieces4` or later)

- In g0-assemble3's environment, field 39 `linkedTateLocal` can be filled by
  `LTLocal.linkedTateLocal_of_tateBridge35 r.r6 t.t5 hU5 hU3 hB (fibreSimple_of_gp4 r t gp) gp.qmEndRank`,
  where `r.r6` and `t.t5` go through the `Iff.rfl` bridges `ObjBridge.* ↔ PkgI2.*`. This needs two new
  inputs, `UnramRoots 2 5` and `UnramRoots 2 3` (`G15Ram`, local-glue). It also needs `TateBridge35`,
  or I3.M0 + `AlgFrobRed`.
- Files to fold in: lg-kerwild's `KerWild.lean` body and `part_tools`, `part_g7`, `part_main`,
  `part_rank`, `part_gp4` from `scratch/lt-local/`.
  - Drop the verbatim copies: `part_copy.lean` and the copy blocks at the head of `part_rank.lean`
    (`ZInQ.DefFaltings.AbVar`, `LeafAdopt.abVarEquiv`, `HSyn.G0Split.FibreOver`, `FibreSimple`,
    `HSyn.LinkedTate.QMEndRank`).
  - Keep `g8-tate`-copied lemmas only once (`padic_card_le`, `padicAlgCl_card`, `T_prime`, here in
    namespace `LTLocal`).
- `dim_bc_of_g7Data` and `modelEndRank4_of_qmEndRank` read `G7Data`'s model clause with
  `first | .2^11 | .2^11.1`, so the same text compiles over both versions of `G7Data` (VERIFIED: both
  files compile).
- Name resolution of `Qbar`, `GQ` in the copied `LinkedTateLocal`: G0Assemble2 resolves them in its
  own context. Here they resolve through the section-level opens of its `section G0A2_a85_linked`
  (`open GlueDescent GlueC10 PkgI3`). Every candidate is a reducible abbrev of
  `AlgebraicClosure ℚ`, resp. `Qbar ≃ₐ[ℚ] Qbar`.

## 6. Compile record

- `scratch/lt-local/build.sh` assembles `LtLocal.lean` (9 576 lines): the imports, then
  `scratch/lg-kerwild/KerWild.lean` verbatim minus `#print axioms`, then parts 1-5 and their axiom
  lines. `lake env lean scratch/lt-local/LtLocal.lean`: exit 0, 64 s, no error, no `sorry`; 11
  axiom reports, all `[propext, Classical.choice, Quot.sound]` (`compile.out`).
- `scratch/lt-local/build4.sh` assembles `LtLocal4.lean` (9 626 lines): the same with
  g0-assemble3's `G7Data` fix ported by `mk_base4.py`, plus part 6. The fix is
  `scratch/g0-assemble3/parts/75_modfield.lean`: the clause and its three proof adjustments,
  exact-substring replacements, each found once. No other copied proof needed a change.
  `lake env lean scratch/lt-local/LtLocal4.lean`: exit 0, 64 s, no error, no `sorry`; 14 axiom
  reports, all standard (`compile4.out`).
- Before the first compile: `lake build` of the 25 `ZInQKernel` modules that `KerWild.lean`
  imports: success.
- Verbatim copies, VERIFIED by construction (`sed` line ranges, recorded in each part's header;
  part 3's blocks also checked by a substring test):
  - `G0Assemble2.lean` l.41358-41360, 62238-62242, 62356-62373, 63903-63947;
  - `LinkedTate.lean` l.17119, 18210-18236, 19042-19045, 19196-19201, 33338-33340, 33577-33590,
    33712-33722, 42841-42844, 43121-43135.
- Development files `T1.lean`-`T4.lean` import `olean/Base` (`ctail.sh`). They are not
  deliverables.
