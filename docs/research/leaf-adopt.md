# leaf-adopt: the latest leaf reports folded into the H decomposition

Status: research note (task leaf-adopt, 2026-11-12). Edited files: `scratch/h-decomposition/Leaves.lean`,
`docs/research/h-decomposition.md`; results log `scratch/leaf-adopt/log.md`; the one-shot
insertion script `scratch/leaf-adopt/fold.py`. No file under `ZInQKernel/`, `blueprint/` or
another task's directory was edited.

Marks: **VERIFIED** = compiled, computed or read here; **STANDARD** = published, with a
reference; **SPECULATIVE** = an assessment. Theorem numbers not read by the locator audit are
UNVERIFIED (no network).

## 0. Main result

**`Leaves.lean` now states 48 of the 56 leaves of the H decomposition concretely, plus three of the
four parts of a 49th (R1). Only 7 leaves and R1(b) remain `opaque` placeholders** (before: 40 of
54, 14 placeholders). VERIFIED: `lake env lean scratch/h-decomposition/Leaves.lean` exits 0
(3m13s, 19.2k lines). There is one `sorry`, the same as before (`HSyn.glueOutputs_of_leaves`),
8 `opaque` and no `axiom`. All 118 `#print axioms` give `propext`, `Classical.choice`, `Quot.sound`,
except `HSyn.sixContactMin_of_leaves`, which adds `sorryAx` through that `sorry`.

| Leaf | Before | Now (Lean name) | Source report |
| --- | --- | --- | --- |
| R1 (a), (c), (d) + `π₀(X₆)=1` | placeholder | `LeafAdopt.R1R2fpRep` (with `LeafQM.AV.R1rec`) | leaf-qm-fp, repaired (Q4, Q5) |
| R1 (b) | inside R1's placeholder | placeholder `R01b_ComplexUniformization`, family form (Q3) | rv-blueprints |
| R2 | placeholder | inside `R1R2fpRep`: `R2X6PropsIff`, `X6Surj` | leaf-qm-fp, repaired (Q5) |
| R5 | placeholder | `LeafQM.AV.R5fp` (= `R5fpStrong`), `R5fpCount`, `R5ptProps` | leaf-qm-fp (Q2 holds already) |
| R16 | placeholder | `LeafModCurves.R16_EichlerShimuraJ1'` (every `K_N` model, no MC9) | leaf-modcurves (M1) |
| R19, R20, R21 | placeholders | `ZInQ.DefFaltings.R19_GaudronRemond`, `R20_FaltingsLemma5`, `R21_Bost` | def-faltings |
| H5 (new, research) | — | `LeafAdopt.H5` = `StableHeightFinite ∧ NeronModelMinimal` | def-faltings, rv-blueprints F2 |
| T33 (new, textbook) | — | `LeafModCurves.JacobianExists ℚ` | leaf-modcurves |
| T34 (new, textbook) | — | `LeafModCurves.DimJ1Genus` | leaf-modcurves |
| T32 (a), (b) | concrete textbook leaf | **glue, proved**: `HSyn.t32a_glue`, `HSyn.t32b_glue` | glue-t32a, glue-b3b |

Counts (VERIFIED by counting the fields of the bundles). There are 23 research-level leaves
(R1-R22 and H5) and 33 textbook leaves (T1-T31, T33, T34), 56 in all.
- Concrete: 18 research-level leaves (R2, R4-R16, R19-R21, H5) and 30 textbook leaves (T1-T9,
  T13-T31, T33, T34), 48 in all, plus R1 in part.
- Placeholders: R3, R17, R18, R22, T10, T11, T12, and R1(b).
- Fields: `ResearchLeaves` has 26 (21 concrete), `TextbookLeaves` has 37 (34 concrete). That is
  55 concrete Props and 8 placeholders.

**Two caveats must accompany every claim about these counts** (they are in the docstrings and in
h-decomposition §0, §2.1, §6 R7):
1. **SPECULATIVE premise of the Shimura-curve leaves (R1, R2, R5).** They are stated over QM
   pairs without polarization, as leaf-qm-fp built them. So each is the published statement or a
   consequence of it only together with bp-qmmoduli §2.2: a QM pair `(A, ι)` in characteristic 0
   has a unique principal polarization with Rosati involution `x ↦ μ⁻¹x̄μ`.
   - §2.2's uniqueness half and its lattice core were checked by model reviews, and its sign
     claim numerically (rv-blueprints).
   - Its existence half is unformalized, and no human has reviewed it.
   - Polarizations cannot be stated in Lean today, so §2.2 cannot be split off as a hypothesis.
2. **The height leaves (R19, R20, R21, H5) are not yet known to be non-vacuous.** The three Props
   of def-faltings `AnalyticUniformizationExists`, `AnalyticUniformizationUnique` (node AN3) and
   `HodgeLatticeTheorem` are open.
   - Until they are proved, the infimum defining `stableFaltingsHeight` may run over an empty
     index set, so `h = ⊤`.
   - Then R21 holds trivially and R19, R20 have no instance.
   - H5's `StableHeightFinite` asserts finiteness, so H5 is "published theorem + correctness of
     the definition".

## 1. How the files were folded (VERIFIED)

The four report files import kernel modules: `ZInQKernel.HDecomp.A6.A6`, `.Objects` and
`.C10.C10`. Their namespaces `PkgI2`, `PkgI3`, `ObjBridge` and `GlueC10` are also defined in
`Leaves.lean`, so `Leaves.lean` cannot import them. `scratch/leaf-adopt/fold.py` therefore copied
their bodies verbatim as four sections, placed after `LeafPushSec`:

| Section | Source | Changes (diff of the section against its source, python `difflib`) |
| --- | --- | --- |
| `GlueT32aSec` | `scratch/glue-t32a/T32a.lean` (contains `scratch/glue-b3b/B3b.lean`) | imports and `#print axioms` dropped; two `namespace LeafPush` blocks (L1473-1506, L1612-1632) dropped, because they re-declare `LeafPush.GQ`, `IsAtPrime`, `inertiaQ`, `T32b_QuadraticRamification` and `T32a_TameQuadratic`, whose bodies are identical to `LeafPushSec` (checked declaration by declaration) |
| `LeafQMSec` | `scratch/leaf-qm-fp/QMLeaves.lean` | imports and `#print axioms` dropped; one renaming, `GlueA6Alg.goodReduction_of_QM_rational3'` ↦ `PkgI2.goodReduction_of_QM_rational3'` (the same theorem: the kernel's A6 module is `Leaves.lean`'s A6 section); closing `end` added |
| `LeafModCurvesSec` | `scratch/leaf-modcurves/ModCurveLeaves.lean` | imports and `#print axioms` dropped; the docstrings of `R16_EichlerShimuraJ1'` and `DimJ1Genus` now say that MC9 is a citation-chain fact (M1); closing `end` added |
| `DefFaltingsSec` | `scratch/def-faltings/Faltings.lean` | imports and `#print axioms` dropped |

No statement-bearing line changed except that one renaming. The names used from the kernel
resolve to `Leaves.lean`'s copies, which are the kernel's: `PkgI3.AbVar`,
`ObjBridge.TorsionStructure`, `ObjBridge.dim`, `GlueC10.IsFrobAt`, `GlueC10.Zbar`. A fifth section,
`LeafAdoptSec`, is new. It contains the repairs (§2), H5 and `LeafAdopt.abVarEquiv`. The last of
these is a proved equivalence between def-faltings' copy `ZInQ.DefFaltings.AbVar` and
`PkgI3.AbVar`; they have the same four fields, and the equivalence preserves `dim` by `rfl`.

The first compile after the insertion had 0 errors (3m29s). So did the compile after the bundle
edits (3m13s).

## 2. The repairs of rv-blueprints that concern leaf statements

| Repair | What was done in Lean | Status |
| --- | --- | --- |
| Q2, R5fpStrong | `LeafAdopt.R5fpStrong`, transcribed from `scratch/rv-blueprints/R5Repair.lean` onto leaf-qm-fp's `QMPair`, `fieldOfModuliPair`; **proved** `R5fp_iff_R5fpStrong`. leaf-qm-fp's `R5fp` already carries `k ↪ ℚ(x)` for `b ≥ 1`. | VERIFIED |
| Q3, R1an in family form | R1(b) restated in the placeholder's docstring: (a) each `P` uniformized; (b) every `τ ∈ ℍ` occurs; (c) `τ ↦ π(P_τ)` holomorphic. Still `opaque`, because analytification is missing. | placeholder |
| Q4, `π₀(X₆) = 1` | Leaf clause `LeafAdopt.R1pi0Props X := GeometricallyConnected X.hom` (Mathlib). It is added to the bundle `R1R2fpRep` and counted inside R1 (Deligne 1971 §2, UNVERIFIED locator). rv-blueprints' glue alternative (from `R5fpCount` and Kummer parity of branch points) is recorded as SPECULATIVE. | stated as leaf |
| Q5, biconditional CM clauses | `LeafAdopt.R2X6PropsIff`. It is **proved** from leaf-qm-fp's one-way clauses with `CMExists` (`r2X6PropsIff_of`, via `cm_of_val`), and it gives `CMExists` back with `X6Surj` (`cmExists_of_iff`). So the biconditionals are glue and add nothing to the published content. | VERIFIED |
| bundle | `LeafAdopt.R1R2fpRep` is leaf-qm-fp's `R1R2fp` with `R2X6Props ∧ CMExists` replaced by `R2X6PropsIff`, plus `R1pi0Props`. **Proved** `R1R2fp_of_rep : R1R2fpRep → R1R2fp`, so every glue theorem of leaf-qm-fp applies. | VERIFIED |
| M1, R16 for the `K_N` model | Nothing to change in the statement. `R16_EichlerShimuraJ1'` quantifies over every `J` with `IsJ1 N J` (Jacobians of every `K_N` model). MC9 is dropped as a leaf; the docstrings say it belongs to the citation chain. | docstrings |
| F2, H5 explicit | `LeafAdopt.H5` is a field `h5` of `ResearchLeaves`. | stated as leaf |
| F1, additivity | h-decomposition's remark under R20 is corrected. Invariance under base change follows from the definition. Additivity does not: E4 needs `h(A)+h(Z) ≤ h(A×Z)`, which needs Néron models and H5. | doc |

## 3. Glue impact

The removed placeholders occurred only in the bundles `ResearchLeaves` and `TextbookLeaves`
(grep). `HSyn.glueOutputs_of_leaves` is a `sorry` that ignores its arguments. So no glue step
type-checked against a placeholder, and no glue statement changed. The glue proved in the adopted
files is now in `Leaves.lean` (compiled):
- A7: `LeafQM.AV.conj_iso_of_rational`, `fibre_conjugates_isomorphic`.
- A4: `exists_fibre_object`.
- h-b1 M9: `cm_of_val`.
- Lemma NV step 2: `residue_unramified_over_branch`.
- A3: `Level3.onto`, `Level3.torsor`.
- A6 on leaf-qm-fp's objects: `QML3.goodReduction`.
- `exists_J1`.
- E2's genus half: `dim_J1_le`.
- G13: `g13_constituent`.
- C9's trace half: `rhoF_traces`, `rhoF_attached`.
- `stableFaltingsHeight_eq_iInf_height` and `modelHeight_eq_of_model_eq`.
- T32: `t32a_glue`, `t32b_glue`, `leafB3a_glue`.

The adopted files also introduce glue targets, which are unproved and are not leaves:
- `X1ModelExists`: without it R16 is vacuous;
- `BelyiX1`;
- `VSurjOfSurjective`.

## 4. What compiles

- `lake env lean scratch/h-decomposition/Leaves.lean`: exit 0, one `sorry` warning (L19192,
  `glueOutputs_of_leaves`), 3m13s (VERIFIED, run3; see the log).
- New `#print axioms`: `HSyn.t32a_glue`, `t32b_glue`, `leafB3a_glue`,
  `GlueB3Unram.unramified_outside_noLeaf`, the adopted leaf-qm-fp, leaf-modcurves and def-faltings
  theorems, `LeafAdopt.r2X6PropsIff_of`, `cmExists_of_iff`, `R1R2fp_of_rep`,
  `R5fp_iff_R5fpStrong`, `abVarEquiv_dim`. Each gives `[propext, Classical.choice, Quot.sound]`.

## 5. What remains

- Placeholders R1(b), R3, R17, R18, R22, T10-T12. def-ladic-cond's R17 is still not folded; it
  was outside this task.
- The premise bp-qmmoduli §2.2.
- AN3 and `HodgeLatticeTheorem`.
- The glue targets above, and the glue of leaf-qm-fp §4.
- Unifying the duplicate abelian-variety layers (WP1).
- `glueOutputs_of_leaves`.

h-decomposition §5 ends with this list as "Remaining work after leaf-adopt".

## 6. Independent check of this diff

(See §7.)
