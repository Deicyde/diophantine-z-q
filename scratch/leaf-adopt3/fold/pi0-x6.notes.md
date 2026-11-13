# pi0-x6 fold notes

Fragment: `scratch/leaf-adopt3/fold/pi0-x6.lean` (section `Pi0X6Sec`, namespace `Pi0X6`).
Source: `scratch/pi0-x6/Pi0X6.lean` (833 lines), copied verbatim. Only changes:
- imports and the 10 `#print axioms` lines are dropped;
- the file's open `noncomputable section` is now closed with `end`;
- a bridge block is appended.

The `sorry` occurrence is in the module docstring ("No `sorry`, no `axiom`."). It is not real.

## Bundle / glue rows

- **No bundle field changes.** As recommended, `LeafAdopt.R1pi0Props X` stays a clause of
  `LeafAdopt.R1R2fpRep`, counted inside R1.
- The reduction is added as proved theorems only. In the R1 row you can note: "`R1pi0Props`
  follows from `R5ptProps`, `R5fpCount` + `R2X6CMExact` + `AGInputs`
  (`Pi0X6.leafAdopt_r1pi0Props_of_X6Props`)".

## Bridging theorems (types exact; conclusion is the Leaves.lean clause)

```lean
theorem Pi0X6.leafAdopt_r1pi0Props_of_bundle {X : Over (Spec (CommRingCat.of ℚ))}
    {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {π₆ : ToP1 X.left}
    (h5 : R5ptProps X Ψ) (hcnt : R5fpCount) (hex : R2X6CMExact Ψ π₆) (hag : AGInputs π₆)
    (x₀ : fieldPt Qbar ⟶ X) : LeafAdopt.R1pi0Props X

theorem Pi0X6.leafAdopt_r1pi0Props_of_X6Props {X Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X}
    {π₆ : ToP1 X.left} (h6 : X6Props Y Φ X Ψ fY) (h5 : R5ptProps X Ψ) (hcnt : R5fpCount)
    (hex : R2X6CMExact Ψ π₆) (hag : AGInputs π₆) : LeafAdopt.R1pi0Props X
```

- Names are under `open LeafQM LeafQM.AV`: `Qbar` = `LeafQM.AV.Qbar`, and `R5ptProps`,
  `R5fpCount`, `X6Props` are `LeafQM.AV.*`.
- `R2X6CMExact` and `AGInputs` are `Pi0X6.*`.
- Both proofs are the file's `r1pi0Props_of_bundle` / `r1pi0Props_of_X6Props` (conclusion
  `GeometricallyConnected X.hom`, definitionally `LeafAdopt.R1pi0Props X`).

## New Props (glue inputs, not literature leaves)

- **`Pi0X6.R2X6CMExact Ψ π₆`** (`def … : Prop`). For each point `x` over `0` / `∞`:
  `π₆ = 0 ↔ Nonempty (com P.q ≃+* R4)` and `π₆ = ∞ ↔ Nonempty (com P.q ≃+* R3)`.
  - `R4` and `R3` are the full rings of integers of `ℚ(ζ₄)` and `ℚ(ζ₃)`.
  - This is R2's CM clause with "CM by R" in its printed meaning, a consequence of Baba–Granath
    2008 Thm 2.1 and the §3.1 table.
  - Count it inside R2, like `R2X6PropsIff`.
- **`Pi0X6.AGInputs π₆`** (`structure … : Prop`). Standard algebraic geometry that Mathlib v4.35
  lacks; open glue. Fields:
  - `over0`: every connected component of `X ×_ℚ Spec ℚ̄` contains a `ℚ̄`-point over `0`;
  - `overInf`: the same over `∞`;
  - `descend`: `ConnectedSpace X_ℚ̄ → GeometricallyConnected X.hom`.

  The Galois compatibility is proved (`compOf_galois`).

## Deleted as duplicate / kernel check

- Nothing deleted; every `Pi0X6.*` name is new.
- The file imports `ZInQKernel.HDecomp.QM.Leaves`. I compared each kernel declaration it uses with
  the copy in Leaves.lean section `LeafQMSec` (lines 14153-15654, same namespaces `LeafQM` /
  `LeafQM.AV`). The text is identical for:
  `R5ptProps`, `R5fpCount`, `ToP1`, `ToP1.val`, `ToP1.val_comp`, `residueImage`, `fieldPt`,
  `fieldMap`, `com`, `inertCount6`, `conductor`, `QMPair`, `pairSetoid`, `PtEquiv`, `X6Props`,
  `Qbar`, `specToEquivOfField_comp`, `QMStr`, `O`.
- The kernel QM files (`Structures`/`Pairs`/`Leaves`) and Leaves.lean's `LeafQMSec` declare the
  same set of names. So opening `LeafQM`, `LeafQM.AV` adds no new names that could become
  ambiguous.
- No kernel declaration needed copying. `LeafAdopt.R1pi0Props` is at Leaves.lean 18651
  (`GeometricallyConnected X.hom`).
- Leaves.lean has no root-level declarations and no top-level `open`. The other `Qbar` abbrevs are
  in namespaces the fragment does not open: `PkgI4`, `GlueC10`, `GlueB3Unram`, `LeafModCurves`,
  `HSyn`.

## Expected compile trouble spots

- **Full Mathlib import.** The scratch file imported QM.Leaves plus 6 selected Mathlib modules;
  Leaves.lean imports all of `Mathlib`. These tactics could behave differently with more
  simp lemmas or instances:
  - the bare `simp` calls in `gaussToO_apply` and `inertCount6_K4/K3` (`simp [h2, h3]`);
  - `simp at hK` in `gaussToO_bijective` and `coord_eq_zero`;
  - `push_cast` / `field_simp` steps;
  - `decide` in `finrank_K4/K3` and `parity_lemma`.
- **Instances.** The fragment adds global instances `NeZero ((4 : ℕ) : ℚ)`,
  `NeZero ((3 : ℕ) : ℚ)`, `IsCyclotomicExtension {4} ℚ K4`, `{3} ℚ K3` and
  `IsTotallyComplex K4/K3` (auto-named in `Pi0X6`). They are harmless but global.
- **`local notation`.** `"Qb"` (CoreSec) and `"ζ₃"` (Q3Sec) are section-local.

## `#print axioms` dropped

`subsingleton_of_galois`, `subsingleton_of_bundle`, `inertCount6_K4`, `pic_R4`,
`inertCount6_K3`, `pic_R3`, `subsingleton_components_of_bundle`, `r1pi0Props_of_bundle`,
`compOf_galois`, `r1pi0Props_of_X6Props` (all `Pi0X6.*`). All were
`[propext, Classical.choice, Quot.sound]` (`scratch/pi0-x6/compile_out.txt`). Suggested to add:
`Pi0X6.leafAdopt_r1pi0Props_of_X6Props`.
