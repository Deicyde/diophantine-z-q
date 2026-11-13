# mobius-contrib: `MobiusGlue` from T5, in the Contrib build

Task mobius-contrib, 2026-11-13. Base: fork main 57a7fa26, merged with `origin/wip/image-plane`
(8f9505f7) and then once with `origin/main` (b7cdba8e). Results log: `scratch/mobius-contrib/log.md`.
This is model work only; no human has reviewed it.

Marks: **VERIFIED** = compiled, computed, or read in a file.

## 1. Result

image-plane's proof that the kernel's `MobiusGlue` follows from the textbook leaf T5 now builds
as five new modules under `ZInQKernel/Contrib/Mobius/`. `lake build
ZInQKernel.Contrib.Mobius.Main` succeeds (VERIFIED). The theorems are:

```lean
-- ZInQKernel/Contrib/Mobius/ImagePlane.lean
theorem LeafQM.AV.CurveGlue.mobiusGlue_of_T5 (hT : ObjBridge.TorsionStructure) : MobiusGlue
theorem LeafQM.AV.CurveGlue.mobiusGlue_of_t5 (h : PkgI2.TorsionStructure.{0}) : MobiusGlue
theorem LeafQM.AV.Pin.imagePlaneCurveClosed : ImagePlaneCurveClosed
```

- `MobiusGlue` is `LeafQM.AV.Pin.MobiusGlue`, the kernel's definition in
  `ZInQKernel/HDecomp/QM/Pin.lean`. It is imported, not redefined.
- `ObjBridge.TorsionStructure` and `PkgI2.TorsionStructure` (`ZInQKernel/HDecomp/Objects.lean`)
  are the kernel's statements of T5, `A(K̄)[n] ≅ (ℤ/n)^{2g}`. The kernel proves
  `ObjBridge.torsionStructure_iff` between them by `Iff.rfl`.

`#print axioms` output from `lake build ZInQKernel.Contrib.Mobius.Main` (VERIFIED):

```
'LeafQM.AV.CurveGlue.mobiusGlue_of_T5' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeafQM.AV.CurveGlue.mobiusGlue_of_t5' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeafQM.AV.Pin.imagePlaneCurveClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**contrib-check.** `scratch/contrib-check/Check.lean` now has `import
ZInQKernel.Contrib.Mobius.Main` and `#print axioms` lines for the two `MobiusGlue` theorems. I built
all its imports with `lake build` and then ran `lake env lean scratch/contrib-check/Check.lean`.
It exits with 0 and no errors, and every axiom set it prints is the standard three, including the
two new lines (VERIFIED, `scratch/mobius-contrib/check.out`). So the new modules have no name
clash with the other Contrib modules that Check.lean imports.

## 2. The modules

| module | source lines of `ImagePlaneFinal.lean` | content |
|---|---|---|
| `Contrib.Mobius.InfraDim` | 45-496 | infra-smooth-dim copy: dimension theory of smooth schemes (imports `Mathlib` only) |
| `Contrib.Mobius.Glue` | 498-1711 | mobius-glue: `MobiusGlue` from `CurveRatFactor`, `CurveSurj` and T5; `NormalizerFinite`, `AutOInnerFinite` (through the kernel's `TSkolemKW.leafSkolemNoether`) |
| `Contrib.Mobius.CurveFacts` | 1713-3895 | curve-glue: curve facts from C1b, C2K, C3K; (CI) `componentIrreducible`; the definitions `ImagePlaneCurve`, `ImagePlaneCurveClosed`, `AlgDep`, `ImageClosed` |
| `Contrib.Mobius.ImagePlane` | 3897-4681 | image-plane: (IC), (AD), C2K, (G1') and the end theorems |
| `Contrib.Mobius.Main` | new | imports `ImagePlane`; `#print axioms` of the three theorems |

Glue imports `Mathlib`, `ZInQKernel.HDecomp.QM.Pin` and `ZInQKernel.HDecomp.Textbook.SkolemNoether`.
These are the source file's imports.

**How the modules were made.**

1. `scratch/mobius-contrib/split.py` cut the file at those lines. That verbatim split compiled
   (commit f7830f2c).
2. The Lean metaprogram `scratch/mobius-contrib/Dead.lean` computed the closure of the constants
   reachable from the three theorems, through types, values and constructors. It listed the 65
   declarations of the 284 that lie outside that closure, with their source ranges.
3. `scratch/mobius-contrib/trim.py` removed those 65 declarations. Any whose name still appeared
   in the remaining text was kept; the one such case, `GlobalFunctionsConst`, I removed by hand
   after a second run of `Dead.lean`.
4. Each module's header lists what was removed. Examples:
   - the leaf-(L0) and leaf-(L) routes (`FiniteGlobalSections`, `GlobalFunctionsConst`,
     `curveFacts_of_L0_*`, `mobiusGlue_of_L0_*`);
   - the CM-free forms (`MobiusGlueNoCM`, `mobiusGlueNoCM_of_T5`, `R1R2fpRep`, …);
   - four unused InfraSmoothDim corollaries.

The kept declarations are textually unchanged: no declaration names or namespaces changed, and
no statement changed. The check is `scratch/mobius-contrib/subseq.py`: the nonblank body lines of
each module form an in-order subsequence of the source file (VERIFIED, all four True). No Tau
Ceti code was vendored; `diffcheck2.py` reports MOD-UNNOTED 0 and NOTE-ONLY 0 (VERIFIED).

## 3. Steps 3 and 4

**Step 3, the closed form of `GluePiecesPin.mobius`: not done, because T5 is not closed in
Contrib.**
- No theorem anywhere in `ZInQKernel/Contrib/`, on any `origin/*` branch, has type
  `PkgI2.TorsionStructure` or `ObjBridge.TorsionStructure` (VERIFIED by `git grep` over all
  refs).
- `docs/research/h-decomposition.md` lists T5 as open.
- tc-survey row 16 says Tau Ceti has T5 only for elliptic curves.
- The Contrib theorem `ZInQ.RLeaf.t36_torsionStructure` proves `X1Belyi.TorsionStructure`, which
  is a different statement: `E[N] ≅ (ℤ/N)²` for elliptic curves (leaf T36).
- Once T5 is proved, the closed form is `mobiusGlue_of_t5 t5_proof : MobiusGlue`.
- In this proof T5 enters only through the kernel's `Level3.torsor`, which `level3_finite` in
  `Contrib/Mobius/Glue.lean` uses for finiteness of the level-3 structures.
- `HSyn.GluePiecesPin` and `HSyn.TextbookLeaves` are defined only in the scratch file
  `scratch/h-decomposition/Leaves.lean`, not in the kernel. So the field form cannot be stated in
  Contrib. `mobiusGlue_of_t5` takes exactly the field type `PkgI2.TorsionStructure.{0}` of
  `TextbookLeaves.t5`.

**Step 4, `imagePlaneCurveClosed : ImagePlaneCurveClosed`: it compiles in Contrib, but its
statement is a scratch copy.**
- `ImagePlaneCurveClosed` is not a kernel definition: no file under `ZInQKernel/` outside
  `Contrib/Mobius` defines it (VERIFIED, grep).
- It is curve-glue's definition (`scratch/curve-glue/C3K.lean`, copied verbatim into
  `ImagePlaneFinal.lean`). It is now defined in `Contrib/Mobius/CurveFacts.lean`.
- The theorem `LeafQM.AV.Pin.imagePlaneCurveClosed` is in the Contrib build with the standard
  axioms. It proves this Contrib copy of the statement, not a kernel Prop.

## 4. Files

- New: `ZInQKernel/Contrib/Mobius/{InfraDim,Glue,CurveFacts,ImagePlane,Main}.lean`.
- New scratch: `scratch/mobius-contrib/{split.py,Dead.lean,trim.py,subseq.py,dead.out,dead2.out,check.out,log.md}`.
- Edited (as allowed): `scratch/contrib-check/Check.lean` (one import, two `#print axioms`
  lines).
