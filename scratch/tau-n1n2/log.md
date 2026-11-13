# tau-n1n2 results log

Start 2026-11-13 04:11 PST. Base 2dd83306. `lake build ZInQKernel.HDecomp.Faltings.H5BaseChange`: OK (04:21).

## Facts checked (VERIFIED by grep/read)
- N1 `NeronModelExists`, N2 `SemistableNeronIdentityComponent` are in the build:
  ZInQKernel/HDecomp/Faltings/H5Neron.lean:205, :603 (identical to scratch/h5-neron/Reduction.lean).
- N1 is consumed once: `TextbookLeaves.t41`, used in `glueOutputs_of_leaves` via
  `heightAdditivity_of_h5neron t.t41 r.h5.2 hPMH` (scratch/h-decomposition/Leaves.lean:33766).
  N2 is not consumed by `sixContactMin_of_leaves` (H5 stays a leaf `r.h5`).
- Mathlib v4.35: no file mentions Néron (grep -i neron over Mathlib/: no hit). Only
  `AlgebraicGeometry/Group/Abelian.lean` (proper geometrically integral group schemes commute).
- Objects.lean:393: no nonzero `AbVar` can be constructed in Mathlib v4.35.
- Anthropic FLT project: not on this host (no local copy found; no network). ATLAS index
  (~/atlas/index): only elliptic-curve NOS (easy direction) and Néron–Tate pairing; no Néron models.
  Tau Ceti index: Néron–Tate heights only.

## N1N2.lean — COMPILED 04:37 (0 errors; all 7 #print axioms: propext, Classical.choice, Quot.sound)
- §1 verbatim copies `IsBaseChangeOf`, `IsOpenSubgroupModel`, `NeronModelExists`,
  `SemistableNeronIdentityComponent`; `neronModelExists_iff`, `semistableNeronIdentityComponent_iff`
  (Iff.rfl with the build's declarations).
- §2 `NeronModelOver R L B` (Néron model of `B : AbVar L` over a ring `R → L`, BLR 1.2/1).
  Leaf `NeronModelExistsSelf` (BLR 1.4/3 literal: B over L, model over 𝓞_L).
  `neronModelExists_of_self : NeronModelExistsSelf → NeronModelExists` PROVED.
- §3 leaf `LocalNeronModelExists` (DVR O ⊂ L), glue `NeronLocalToGlobal`;
  `neronModelExistsSelf_of_local`, `neronModelExists_of_local` PROVED.
- §4 `trivNeronOver`, `localNeronModelExists_zero`, `neronLocalToGlobal_zero` (zero AV) PROVED.
- Failed attempt (abandoned): transporting along `(B_L)_L ≅ B_L` (selfIso, pullback along
  Spec.map id) inside a `GroupModel` field: "(kernel) deterministic timeout" (known pattern,
  memory lean-kernel-iso-composite-timeout). Avoided by stating the leaf with `NeronModelOver`.

## N1N2.lean §5 — COMPILED 04:44 (0 errors; all 11 #print axioms: propext, Classical.choice, Quot.sound)
- `isMonHom_of_reflect` (general monoidal-functor lemma), `isMonHom_of_neron` (an iso of Néron
  group models compatible with `gen` is a group iso), `isOpenSubgroupModel_of_neron`.
- `SemistableNeronIdentityComponentSome` (N2 with "∃ Néron 𝒩'" instead of "∀ Néron 𝒩'").
- `semistableNeronIdentityComponent_of_some : Some → N2` PROVED; converse from N1 PROVED.

## N1N2.lean §3 revised, §6 — COMPILED 04:47 (0 errors; all 13 #print axioms: propext, Classical.choice, Quot.sound)
- §3: new leaf `AbelianSchemeIsNeron` (BLR 1.2/8, Dedekind R with fraction field L);
  `NeronLocalToGlobal` now takes it as hypothesis (so the glue uses no literature theorem beyond
  the textbook facts listed in its docstring); `neronModelExists_of_local hloc hab hglue`.
- §6: `resHom` (copy of HDecomp `toW`), `bcProj` (A_{L'} → A_{L₀}), `LocalSemistableAt A O`
  (canonical local statement: open immersions U → 𝒩', U → 𝒩₀ ×_{O₀} O', compatible on generic
  fibres), leaf `LocalSemistableIdentityComponent` (SGA 7 IX 3.6 + 3.3 local), `SemistableNeronAt`,
  glue `SemistableLocalToGlobal`; `semistableNeronIdentityComponent_of_local` and
  `n1_n2_of_leaves` PROVED.

## N1N2.lean converse — COMPILED 05:13 (0 errors; 14 #print axioms, all propext, Classical.choice, Quot.sound)
- `selfIso` ((B_L)_L ≅ B_L) as `noncomputable irreducible_def`; `isMonHom_pullbackId`,
  `isMonHom_selfIso`, `selfGen`, `selfGen_hom`, `selfGen_isMonHom`, `genIso_neron`, `selfGen_neron`,
  `neronModelExistsSelf_of : NeronModelExists → NeronModelExistsSelf`,
  `neronModelExistsSelf_iff` PROVED.
- FINDING (Lean): with `selfIso` a plain `def` (eqToIso ≪≫ pullbackId.app), the kernel timed out
  ("deterministic timeout") on `selfGen_hom := Iso.trans_hom _ _`, on `selfGen_isMonHom` and on
  the structure literal; `irreducible_def` fixes all three.
- Independent model review (subagent, read-only) of all new defs: no PROBLEM; three MINOR
  docstring points fixed (EGA IV 8.8.2 for agreement of spread-out models; compositum step;
  SGA 3 VI_A 2.4 / EGA IV 4.5.13 for identity components under base change).

## N1N2.lean §7 — COMPILED 05:15 (0 errors; 15 #print axioms, all standard)
- `NeronModelOver.neronProp`, `NeronModelOver.uniqueIso` (two Néron models over any base `R` are
  isomorphic by a group isomorphism compatible with `gen`) PROVED (glue lemma for the two glue Props).

## N1N2.lean §8 — COMPILED 05:16 (0 errors; 17 #print axioms, all standard)
- `trivNeronOver'` (Néron model `𝟙` of any `B` with `B.X ≅ 𝟙`), `bothSides_over` (for every `A`:
  both sides of the compatibility equation of `LocalSemistableAt` agree after `𝒩₀ → Spec O₀`),
  `localSemistableAt_zero` (the conclusion of leaf N2-loc holds for the zero AV, `L₀ = K`) PROVED.
- Lean note: with `L₀ = K` there are two `Algebra K L'` instances in context (`[Algebra K L']`,
  `[Algebra L₀ L']`); explicit `@` needed. `erw` on `Over.w` facts hit the heartbeat limit;
  explicitly typed `have`s + `rw [reassoc_of% …]` work.
