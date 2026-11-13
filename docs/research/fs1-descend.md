# fs1-descend: FS1b′ `FiniteDescends` is proved (Mathlib only, no new leaf)

**Result.** The glue Prop FS1b′ `FiniteDescends` of scratch/g0-fibresimple/ (copied verbatim) is a theorem:
`FS1Descend.finiteDescends : FiniteDescends` in scratch/fs1-descend/FiniteDescends.lean, proved from Mathlib v4.35
alone. Along the way the file proves that finiteness satisfies fpqc descent in general,
`FS1Descend.isFinite_descendsAlong : MorphismProperty.DescendsAlong @IsFinite (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`,
and that separatedness and properness do too. No leaf and no new glue Prop is introduced. VERIFIED (compiled; standard axioms).

Consequence for g0-fibresimple: the bundle `FibreSimplePieces` = FS1b′ + FS5 shrinks to FS5 `FibreComTrivial` alone.
`G0FibreSimple.fibreSimple_of_leaves_fs5 (t : HSyn.TextbookLeaves) (hMul : MulIsogeny) (hRig : RigidityHom)
(hCom : FibreComTrivial) : FibreSimple` compiles against the unchanged FibreSimple.lean (integration check below).
FS5 is one of the three Props blocked by the QM pinning defect (task qm-pin), so this task did not work on it.

## Statement (verbatim from scratch/g0-fibresimple/FibreSimple.lean)

```lean
def FiniteDescends : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (X Y : Over (Spec (CommRingCat.of K)))
    (g : X ⟶ Y),
    IsFinite ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map g).left →
      IsFinite g.left
```

The statement is true and not vacuous: `X`, `Y` are arbitrary `K`-schemes, and the hypothesis is the usual
finiteness of `g_L : X_L → Y_L`.

## Proof

The g0-fibresimple report found that Mathlib's route through `HasAffineProperty.descendsAlong_of_affineAnd` needs
fpqc descent of `IsAffineHom`, which Mathlib lacks. This proof avoids affineness altogether. It uses Mathlib's
Zariski-main-theorem characterization of finite morphisms, `IsFinite ↔ IsProper ∧ LocallyQuasiFinite`
(`IsFinite.iff_isProper_and_locallyQuasiFinite`, tagged Stacks 02LS in Mathlib). Then:

1. **Separatedness descends.** `isSeparated_eq_diagonal_universallyClosed : @IsSeparated = diagonal @UniversallyClosed`.
   The diagonal is always an immersion (Mathlib instance). A universally closed diagonal has closed image, and an
   immersion with closed image is a closed immersion (`IsClosedImmersion.of_isPreimmersion`). Mathlib descends
   `UniversallyClosed` along fpqc morphisms (Stacks 02KS) and descends `P.diagonal` whenever `P` descends, which gives
   `isSeparated_descendsAlong`.
2. **Properness descends.** Rewrite with `isProper_eq` (separated ⊓ universally closed ⊓ locally of finite type).
   Mathlib already has the instance for `LocallyOfFiniteType` (LocalFlatDescent.lean). This gives `isProper_descendsAlong`.
3. **Local quasi-finiteness descends** along a surjection when the target morphism is locally of finite type
   (`locallyQuasiFinite_of_isPullback`). Take `z ∈ Z` and pick `x ↦ z` under the surjection `f : X → Z`. Each
   `y ∈ g⁻¹{z}` lifts to a point of the pullback `A` lying over `(x, y)` (`Scheme.exists_preimage_of_isPullback`).
   So `g⁻¹{z}` lies in the image of the finite set `fst⁻¹{x}` (`Scheme.Hom.finite_preimage_singleton`, since
   `fst` is finite). Mathlib's fibre criterion `LocallyQuasiFinite.of_finite_preimage_singleton` concludes.
4. **Finiteness descends** (`isFinite_descendsAlong`): combine 2 and 3 with `IsFinite.of_isProper_of_locallyQuasiFinite`.
5. **`finiteDescends`.** `Spec L → Spec K` is surjective and flat (`flat_and_surjective_SpecMap_iff` and
   `RingHom.faithfullyFlat_algebraMap_iff`, the same proof as g0-fibresimple's `specMap_flat_surjective`), and it is
   quasi-compact. Its base change `Y_L → Y` has the same three properties. The square formed by `X_L → Y_L` and
   `X → Y` is a pullback by `IsPullback.of_right`, since the outer square (`X_L` over `X`) and the right square
   (`Y_L` over `Y`) are both pullbacks. Apply step 4.

Technical note: the file sets `backward.isDefEq.respectTransparency.types false`, as Mathlib's FlatDescent.lean
does. Without it, instance search fails on `IsStableUnderBaseChangeAlong @Surjective Y.hom` and on the
diagonal-descent instance.

## What compiles (VERIFIED)

* `lake env lean scratch/fs1-descend/FiniteDescends.lean`: exit 0 in 76 s, no errors, no warnings. `#print axioms`
  for `FS1Descend.finiteDescends` and `FS1Descend.isFinite_descendsAlong` gives [propext, Classical.choice, Quot.sound].
* `scratch/fs1-descend/check_integration.sh` assembles g0-fibresimple's FibreSimple.lean verbatim, then
  FiniteDescends.lean, then IntegrationTail.lean, in the gitignored `.checks/` (20784 lines; needs
  `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` first). Result: exit 0 in
  193 s, 0 errors, no `sorry`. In it, `G0FibreSimple.finiteDescends_proof : FiniteDescends := FS1Descend.finiteDescends`
  typechecks against g0-fibresimple's own definition, and `G0FibreSimple.fibreSimple_of_leaves_fs5` compiles. Both,
  as well as `HSyn.glueOutputs_of_leaves`, have the standard three axioms.

## What remains

* Nothing for FS1b′. Integration step: in the g0-fibresimple chain, replace the field `finiteDescends` of
  `FibreSimplePieces` with `FS1Descend.finiteDescends`, or use `fibreSimple_of_leaves_fs5` from IntegrationTail.lean.
  The lemmas could also go into ZInQKernel/HDecomp/ as a Mathlib-only module.
* The fpqc descent instances proved here (`IsSeparated`, `IsProper`, `IsFinite`) are general and Mathlib-only, and
  could be upstreamed to Mathlib's Morphisms/FlatDescent.lean.
* FS5 `FibreComTrivial` stays open and is blocked by qm-pin.

Files: scratch/fs1-descend/FiniteDescends.lean (proof), IntegrationTail.lean and check_integration.sh (integration
check), log.md.
