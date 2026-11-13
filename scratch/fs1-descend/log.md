# fs1-descend results log

## Statement
- `FiniteDescends` copied verbatim from scratch/g0-fibresimple/FibreSimple.lean (lines 20518-20523; depends only
  on Mathlib) into scratch/fs1-descend/FiniteDescends.lean, namespace `FS1Descend`.

## FS1b′ proved
- 04:19 `lake env lean scratch/fs1-descend/FiniteDescends.lean`: exit 0 in 76 s, no errors, no warnings;
  `#print axioms FS1Descend.finiteDescends` and `FS1Descend.isFinite_descendsAlong`: [propext, Classical.choice,
  Quot.sound]. VERIFIED (compiled).
- Proof (all from Mathlib v4.35, no new leaf):
  - `isSeparated_eq_diagonal_universallyClosed : @IsSeparated = diagonal @UniversallyClosed` (diagonal is an
    immersion, Mathlib instance; immersion + closed range ⇒ closed immersion, `IsClosedImmersion.of_isPreimmersion`).
  - `isSeparated_descendsAlong`, `isProper_descendsAlong` (instances, along `Surjective ⊓ Flat ⊓ QuasiCompact`):
    from Mathlib's descent of UniversallyClosed, LocallyOfFiniteType and of diagonals; `isProper_eq`.
  - `locallyQuasiFinite_of_isPullback`: for a pullback square with `f` surjective, `g` locally of finite type and
    `fst` locally quasi-finite and quasi-compact, `g` is locally quasi-finite (fibre criterion
    `LocallyQuasiFinite.of_finite_preimage_singleton`, `Scheme.exists_preimage_of_isPullback`).
  - `isFinite_descendsAlong : DescendsAlong @IsFinite (@Surjective ⊓ @Flat ⊓ @QuasiCompact)` via
    `IsFinite.of_isProper_of_locallyQuasiFinite` (Mathlib, ZMT file, Stacks 02LS).
  - `finiteDescends : FiniteDescends`: `Y_L → Y` is a base change of `Spec L → Spec K` (surjective, flat,
    quasi-compact); `X_L → Y_L` over `X → Y` is a pullback by `IsPullback.of_right`.
- Note: the file needs `set_option backward.isDefEq.respectTransparency.types false` (as Mathlib's
  FlatDescent.lean does); without it instance search fails on `IsStableUnderBaseChangeAlong @Surjective Y.hom`.
