# afr-absfrob (2026-11-13)

**Result: both glue Props of alg-frob-red are closed.** Statements are unchanged (VERIFIED with `cmp`).
- `AlgFrobRedRed.AbsFrob` is proved from Mathlib alone (`scratch/afr-absfrob/AbsFrobDef.lean`,
  `import Mathlib` only). The file constructs the absolute Frobenius `AbsFrobDef.fr p X : X ⟶ X`
  of a scheme with `p = 0`: the identity on the space and `s ↦ s^p` on sections, with local stalk
  maps. It proves `fr_naturality` (`f ≫ Fr_X = Fr_Y ≫ f`) and `fr_Spec`
  (`Fr_{Spec R} = Spec(r ↦ r^p)`).
- `AlgFrobRedRed.FExtendGen` is proved from the kernel leaf I2-NMP:
  `fExtendGen_of_nmp : PkgI2.NeronMappingAbelianScheme.{0} → FExtendGen`. The proof:
  - `F` lies over `Spec σ⁻¹|_L`. This is a Galois-rigidity lemma for maps from an integral
    scheme to `Spec L`.
  - The conjugate model `𝒜 ×_{Spec t} Spec O_w` is an abelian scheme.
  - NMP extends the generic morphism, and `F̃ = G ≫ pr₁`.
  - The unit section is fixed by Mathlib's `ext_of_isDominant_of_isSeparated`, applied twice.
- Hence `algFrobRed_of_nmp : GoodRedCofinite → SmoothGeomConnIntegral → I2-Red → I2-NMP →
  FrobTrace.AlgFrobRed`, and `tateBridge35_of_nmp`, which also takes I3.M0.

**What compiles.** `scratch/afr-absfrob/AfrAbsFrob.lean`, assembled by `build.sh` from a
`cmp`-identical copy of alg-frob-red's `AlgFrobRed.lean`, then `AbsFrobDef`, then
`part_fext.lean`. `lake env lean`: exit 0, no `sorry`, 95 axiom prints, all
`[propext, Classical.choice, Quot.sound]`. `AbsFrobDef.lean` also compiles on its own.

**What remains** (outside this task): the leaf candidates `GoodRedCofinite` and
`SmoothGeomConnIntegral`, and the kernel leaves I2-Red and I2-NMP. `FExtendGen` does not use
`IsFinite F`, `Surjective F` or the Frobenius clause of `hσ`.

Report: docs/research/afr-absfrob.md. Log: scratch/afr-absfrob/log.md.
