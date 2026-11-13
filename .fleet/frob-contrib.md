# frob-contrib (2026-11-13)

**Result.** Two scratch developments are now modules under `ZInQKernel/Contrib/`. Every new
module builds with `lake build` and has standard axioms only.

- `ZInQKernel/Contrib/AbsFrob/{Basic,AlgFrobRed,Sanity}.lean`: afr-absfrob's absolute Frobenius.
  `AbsFrobDef.fr` is the identity on the space and `s ↦ s^p` on sections, both by `rfl`; the file
  also has `fr_naturality`, `fr_Spec`, and `AlgFrobRedRed.absFrob : AbsFrob` (the Prop is
  verbatim from alg-frob-red).
- `ZInQKernel/Contrib/UnramRoots/{Reduction,Metric,FrobData,Procyclic,Main,Sanity}.lean`:
  `G15Ram.UnramRoots p ℓ` holds for all `p, ℓ` (`UnramRootsTask.unramRoots(_all,_two)`), from
  Mathlib plus Tau Ceti modules that were already vendored. Nothing new was vendored and the
  NOTICE is unchanged.

**Statement check (independent reading, docs/research/frob-contrib.md §1).**
- `UnramRoots` is identical to local-glue's text. No hypothesis is stronger than needed (no
  continuity, `p ≠ ℓ` or Galois assumption) and no conclusion is weaker than its docstring.
- It is **not vacuous**, compiled at `p = 2`: the unramified quadratic character (`ψ(σ) = ±1`
  by the action on a cube root of unity ω) meets every hypothesis. ψ is nontrivial because
  `X²+X+1` has no root in `ℚ_2`, and the theorem then yields η with `η(σ)⁴ = −1`.
- AbsFrob: the statements are faithful. One hypothesis is redundant (`hY` in `fr_naturality`,
  which follows from `hX`); `fr_naturality'` drops it. Two checks rule out a trivial `fr`: it is
  `𝟙` on `Spec 𝔽_p` and not `𝟙` on `Spec 𝔽_p[T]`.

**Compiles.**
- The 9 modules: `lake build` exits 0.
- `scratch/frob-contrib/Check.lean` (contrib-check's file plus 13 new `#print axioms`) and
  `CheckFrob.lean`: every declaration is `[propext, Classical.choice, Quot.sound]`.
- Only new files were added; nothing on the pinned list changed.

**Remains.**
- The new modules are not imported by the root `ZInQKernel.lean`, so they must be built by name.
- local-glue and alg-frob-red are still scratch. Once they are adopted they should import
  `UnramRoots/Reduction.lean` and `AbsFrob/AlgFrobRed.lean` instead of redefining
  `G15Ram.UnramRoots` and `AlgFrobRedRed.AbsFrob`.
- afr-absfrob's `fExtendGen_of_nmp` was not adopted (outside this task).
