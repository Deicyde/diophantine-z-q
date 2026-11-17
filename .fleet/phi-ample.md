# phi-ample (fleet summary)

**Verdict: `mumfordKLFiniteSectionAC` removed, −1, no new leaf.** Mumford §6 Application 1 (`K(L)` finite for
ample `L`) is now a Lean theorem over every field. It is proved inside the context of `PhiAmpleIsogeny`
(representation of `Pic`, `Pic⁰ = (B, j)`, lift `λ_L`). The argument: an integral closed `Z` in `ker λ_L` has
`(1×i)^*Λ(L) = 1` by Kleiman 9.2.5 (vendored, already proved), hence `i^*L ⊗ i^*(−1)^*L = 𝒪_Z` with both factors
ample, hence `Z` is affine and so a point; the kernel is noetherian, hence finite.

**Compiles (VERIFIED, standard axioms, no sorry):**
* `ZInQKernel/Contrib/OneProof/MumfordKLFinite.lean`, with `PhiAmple.mumfordKLFiniteSectionAC_of_open : L1 → L2 →
  PicFix.MumfordKLFiniteSectionAC` (L1, L2 are fields of the same bundle `OpenAddedLeaves19`),
  `mumfordKLFiniteAC_of_open`, `finite_ker_pts`, and `phiAmpleIsogeny_of_phiSurjective : MumfordPhiSurjectiveAC →
  PhiAmpleIsogeny`.
* `lake build` of Main + Discharges + the file succeeds (14102 jobs).
* `#discharges`: `OpenAddedLeaves19.mumfordKLFiniteSectionAC` by `PhiAmple.mumfordKLFiniteSectionAC_of_open`,
  still assumes `[PicRepresentableAbVar, PicZeroAbVar]`.
* Fold spec `scratch/phi-ample/autofold.json` (no leaves):
  * on main, `16/21 on 37 -> 15/21 on 36` (strictest the same); the printed module compiles to
    `sixContactMin_of_open39`;
  * on leaf-fold33b, `15/20 on 35 -> 14/20 on 34`; it compiles to `sixContactMin_of_open40`.

**Remains:** `mumfordPhiSurjectiveAC` (Mumford §8 Thm 1, printed-form leaf, unchanged).
* Surjectivity of `λ_L` now amounts to `dim Pic⁰ = g` (§13, cohomology), which the tree does not have.
* Deriving it through `weilPairingMumford` would be circular: weil-proof's discharge of that field uses
  `PhiAmpleIsogeny`.
* Poincaré's complement needs surjectivity, so the field cannot be narrowed away.

Report: `docs/research/phi-ample.md`; log: `scratch/phi-ample/log.md`.
