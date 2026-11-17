# hcm-weierstrass (fleet note)

**Result.** Step G1 of `hCM` is now proved in Lean. G1 is the gap between Shimura's "analytic isomorphism
`ℂ/𝔞 → E(ℂ)`" and the clause form `IsAnalyticUnif`. No hypotheses were added. The proof is in
`ZInQKernel/Contrib/OneProof/ShimuraThm54Biholo.lean` (namespace `ZInQ.Contrib.HCMWeierstrass`), which imports only
`ShimuraMainCM`. It uses only the standard axioms and has no `sorry`.

* **`E(ℂ)` as a complex manifold.** The points `E.toAffine.Point` of any short Weierstrass model over `ℂ` are given:
  * a topology: the one-point compactification of the affine curve, which is the `ℙ²` topology;
  * an atlas whose charts are the coordinates `x`, `y` (at the points with `y = 0`) and `t = -x/y` (at `O`).

  Mathlib's `IsManifold 𝓘(ℂ) ω` holds for it (`isManifoldPoint`, `chartAt_coe`, `atlas_coord`).
* **The Weierstrass map is biholomorphic.** `ξ_L` has the cosets of `L` as fibres, is onto, and is a local
  biholomorphism in the sense of Mathlib's `IsLocalDiffeomorph` (`toPoint_isAnalyticIso`). The proof uses the inverse
  function theorem with three local coordinates:
  * at `O`: `t ∘ ξ = 2(z + z³E)/(2 - z³D)`, with derivative 1;
  * at the 2-torsion points: `y ∘ ξ = ℘'/2`, with `℘'' = 6℘² - g₂/2` proved;
  * elsewhere: `x ∘ ξ = ℘`.
* **The dictionary, in both readings of the print.**
  * `IsAnalyticUnif ↔ IsAnalyticIso ∧ additive`.
  * `IsAnalyticUnif ↔ IsAnalyticIso ∧ ξ 0 = O`. This form rests on a theorem that a biholomorphism `ℂ/Λ → E(ℂ)` with
    `0 ↦ O` is a group homomorphism (Liouville on the derivative of the local lifts).
* **New leaf `ShimuraThm54Biholo`.** This is Shimura's Theorem 5.4 with the analytic isomorphisms of section 1. Its
  hypothesis asks `ξ(0) = O` and its conclusion asks no group law, so it is weaker than or equal to the print in either
  reading. The discharge is `shimuraThm54_of_biholo : ShimuraThm54Biholo → ShimuraThm54`.

**What compiles (VERIFIED).**
* `lake build` of the new module, and of Main and Discharges (16047 jobs).
* `#print axioms`: standard (`scratch/hcm-weierstrass/Axioms-output.txt`).
* `#discharges`: `DISCHARGES [hCM] by ZInQ.Contrib.HCMWeierstrass.shimuraThm54_of_biholo`, which still assumes
  `[ShimuraThm54Biholo]`; axioms standard.
* `FoldCheck.lean` (the frozenTarget with `hCM` filled, and the folded body): axioms standard.
* `autofold.json` is written. The fold is manual, because `hCM` is a top-level hypothesis.
* `scratch/hcm-weierstrass/Combined.lean`: hcm-lattice's file copied, plus about 90 new lines. Axioms standard. It
  proves:
  * `hcmLattice_isAnalyticIso_iff`: with `ξ(0) = O`, hcm-lattice's ℙ²/immersion `IsAnalyticIso` is equivalent to
    this file's;
  * `ShimuraThm54LocalBiholo → ShimuraThm54`. This leaf has the print's analytic isomorphisms and the print's
    `p`-component `s⁻¹𝔞`, so it removes G1 and R2 together. It becomes the recommended fold once `HCMLattice.lean`
    is in the tree.

**What remains.**
* R2 in the tree: hcm-lattice's proof is still a scratch file. The combined leaf is ready for when it lands.
* The theorem numbers are UNVERIFIED.
* Proposed rating for `hCM`: published, strict LEAF, strictest GLUE until R2 is settled.

Report: `docs/research/hcm-weierstrass.md`.
