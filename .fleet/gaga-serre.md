# gaga-serre (fleet note)

**Result: `gagaMorphism` is proved from printed leaves only, with the GAGA leaf now Serre's theorem on holomorphic
maps of projective varieties, stated over Serre's own objects (VERIFIED: compiled, standard axioms, `#discharges`
shows the field discharged). Against the 11-16 re-rating the fold is −2 GLUE: 33/12 → 38/10 (strict and strictest).**

```lean
SerreGAGA.gagaMorphism_of_serre (hM : MumfordComplexTorus) (hL : SGA1_XII_3_3a) (hPC : ProperCompactAn)
  (hC : SGA1_XII_2_4) (hS : SerreGAGAMorphism) : ZInQ.HomLattice.GAGAMorphism
```

- **The leaf.** `SerreGAGAMorphism` takes `X`, `Y` with `IsProjVar` (reduced closed subschemes of `ℙ^N_ℂ`) and `F`
  with `IsSerreHolMap`: continuous for the topology glued from affine pieces, and pulling back germs of
  `SerreHolAt`, the local restrictions of holomorphic functions of affine coordinates. It concludes
  `∃ f : X ⟶ Y, F = f` on ℂ-points. Serre's `X^h` is reduced by construction, which removes the review's
  nonreduced-`𝒪_{X^an}` objection.
- **Proved in Lean.** These theorems are in `ZInQKernel/Contrib/OneProof/SerreGAGA.lean`:
  - `AnFunAt ↔ SerreHolAt`;
  - chart independence: holomorphic in some affine chart ⇔ holomorphic in every affine chart, so any affine
    cover gives the same sheaf;
  - `IsAnMorphism ↔ IsSerreHolMap`;
  - abelian varieties are `IsProjVar`, using the vendored projective immersion plus properness, which makes the
    immersion closed;
  - hence `SGA1_XII_4_4` (sga1-fix's leaf) becomes glue.
- **Base.** `origin/main` was merged first. Fork PR #35 has not landed, so sga1-fix's `uniformizationLeafAll`
  route is kept.
- **Citation.** `ProperCompactAn` is now cited to SGA 1 XII 3.2 first, with GAGA §2 Prop. 6 for varieties.

**Rating.** `SerreGAGAMorphism` is printed form: exact, or a special case if the print allows any `Y`.
- Locator UNVERIFIED: GAGA is not on the host.
- From memory (SPECULATIVE), §4 states the holomorphic-map proposition itself and proves it from Prop. 13
  (Chow) via the graph.
- The kinds flag asks the statement check to confirm that it is printed, not only Chow, and that it has no
  irreducibility hypothesis.
- If only Chow is printed, the morphism form needs graph glue plus isomorphism reflection. That is not done
  (report §3).

**What compiles.**
- `lake build ZInQKernel.Contrib.OneProof.SerreGAGA` builds.
- `scratch/gaga-serre/discharges.txt` holds the `#discharges` output, after a full chain build at the merged
  base (13,698 jobs).
- `scratch/gaga-serre/autofold.json` replaces sga1-fix's spec. It has 5 leaves, and `sga1_XII_4_4` is dropped.
  Its dry run exits 0, and `FoldDryRun.lean` compiles.

**What remains.** The statement check of `SerreGAGAMorphism` against GAGA §4, the `locators.md` rows (proposed in
the report, §4), and the fold.

Report: `docs/research/gaga-serre.md`.
