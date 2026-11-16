# sga1-fix (fleet note)

**Result: `uniformizationLeafAll` and `gagaMorphism` are both proved from printed leaves only (VERIFIED: compiled,
standard axioms, `#discharges` shows both fields discharged). The fold is −2 GLUE against the 11-16 re-rating:
44/12 → 49/10, and strictest 43/13 → 48/11.**

```lean
SGA1Printed.uniformizationLeafAll_of_printed (hM : MumfordComplexTorus) (hL : SGA1_XII_3_3a)
  (hPC : ProperCompactAn) (hC : SGA1_XII_2_4) : UniformizationLeafAll
SGA1Printed.gagaMorphism_of_printed (hM) (hL) (hPC) (hC) (hG : SGA1_XII_4_4) : GAGAMorphism
```

The three gaps the review found are closed:
- **(1) Étale leaf.** `SGA1_XII_3_3a` is SGA 1 XII Rem. 3.3(a), "f étale ⇒ f^an a local isomorphism". The leaf
  keeps only the topological part: `Q ↦ (fᵢ Q)` is a local homeomorphism.
  - The regular-functions half is now **proved in Lean** from étaleness alone (`regular_half`). It uses Mathlib's
    standard-étale local structure (`Algebra.IsEtaleAt.exists_isStandardEtale`) and the analytic inverse function
    theorem.
  - So the meaning of "isomorphisme local" no longer matters.
- **(2) Connectedness leaf.** `SGA1_XII_2_4` is SGA 1 XII 2.4 "only if", stated as asked: X locally of finite type
  and preconnected ⇒ X^an preconnected.
- **(3) GAGA leaf.** `SGA1_XII_4_4` is GAGA for morphisms of abelian varieties with no atlas: every
  `IsAnMorphism A(ℂ) → B(ℂ)` is `P ↦ P ≫ f`.
  - `IsAnMorphism` means continuous and pulling back `AnFunAt`, where `AnFunAt` is "locally H ∘ (regular
    functions), H holomorphic", the structure sheaf of the reduced `X^an`.
  - Proved in Lean: `IsAnStr` atlases have exactly these holomorphic functions and maps
    (`contMDiffAt_iff_anFunAt`, `contMDiff_iff_isAnMorphism`).
  - Proved in Lean: `AnFunAt` is the pullback of 𝒪_{ℂⁿ} along étale coordinates (`anFunAt_iff_etale`).
  - Proved in Lean: the étale atlas satisfies `IsAnStr` (`isAnStr_of_3_3a`).
  - Hence `GAGAChart ↔ SGA1_XII_4_4`.

**Ratings.** All three new leaves are printed form: 3.3(a) is a special case and consequence, 2.4 is exact, and
4.4 is a special case. All locators are UNVERIFIED; the page for 3.3(a), p. 325, comes from the review.

**What compiles.**
- `ZInQKernel/Contrib/OneProof/SGA1Printed.lean` (31 KB, imports GAGAChart) builds.
- `scratch/sga1-fix/discharges.txt` holds the `#discharges` output.
- `scratch/sga1-fix/autofold.json` discharges both textbook fields with the 5 leaves. Its dry run exits 0, and
  `FoldDryRun.lean` compiles.
- This spec replaces sga1-etale's and gaga-chart's specs. Fold order notes are in report §5.

**What remains.**
- Statement checks of the 3 new leaves against SGA 1 XII. Nobody has read 3.3(a), 2.4, 4.4 or 1.1 for this task.
- `locators.md` rows (proposed in the report, §3).
- The fold.

Report: `docs/research/sga1-fix.md`.
