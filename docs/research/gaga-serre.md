# gaga-serre: the GAGA leaf in Serre's printed form

**Result (VERIFIED: compiled; `lake build ZInQKernel.Contrib.OneProof.SerreGAGA` succeeds and every theorem below
has axioms `propext`, `Classical.choice`, `Quot.sound`).** `gagaMorphism` is now a theorem from printed leaves
only. The GAGA leaf is Serre's theorem on holomorphic maps of projective varieties, stated over Serre's own
objects. The review's objection to sga1-fix's `SGA1_XII_4_4` was that SGA 1's `𝒪_{X^an}` may be nonreduced. That
objection does not apply here: Serre's `X^h` is reduced by construction, and the identification of Serre's
sheaf and maps with the repository's `AnFunAt` and `IsAnMorphism` is now a Lean proof.

```lean
theorem SerreGAGA.gagaMorphism_of_serre (hM : MumfordComplexTorus) (hL : SGA1_XII_3_3a)
    (hPC : ProperCompactAn) (hC : SGA1_XII_2_4) (hS : SerreGAGAMorphism) : ZInQ.HomLattice.GAGAMorphism
```

- **Count (VERIFIED dry run).** Measured against the 11-16 re-rating (`gagaMorphism` and `uniformizationLeafAll`
  both GLUE, as on `origin/wip/leaf-fold32`), the fold goes from 33/12 to 38/10 in both the strict and the
  strictest column. That is **−2 GLUE**, which meets the target. At the merged base as committed (`gagaMorphism`
  still LEAF there), the dry run prints 34/11 → 38/10.
- **Base.** `origin/main` (2880fef1e) was merged first; the merge was clean. Fork PR #35, which would prove
  `uniformizationLeafAll` outright, has not landed on `origin/main`:
  `cloud-b3/w17-pub-uniformization` is not an ancestor of it. sga1-fix's route for `uniformizationLeafAll` is
  therefore kept unchanged.
- **Files.** The contribution is `ZInQKernel/Contrib/OneProof/SerreGAGA.lean`. It imports
  `ZInQKernel.Contrib.OneProof.SGA1Printed` and the vendored `…Jacobian.AlgebraicGeometry.Group.QuasiProjective`,
  never `OneProof.Main`. No statement was changed, and nothing else under `ZInQKernel/` was edited.

## 1. The leaf and Serre's objects (verbatim; namespace `SerreGAGA`)

```lean
def IsProjVar (X : Over (Spec (CommRingCat.of ℂ))) : Prop :=
  IsReduced X.left ∧
    ∃ (N : Type) (_ : Finite N) (i : X.left ⟶ ℙ(N; Spec (CommRingCat.of ℂ))),
      IsClosedImmersion i ∧ i ≫ ℙ(N; Spec (CommRingCat.of ℂ)) ↘ Spec (CommRingCat.of ℂ) = X.hom

def SerreHolAt (X : Over (Spec (CommRingCat.of ℂ))) (F : CPt X → ℂ) (P : CPt X) : Prop :=
  ∃ c : AffineChart X, XPtIn X P c.U ∧ ∃ H : (Fin c.k → ℂ) → ℂ,
    AnalyticAt ℂ H (fun i => XevalAt X c.U (c.f i) P) ∧
    ∀ᶠ Q in @nhds _ (analyticTopology X) P, F Q = H (fun i => XevalAt X c.U (c.f i) Q)

def IsSerreHolMap (X Y : Over (Spec (CommRingCat.of ℂ))) (F : CPt X → CPt Y) : Prop :=
  @Continuous _ _ (analyticTopology X) (analyticTopology Y) F ∧
    ∀ (P : CPt X) (s : CPt Y → ℂ), SerreHolAt Y s (F P) → SerreHolAt X (s ∘ F) P

def SerreGAGAMorphism : Prop :=
  ∀ (X Y : Over (Spec (CommRingCat.of ℂ))), IsProjVar X → IsProjVar Y →
    ∀ F : CPt X → CPt Y, IsSerreHolMap X Y F → ∃ f : X ⟶ Y, ∀ P, F P = P ≫ f
```

Every object is an existing concrete definition; no structure was invented:
- `ℙ(N; S)` is the vendored Jacobian-Challenge `ProjectiveSpace`, the base change of `Proj ℤ[x_N]`. It is the
  same `ℙ` that TailZ24's `IsVeryAmple` uses.
- `IsClosedImmersion` and `IsReduced` are Mathlib's.
- `CPt`, `XPtIn` and `XevalAt` (ℂ-points, membership, evaluation) are unif-printed's.
- `AffineChart` and `analyticTopology` are unif-topology's. An `AffineChart` is an affine open with ℂ-algebra
  generators, i.e. `U ↪ 𝔸^k`. `analyticTopology` is the topology glued from all of them.
- `AnalyticAt` is Mathlib's.

**How each piece matches Serre** (GAGA §1–§2; numbering UNVERIFIED, standard content):
- *Varieties.* Serre's varieties are FAC varieties: reduced, separated, of finite type over ℂ, not necessarily
  irreducible. A projective variety is a closed subvariety of a projective space, which is `IsProjVar`. Its
  points are the closed points, i.e. `CPt X` (ℂ-morphisms `Spec ℂ → X`).
- *The space `X^h`.* `X(ℂ)` with the topology induced on each affine piece `U ⊂ ℂ^k` is `analyticTopology`. Its
  structure sheaf is the sheaf of functions that are locally restrictions of holomorphic functions of the
  coordinates of an affine piece, which is `SerreHolAt`. A space built this way is reduced: its sections are
  functions.
- *Holomorphic maps.* A holomorphic map is a continuous map that pulls back germs of holomorphic functions:
  `IsSerreHolMap`.
- *"F is regular."* This means `F` is the map on points of a morphism of varieties, i.e. a ℂ-morphism of
  reduced ℂ-schemes: `∃ f : X ⟶ Y, ∀ P, F P = P ≫ f`.

## 2. Glue proved (all VERIFIED, compiled, standard axioms; `scratch/gaga-serre/axioms.txt`)

| theorem | content |
| --- | --- |
| `anFunAt_eventually` | `AnFunAt X F P` is an open condition in `P` (`AnalyticAt.eventually_analyticAt`, `continuousAt_xevalAt_an`) |
| `isAnMorphism_iff_germ` | sga1-fix's `IsAnMorphism` (stated with opens `W`) ⇔ continuous and pulls back germs at every point |
| `exists_affineChart_le` | every open `U ∋ P` contains an `AffineChart` at `P` (`X` locally of finite type) |
| `anFunAt_iff_serreHolAt` | **`AnFunAt X F P ↔ SerreHolAt X F P`**. The arbitrary regular functions `g` are restricted to an affine chart inside `U`, and there `gⱼ = pⱼ(f)` with `pⱼ` polynomials (`Generates`, `evP_eval₂`) |
| `isAnMorphism_iff_isSerreHolMap` | **`IsAnMorphism X Y F ↔ IsSerreHolMap X Y F`** (`X`, `Y` locally of finite type) |
| `locallyOfFiniteType_of_isProjVar` | projective varieties are of finite type (closed immersion followed by the proper `ℙ^N → Spec ℂ`) |
| `isProjVar` | **abelian varieties are projective varieties**. `A` is integral (`GeometricallyIntegral.isIntegral_of_subsingleton`), hence reduced. The vendored `GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral` gives an immersion `i : A → ℙ^N_ℂ` over ℂ. `i` is proper (`IsProper.of_comp`, since `ℙ^N_ℂ` is separated), so its range is closed and `i` is a closed immersion (`IsClosedImmersion.of_isPreimmersion`) |
| `sga1_XII_4_4_of_serre` | `SerreGAGAMorphism → SGA1Printed.SGA1_XII_4_4` |
| `gagaMorphism_of_serre` | **main theorem**, through sga1-fix's `gagaMorphism_of_printed` |

CHART_INDEPENDENCE_PLACEHOLDER

## 3. Does Serre state the morphism result itself? (UNVERIFIED: GAGA was not available to this task)

There is no copy of GAGA on this host, and no repository note quotes its §4. **From memory (SPECULATIVE):**
- GAGA §4 ("Applications") proves Prop. 13 first: every analytic subset of `X^h`, for `X` projective, is
  algebraic. Chow's theorem is a corollary of it.
- It then states, as a separate proposition, that a holomorphic map from a projective variety `X` to an
  algebraic variety `Y` is regular. The proof applies Prop. 13 to the graph.
- I cannot say whether `Y` must be projective in the print. Either way, the leaf (both `X` and `Y` projective) is
  the print or a special case of it.

The autofold flag asks the statement check to confirm three things:
1. GAGA prints the holomorphic-map statement itself, not only Chow's theorem.
2. The statement has no irreducibility hypothesis (FAC varieties need not be irreducible).
3. The numbering.

**If the check finds only Chow's theorem**, the leaf should become Prop. 13, and the morphism form becomes glue.
That glue is not done here. It needs three steps:
- the graph `Γ_F` is a closed analytic subset of `(X × Y)^h`;
- the algebraic `Γ` that Prop. 13 gives has a projection `Γ → X` whose analytification is biholomorphic (its
  inverse is `x ↦ (x, F x)`);
- an algebraic morphism with biholomorphic analytification is an isomorphism (SGA 1 XII 3.1, per
  cloud-b3/w17-pub-gaga's note, or ZMT for normal `X`; abelian varieties are normal).

None of these is in the repository. A second printed source for the morphism form, also UNVERIFIED, is the
corollary to Chow's theorem in Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §3: holomorphic maps
between projective varieties are algebraic.

## 4. Ratings of the leaves in the fold

| leaf | source | rating |
| --- | --- | --- |
| `SerreGAGA.SerreGAGAMorphism` (**new**) | Serre, GAGA, Ann. Inst. Fourier 6 (1956), §4, the proposition on holomorphic maps (UNVERIFIED locator) | **printed form** (exact, or a special case if the print allows `Y` arbitrary) |
| `UnifPrinted.MumfordComplexTorus` | Mumford §1 | printed form (unif-printed; unchanged) |
| `SGA1Printed.SGA1_XII_3_3a` | SGA 1 XII Rem. 3.3(a) | printed form, special case and consequence (sga1-fix; unchanged) |
| `UnifTopology.ProperCompactAn` | **SGA 1 XII 3.2** first, then Serre GAGA §2 Prop. 6 (see below) | printed form (unif-topology; citation reordered) |
| `SGA1Printed.SGA1_XII_2_4` | SGA 1 XII 2.4, "only if" | printed form (sga1-fix; unchanged) |

**Why `SerreGAGAMorphism` is printed form.** The objects are Serre's at the level of definitions. This is the
review's point, and it is now proved rather than argued:
- `X^h` has the topology glued from affine pieces, and the sheaf of local restrictions of holomorphic functions
  (`SerreHolAt`);
- a holomorphic map pulls back germs (`IsSerreHolMap`);
- a projective variety is a reduced closed subscheme of `ℙ^N_ℂ`.

There is no nonreduced structure sheaf anywhere, so no second theorem identifies `𝒪_{X^an}` with functions.
The one translation is the standard dictionary between FAC varieties and reduced separated ℂ-schemes of finite
type: points are closed points, and regular maps are ℂ-morphisms. This translation is a definition-level
correspondence, not a theorem about analytic spaces.

The leaf asserts existence only. It does not assert uniqueness, which is automatic for reduced `X`. The conclusion
"F is regular" is exactly `∃ f, F = f` on points.

**What is now glue.** sga1-fix's `SGA1_XII_4_4` is a theorem (`sga1_XII_4_4_of_serre`), and so is the
identification `AnFunAt = SerreHolAt`, `IsAnMorphism = IsSerreHolMap`.

**`ProperCompactAn`: SGA 1 XII 3.2 is cited first.** The leaf quantifies over all proper ℂ-schemes `X`, which may
be nonreduced or non-separated in the sense of FAC varieties. That is the generality of SGA 1 XII 3.2 (for `f`
locally of finite type over ℂ, `f` is proper iff `f^an` is proper; take `Y = Spec ℂ`). Serre's GAGA §2 Prop. 6 is
stated for varieties, so it reaches the leaf only through `X_red` (`X(ℂ) = X_red(ℂ)`). The autofold spec's `doc`
and `source` for `properCompactAn` now read "SGA 1 XII 3.2 …; Serre, GAGA §2 Prop. 6 (for varieties)". The
docstring in `UniformizationTopology.lean` is unchanged, because that file is not this task's to edit. Locators
are UNVERIFIED.

**Locator note, from another task (not read by me).** `cloud-b3/w17-pub-gaga`'s README reports reading SGA 1
math/0206203v2. It says XII **Cor. 4.5** (pp. 250–251) is the full faithfulness for morphisms of proper schemes,
and Thm. 4.4 is the equivalence of coherent sheaves. So sga1-fix's "Thm. 4.4 and its corollary" is Cor. 4.5.
This affects only the docstring of `SGA1_XII_4_4`, which is no longer a leaf in this fold.

**Proposed rows for `docs/research/locators.md`** (not added; the file belongs to other tasks):
- `SerreGAGAMorphism`: Serre, GAGA (1956), §4, the proposition on holomorphic maps of projective varieties
  (proved from Prop. 13 through the graph). Exact form over Serre's objects. UNVERIFIED.
- `ProperCompactAn`: SGA 1, Exp. XII, Prop. 3.2 (with `Y = Spec ℂ`); Serre GAGA §2 Prop. 6 for varieties.
  UNVERIFIED.

DISCHARGES_PLACEHOLDER

## 6. Autofold spec (VERIFIED dry run)

`scratch/gaga-serre/autofold.json` (import `ZInQKernel.Contrib.OneProof.SerreGAGA`):

```
uniformizationLeafAll := _root_.SGA1Printed.uniformizationLeafAll_of_printed {n}.mumfordComplexTorus
  {n}.sga1_XII_3_3a {n}.properCompactAn {n}.sga1_XII_2_4
gagaMorphism := _root_.SerreGAGA.gagaMorphism_of_serre {n}.mumfordComplexTorus {n}.sga1_XII_3_3a
  {n}.properCompactAn {n}.sga1_XII_2_4 {n}.serreGAGAMorphism
```

- **Leaves.** Five leaves, each of kind `published`: `mumfordComplexTorus`, `sga1_XII_3_3a`, `properCompactAn`,
  `sga1_XII_2_4` and `serreGAGAMorphism`. Each is flagged `unread: new printed leaf, no reading recorded; locator
  UNVERIFIED`. The flag on `serreGAGAMorphism` adds the check request of §3.
- **Dry run.** `python3 scripts/one_proof/autofold.py scratch/gaga-serre/autofold.json --dry-run` exits 0. At the
  merged base it prints "34/11 on 45 -> 38/10 on 48; strictest 34/11 -> 38/10".
- **Re-rated base.** The `gagaMorphism` row of `kinds.tsv` was set temporarily to `consequence`/GLUE/GLUE, as on
  `origin/wip/leaf-fold32`, and the file was restored afterwards. The dry run then printed **"33/12 on 45 ->
  38/10 on 48; strictest 33/12 -> 38/10"**.

FOLD_PLACEHOLDER

**This spec replaces sga1-fix's**: fold this one instead. It drops `sga1_XII_4_4`. If sga1-fix's spec is folded
first, discharge its `sga1_XII_4_4` field with `_root_.SerreGAGA.sga1_XII_4_4_of_serre {n}.serreGAGAMorphism`.
If gaga-chart's is folded first, discharge `gagaChart` with `_root_.SGA1Printed.gagaChart_of_printed
(_root_.SerreGAGA.sga1_XII_4_4_of_serre {n}.serreGAGAMorphism)`.

## 7. What remains

- Statement check of `SerreGAGAMorphism` against GAGA §4 (§3 above: is the morphism statement printed, are there
  hypotheses, what is the numbering).
- Locator rows (§4) and the fold itself.

## 8. Files

- `ZInQKernel/Contrib/OneProof/SerreGAGA.lean`: the contribution.
- `scratch/gaga-serre/`:
  - `S1.lean`, `S2.lean`, `S3.lean`: development stages;
  - `Axioms.lean` with `axioms.txt`;
  - `DischargesCheck.lean` with `discharges.txt`;
  - `autofold.json`, `autofold-dryrun.txt`, `autofold-dryrun-rerated.txt`, `FoldDryRun.lean`;
  - `log.md`.
