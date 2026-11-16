# gaga-chart: `gagaMorphism` from GAGA in chart form

**Result (VERIFIED: compiled; `lake build ZInQKernel.Contrib.OneProof.GAGAChart` succeeds, and every theorem below
has axioms `propext`, `Classical.choice`, `Quot.sound`).** The textbook field
`gagaMorphism : ZInQ.HomLattice.GAGAMorphism` is now a theorem. It follows from one new leaf, `GAGAAn.GAGAChart`
(GAGA for maps of complex abelian varieties, with the hypothesis "holomorphic in the charts of `A^an`, `B^an`" over
unif-topology's `analyticTopology`), and the existing textbook field `uniformizationLeafAll`, which every consumer of
`gagaMorphism` already takes next to it:

```lean
theorem GAGAAn.gagaMorphism_of_gagaChart (hU : UniformizationLeafAll) (hG : GAGAChart) :
    ZInQ.HomLattice.GAGAMorphism
```

The holomorphic inverse function step that the 11-16 dictionary pass found between the print's hypothesis and the
Lean one is now proved in Lean. It uses Mathlib's analytic inverse function theorem: `ContDiffAt.to_localInverse`,
and `OpenPartialHomeomorph.contDiffAt_symm` at `ω`. No reading step needs it any more. The restated leaf is rated
**printed form, special case** (§3). So the target is met: `gagaMorphism` is replaced by a printed leaf, and the
only other input is an existing field.

The file is `ZInQKernel/Contrib/OneProof/GAGAChart.lean` (33 KB). It imports:
- `ZInQKernel.OneProof.H.TailQ`, which defines `GAGAMorphism`;
- `ZInQKernel.Contrib.OneProof.SmoothComplexManifoldEtale`, sga1-etale's module, which brings unif-printed's and
  unif-topology's modules with it.

Those three contribution files must be in the tree. Their folds do not need to be applied. No statement was changed,
and nothing outside this file, `scratch/gaga-chart/` and this report was edited.

**ShimuraThm54.** The same restatement does **not** settle `ShimuraThm54`'s step (§6). The idea transfers, but that
leaf is stated over Mathlib's Weierstrass points, which have no analytic structure in Lean. Also, its predicate
`IsAnalyticIso` has no derivative clause to feed the inverse function theorem.

## 1. The new leaf (verbatim; namespace `GAGAAn`, `open UnifPrinted UnifTopology`)

```lean
def IsAnStr (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ) [TopologicalSpace (CPt X)]
    [ChartedSpace (Fin n → ℂ) (CPt X)] : Prop :=
  IsManifold 𝓘(ℂ, Fin n → ℂ) ω (CPt X) ∧
  (∀ (U : X.left.Opens) (f : Γ(X.left, U)),
    ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω (XevalAt X U f) {P | XPtIn X P U}) ∧
  (∀ P : CPt X, ∃ (U : X.left.Opens) (f : Fin n → Γ(X.left, U)), XPtIn X P U ∧
    IsLocalDiffeomorphAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω (fun Q i => XevalAt X U (f i) Q) P)

def GAGAChart : Prop :=
  ∀ (A B : AbVar ℂ) (n m : ℕ),
    letI := analyticTopology A.X
    letI := analyticTopology B.X
    ∀ (_ : ChartedSpace (Fin n → ℂ) (CPt A.X)) (_ : ChartedSpace (Fin m → ℂ) (CPt B.X)),
      IsAnStr A.X n → IsAnStr B.X m →
      ∀ F : CPt A.X → CPt B.X, ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ) ω F →
        ∃ f : A.X ⟶ B.X, ∀ P, F P = P ≫ f
```

Every object is concrete:
- `CPt`, `XPtIn` and `XevalAt` are unif-printed's `ℂ`-points, membership and evaluation.
- `analyticTopology` is unif-topology's topology of `X^an`. unif-topology proved it equal to the classical topology.
- `IsManifold`, `ContMDiff`, `ContMDiffOn` and `IsLocalDiffeomorphAt` are Mathlib's.
- `f : A.X ⟶ B.X` is a morphism of `ℂ`-schemes.

`IsAnStr` is the conjunction of the three clauses of `UnifTopology.SmoothComplexManifoldAn`, word for word. It is a
predicate on genuine data: a topology and an atlas.

**`IsAnStr` is the complex structure of `X^an`, and the leaf does not depend on the choice of charts.** Both claims
are proved in Lean:
- `contMDiff_id_of_isAnStr`: if every `U(ℂ)` is open, two atlases on `X(ℂ)` that both satisfy `IsAnStr` make the
  identity holomorphic in both directions. So they have the same holomorphic maps.
- `gagaChart_of_some : GAGAChartSome → GAGAChart`: GAGA for one choice of `IsAnStr` charts on `A(ℂ)` and `B(ℂ)`
  (for instance the atlases of `A^an` and `B^an`) gives the leaf for every choice.
- `IsAnStr` charts exist, so the leaf is not vacuous. They come from sga1-etale's étale atlas, through
  `SmoothComplexManifoldAn` (`isAnStr_of_etale`). They also come from any uniformization, through
  `exists_isAnStr_of_unif` (§2).

## 2. Glue proved (all VERIFIED, compiled; standard axioms)

| theorem | content | method |
| --- | --- | --- |
| `contMDiffAt_of_regular` | a map `G : M → X(ℂ)`, continuous at `x`, with every regular function `∘ G` holomorphic at `x`, is holomorphic at `x` for any `IsAnStr` atlas | the regular local coordinates of `IsAnStr` (`IsLocalDiffeomorphAt.contMDiffAt_localInverse`, `localInverse_eventuallyEq_left`), as in unif-printed's `contMDiff_comp` |
| `continuous_analyticHom` | `IsAnalyticHom ψ` implies `ψ` continuous into the classical topology | `continuous_generateFrom_iff`. The preimage of a basic set is `cDom ψ V ∩ (s ∘ ψ)⁻¹(ball)` |
| `continuousAt_symm`, `continuous_symm` | `φ⁻¹` is continuous for a uniformization | clause (iii) (`open_map`), and basic opens `isOpen_basic` |
| `gagaMorphism_of_chart_core` | `GAGAMorphism` from `UniformizationLeafAll`, `IsAnStrExists` and `GAGAChart` | see below |
| `RChart`, `rChartedSpace`, `isManifold_rChart`, `contMDiffOn_xevalAt_rChart`, `isAnStr_rChart` | a covering family of charts `Q ↦ (fᵢ(Q))` by regular functions, in which regular functions are analytic, gives an `IsAnStr` atlas | the pattern of sga1-etale's `chartedSpaceOf`, `isManifold_of`, `contMDiffOn_xevalAt` and `chartDiffeo`, with the analytic representation as a field of the chart |
| `continuousOn_xevalAt`, `uPt`, `continuous_uPt`, `uPt_image_eq` | regular functions are continuous on `U(ℂ)`; `v ↦ φ(proj v)` is continuous; `φ(proj S) = (φ⁻¹)⁻¹(proj S)` | basic opens; clause (i); algebra of `AddEquiv` |
| `exists_rChart` | from a uniformization, a regular chart at every point of `A(ℂ)` | see below |
| `exists_isAnStr_of_unif` | `IsAnStr` charts on `A(ℂ)` from a uniformization | `exists_rChart`, `isAnStr_rChart`, `classicalTopology_eq_analyticTopology` |
| `gagaMorphism_of_gagaChart` | **main theorem** | `gagaMorphism_of_chart_core`, with the charts from `exists_isAnStr_of_unif` applied to `uniformizationLeafAll` |
| `gagaMorphism_of_chart`, `gagaMorphism_of_chart_etale` | variants that take the charts from `SmoothComplexManifoldAn`, or from sga1-etale's `SGA1_XII_3_1_Etale` | `gagaMorphism_of_chart_core` |
| `contMDiff_id_of_isAnStr`, `GAGAChartSome`, `gagaChart_of_some`, `isAnStr_of_etale` | uniqueness and existence of the structure (§1) | `contMDiffAt_of_regular`; `ContMDiff.comp`; `smoothComplexManifoldAn_of_etale` |

**The core argument (`gagaMorphism_of_chart_core`).** We are given:
- a strong uniformization `φ` of `A` (converted to bp-analytic's form by `bp_of_isStrongUnif`);
- an analytic homomorphism `ψ : ℂ^g → B(ℂ)` that kills `Λ`;
- `IsAnStr` charts on `A(ℂ)` and `B(ℂ)`.

Define `F : A(ℂ) → B(ℂ)` by `F P = ψ (out (φ⁻¹ P))`. Then `F (φ (proj v)) = ψ v`, because `ψ` is a homomorphism
that kills `Λ`.

Fix `P₀ = φ (proj v₀)`. Clause (ii) of the uniformization gives regular `f₁, …, f_g` on `U ∋ P₀`. Set `Θ = (fᵢ)` and
`G = Θ ∘ φ ∘ proj`. Then `G` is analytic near `v₀` (clause (i)), and its derivative at `v₀` is invertible.
Mathlib's analytic inverse function theorem gives a local inverse `L`, analytic at `G v₀`. The proof has four steps:
1. **Local form of `F`.** Near `P₀`, `F = ψ ∘ L ∘ Θ`. This uses the continuity of `φ⁻¹`, the fact that `proj` is an
   open map, and `L (G v) = v`.
2. **Holomorphy into `B(ℂ)`.** By `contMDiffAt_of_regular` for the target, it suffices that `F` is continuous at
   `P₀` and that `s ∘ F` is holomorphic for every regular `s` on `B`.
3. **Analyticity of `s ∘ ψ`.** Write `ψ = φ_B ∘ proj ∘ D`, with `D` linear. Here `φ_B` comes from
   `uniformizationLeafAll`, and `D` from homlattice's `exists_complexLinear_of_analytic_strong`. Then `s ∘ ψ` is
   analytic by clause (i) for `B`. `IsAnalyticHom` only gives complex differentiability, and Mathlib has Osgood's
   lemma only in one variable, so this route through `φ_B` is needed.
4. **Holomorphy of `Θ`.** `Θ` is holomorphic for the `IsAnStr` atlas of `A`.

So `F` is `ContMDiff ω`. `GAGAChart` then gives `f`, and `ψ z = F (φ (proj z)) = φ (proj z) ≫ f`.

**The charts from a uniformization (`exists_rChart`).** At `P₀`, choose an open `S ∋ v₀` with three properties:
- `S` lies in the source of the inverse function theorem's local homeomorphism `h` of `G`;
- `S` lies in the domain where `G` is analytic;
- `dG` is invertible on `S` (`ContinuousLinearMap.isOpen_setOfPred_isInvertible`).

The chart is `Q ↦ Θ Q` on `φ(proj S)`, with inverse `w ↦ φ (proj (h⁻¹ w))` on `h(S)`. Its source is open because
`φ⁻¹` is continuous. A regular function in this chart is `(s ∘ φ ∘ proj) ∘ h⁻¹`. That composite is analytic at every
point of `h(S)`: `h⁻¹` is analytic there by `OpenPartialHomeomorph.contDiffAt_symm` (since `dG` is invertible), and
`s ∘ φ ∘ proj` is analytic by clause (i).

## 3. Rating of the new leaf

| leaf | source | rating |
| --- | --- | --- |
| `GAGAAn.GAGAChart` | Serre, *Géométrie algébrique et géométrie analytique*, Ann. Inst. Fourier 6 (1956): every analytic morphism between projective varieties is algebraic (abelian varieties are projective). SGA 1 (LNM 224), Exp. XII, Thm. 4.4 and its corollary on morphisms: for `X` proper over `ℂ`, `Hom(X, Y) → Hom(X^an, Y^an)` is bijective. Section and statement numbers from memory, **UNVERIFIED**. kinds.tsv's re-rating on `wip/leaf-fold32` also names SGA 1 XII 4.4 for proper `X`. | **printed form, special case** |

**Why printed form.** The print says: a morphism of analytic spaces `A^an → B^an` is `f^an` for a unique morphism
`f : A → B`. The leaf is that statement in the special case of abelian varieties, without uniqueness. The reading
from the print to the leaf has three steps:
1. **Points and topology.** The underlying space of `X^an` is `X(ℂ)` with the analytic topology, which is
   `analyticTopology` (unif-topology, proved equal to the glued affine topology). The map underlying `f^an` is
   `P ↦ P ≫ f`.
2. **The complex structure.** `A` is smooth, so `A^an` is a complex manifold. Its atlas satisfies `IsAnStr`:
   regular functions are holomorphic, because `X^an → X` is a morphism of ringed spaces; and local parameters are
   holomorphic coordinates. Sources: SGA 1 XII 1.1, 3.1; Shafarevich, *BAG 2*, VII §1.1.

   This is the printed content of `SmoothComplexManifoldAn`, which unif-topology rates printed form and sga1-etale
   proves from `SGA1_XII_3_1_Etale`. The leaf quantifies over all `IsAnStr` atlases. That adds nothing, by
   `contMDiff_id_of_isAnStr` and `gagaChart_of_some` (Lean). So "`ContMDiff ω` in `IsAnStr` charts" is exactly
   "holomorphic for `A^an` and `B^an`".
3. **Holomorphic maps are morphisms.** For complex manifolds, a morphism of analytic spaces (of `ℂ`-ringed spaces)
   is a holomorphic map in charts. This holds by definition of the structure sheaf (Grauert–Remmert, *Coherent
   analytic sheaves*, Ch. 1; locator UNVERIFIED).

None of these steps inverts a map, so the holomorphic inverse function theorem is no longer part of the reading.
It sits in the glue, proved twice in Lean (§2). The previous form needed it to go from `IsStrongUnif`/`IsAnalyticHom`
to "a holomorphic map `A^an → B^an`".

**Special-case remarks.**
- Serre's GAGA is for projective varieties, and abelian varieties are projective (Mumford §6, a theorem). SGA 1's
  form for proper `X` applies directly.
- The leaf asks `F` to be holomorphic on all of `A(ℂ)` and concludes only existence. Both choices make it weaker
  than the print.
- The leaf does not require `F` to be a homomorphism. The print does not either.

**Statement check.** These items should be checked against the print:
- the numbering "SGA 1 XII 4.4" and its corollary on morphisms (UNVERIFIED);
- the GAGA section that treats morphisms (UNVERIFIED; I believe it is a corollary of the comparison theorem, through
  graphs).

**Proposed row for `docs/research/locators.md`** (not added, since that file belongs to other tasks):
`GAGAChart`: Serre, GAGA (1956), the proposition on morphisms of projective varieties; SGA 1 Exp. XII, Thm. 4.4 /
Cor. 4.5 (proper `X`). Special case: abelian varieties, uniqueness dropped. UNVERIFIED.

## 4. `#discharges` (VERIFIED)

`lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` succeeded (12,994 jobs). Then
`lake env lean scratch/gaga-chart/DischargesCheck.lean`, with full output in `scratch/gaga-chart/discharges.txt`:

```
DISCHARGES [OpenTextbookLeaves11.gagaMorphism] by GAGAAn.gagaMorphism_of_gagaChart
  still assumes: [BPAnalytic.Uniformization.UniformizationLeafAll, GAGAAn.GAGAChart]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves11.gagaMorphism] by GAGAAn.gagaMorphism_of_chart_etale
  still assumes: [BPAnalytic.Uniformization.UniformizationLeafAll, SGA1Etale.SGA1_XII_3_1_Etale, GAGAAn.GAGAChart]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves11.gagaMorphism] by GAGAAn.gagaMorphism_of_chart
  still assumes: [BPAnalytic.Uniformization.UniformizationLeafAll,
 UnifTopology.SmoothComplexManifoldAn,
 GAGAAn.GAGAChart]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves11.gagaMorphism] by GAGAAn.gagaMorphism_of_chart_core
  still assumes: [BPAnalytic.Uniformization.UniformizationLeafAll, GAGAAn.IsAnStrExists, GAGAAn.GAGAChart]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 63 open hypotheses, 1952 theorems checked, 15 discharge one
```

The output also lists the earlier contributions' rows (unif-printed, unif-topology, sga1-etale and others), because
their modules are imported. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each of:
`gagaMorphism_of_gagaChart`, `gagaMorphism_of_chart`, `gagaMorphism_of_chart_etale`, `gagaMorphism_of_chart_core`,
`exists_isAnStr_of_unif`, `exists_rChart`, `contMDiff_id_of_isAnStr`, `gagaChart_of_some` and
`contMDiffAt_of_regular`.

## 5. Autofold spec (VERIFIED dry run)

`scratch/gaga-chart/autofold.json` discharges `gagaMorphism` by

```
_root_.GAGAAn.gagaMorphism_of_gagaChart {n}.uniformizationLeafAll {n}.gagaChart
```

It adds the leaf `gagaChart : _root_.GAGAAn.GAGAChart` to the textbook bundle, with kind `published` and flag
`unread: new printed leaf, no reading recorded; locator UNVERIFIED`. The import is
`ZInQKernel.Contrib.OneProof.GAGAChart`.

`python3 scripts/one_proof/autofold.py scratch/gaga-chart/autofold.json --dry-run` exits 0 and prints "strict
count: 46/10 on 56 -> 46/10 on 56; strictest 45/11 -> 45/11". The dry-run module minus its first line is
`scratch/gaga-chart/FoldDryRun.lean`. It compiles, and `HDec.HSyn.sixContactMin_of_open30` has axioms
`[propext, Classical.choice, Quot.sound]`.

**Count.** The count is neutral at this base because this base's `kinds.tsv` still rates `gagaMorphism` LEAF.
Against the 11-16 dictionary re-rating on `wip/leaf-fold32` (`gagaMorphism` `consequence`, GLUE), the fold is
**−1 GLUE**: one GLUE field is replaced by one printed leaf.

**Fold order.**
- If unif-printed's, unif-topology's or sga1-etale's fold lands first, `uniformizationLeafAll` leaves the bundle.
  Its proof term then goes in its place. For sga1-etale's fold:
  ```
  _root_.GAGAAn.gagaMorphism_of_gagaChart (_root_.SGA1Etale.uniformizationLeafAll_of_etale
    {n}.mumfordComplexTorus {n}.sga1_XII_3_1_Etale {n}.properCompactAn {n}.connectedPreconnectedAn) {n}.gagaChart
  ```
- The variant `gagaMorphism_of_chart_etale` uses `SGA1_XII_3_1_Etale` in place of the uniformization charts. It is
  not needed: `gagaMorphism_of_gagaChart` takes no leaf beyond `GAGAChart`.

## 6. Does the same restatement settle `ShimuraThm54`'s step?

**No, not as it stands.** This is read from `origin/wip/hcm-g1` (`ZInQKernel/Contrib/OneProof/ShimuraMainCMG1.lean`
and `docs/research/hcm-g1.md`); VERIFIED (read).

The predicate `HcmG1.IsAnalyticIso L W ξ` asks three things of `ξ : ℂ →+ W.toAffine.Point`:
- `ξ` is surjective;
- its kernel is `L`;
- its Weierstrass coordinates are holomorphic off `L`.

The print's hypothesis is an analytic isomorphism `ℂ/𝔞 → E(ℂ)`. Going from the predicate to the print needs two
facts. First, the induced map is holomorphic at `L` (by translation). Second, its inverse is holomorphic. The
dictionary pass flagged the second as the same inverse-function-theorem step as `gagaMorphism`'s. The fix here does
not carry over directly, for two reasons:
1. **Different objects.** `ShimuraThm54` is stated over Mathlib's `WeierstrassCurve.Affine.Point`, not over the
   `ℂ`-points of a scheme. Neither Mathlib nor the repository has `analyticTopology`, an atlas, or `IsAnStr` there.
   A chart-form hypothesis ("`ξ` is biholomorphic for the Riemann surface `E(ℂ)`") first needs a complex structure
   on `W(ℂ)`. That would mean charts `x` or `y` at affine points and `x/y` at `O`, or restating the leaf over the
   projective scheme of `W` and then using unif-topology's objects.
2. **No derivative clause.** Here the inverse function theorem is fed by clause (ii) of `IsStrongUnif`, which gives
   regular coordinates with invertible derivative. `IsAnalyticIso` has no such clause. A consumer that builds `ξ`
   from `(℘, ℘'/2)` (hcm-g1's `wHom`) would have to prove the immersion property itself: `℘'` and `℘''` do not
   vanish together (`℘''(ω/2) = 2(eᵢ−eⱼ)(eᵢ−eₖ) ≠ 0`), and the chart `x/y` at `0` has derivative `≠ 0`. Mathlib's
   one-variable fact "injective holomorphic implies nonzero derivative" would be an alternative; I have not checked
   whether Mathlib has it.

**Suggested correction (SPECULATIVE, not built).** Add a coordinates clause to `IsAnalyticIso`, analogous to
`IsStrongUnif.coords`:
- at each `z ∉ L`, `(X', Y')(z) ≠ 0`;
- near `L`, `X/Y` extends holomorphically with nonzero derivative.

With that clause, the hypothesis is the print's analytic isomorphism after the inverse function theorem in Lean, as
here. The consumer then owes the `℘''` computation above. This is a separate task.

## 7. Files

- `ZInQKernel/Contrib/OneProof/GAGAChart.lean`: the contribution.
- `scratch/gaga-chart/`:
  - `A.lean`: first version (charts from `SmoothComplexManifoldAn`);
  - `B.lean`: regular charts and charts from a uniformization;
  - `C.lean`: copy of the module;
  - `D.lean`: `gagaChart_of_some`;
  - `DischargesCheck.lean` with `discharges.txt`, `autofold.json`, `autofold-dryrun.txt`, `FoldDryRun.lean`;
  - `log.md`.
- Build note: the build tree was copied from `~/dzq-wt/nv-local` (its `.lake/build` and `lean/.lake/build`). That
  tree differs from this base only in contribution files.
