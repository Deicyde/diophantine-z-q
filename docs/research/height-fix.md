# height-fix: Bost and Gaudron–Rémond over a sound printed stable height

Task height-fix, 2026-11-16/17. Base: wip/height-dict 15cc5a60, with origin/main (0caafe66) merged, and
origin/wip/dict-models (ca225d00) merged for its `k(s)` semistability and the ascent to `k̄`. Model work only; no
human has reviewed it. There is no network here, so every locator below is recalled and marked UNVERIFIED unless a
file in the repository records a reading.

Marks: **VERIFIED** (compiled, or read in a file), **STANDARD** (published, with a reference), **SPECULATIVE**
(my argument), **UNVERIFIED** (a theorem number recalled from memory).

## 1. Result

**Items (1) and (2) of the review are closed in Lean. Item (3) is closed in the direction the print needs. One
glue Prop remains, for the opposite direction.** Everything below compiles with the standard axioms (VERIFIED,
§6), in a new file `ZInQKernel/Contrib/OneProof/PrintedStableHeight.lean` (namespace `ZInQ.HeightFix`).

The two new leaves, `BostLowerBoundPrinted` and `GaudronRemondThm14Printed`, are the old rows with
`IsStableFaltingsHeight` replaced by `ZInQ.HeightFix.IsPrintedStableHeight`. That definition changes three
things:

1. **Soundness (item 1).** The archimedean metric is `IsPrintedMetricSq 𝒢 τ η r`: the measure `(i/2)^g η ∧ η̄`
   on `A_τ(ℂ)` *exists*, and every such measure has total mass `r`.
   - Existence is proved for every group model (Néron or not), every `τ` and every `η ≠ 0`
     (`existsUnique_isPrintedMetricSq`, from T35). So `r` is well defined, and there is no case in which every
     `r` passes.
   - If existence failed, no `r` would pass, so the leaf could only become weaker, never false.
2. **R3 (item 2) is now a definition plus proved lemmas.**
   - The definition: `IsFormMeasure` says the measure has the density of `(i/2)^g η ∧ η̄` at every point, in
     algebraic coordinates translated to that point. Invariance of the measure is not assumed.
   - Proved lemmas, all VERIFIED:
     - two finite measures with the same local densities are equal (`eq_of_density`);
     - hence the measure is left-invariant (`isMulLeftInvariant_of_densAt`, `isFormMeasure_iff`);
     - the translated coordinates are charts (`exists_chart`, the inverse function theorem) and holomorphic
       coordinates (`chartAt_comp_hasStrictFDerivAt`);
     - Haar uniqueness identifies the mass as the kernel's `|c_τ η|² covol(Λ_τ)` (`isPrintedMetricSq_iff`).
3. **Semistability (item 3).** `IsSemistableRes` is SGA 7 IX Déf. 2.2/3.2 read over the residue field `k(𝔭)`:
   dict-models' `HasSemiAbelianIdCompTorus`, with a torus that need not split over `k(𝔭)`.
   - The ascent `k(𝔭) ⇒ k̄` to the kernel's geometric form is proved (`isSemistable_of_res`, from Stacks 04KV).
   - The descent `k̄ ⇒ k(𝔭)` is the new glue `SemiAbelianDescendsPerfect` (§4).

Both fields are proved from the new leaves:

```lean
theorem ZInQ.HeightFix.bostLowerBound_of_printed (hB : BostLowerBoundPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hMT : AvSplit.MumfordTorsionAlgClosed)
    (hD : SemiAbelianDescendsPerfect) : ZInQ.HeightSplit.BostLowerBound
theorem ZInQ.HeightFix.gaudronRemondThm14_of_printed (hGR : GaudronRemondThm14Printed)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hMT : AvSplit.MumfordTorsionAlgClosed)
    (hD : SemiAbelianDescendsPerfect) : ZInQ.HeightSplit.GaudronRemondThm14
theorem ZInQ.HeightFix.isPrintedStableHeight_iff (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hGC : AVGlue.GeomConnOfRationalPoint) (hD : SemiAbelianDescendsPerfect) [NumberField K]
    (A : PkgI3.AbVar K) (x : ℝ) : IsPrintedStableHeight A x ↔ IsStableFaltingsHeight A x
```

`NeronMetrizable` is no longer a hypothesis of the identification. It is proved from T35 inside the proof
(`neronMetrizable_of_t35`).

**Count.** The target was −2 GLUE against the re-rated base. The result is −1:

- two GLUE rows (`bostLowerBound` and `gaudronRemondThm14`, as re-rated by the review) become two printed
  leaves;
- one new glue row, `semiAbelianDescendsPerfect`, is added.

The −2 is reached if `SemiAbelianDescendsPerfect` is proved, or if SGA 7 IX turns out to print the criterion
"`G` is semi-abelian iff `G_k̄` is" (§4). Against this base's `kinds.tsv`, which still has both rows as LEAF,
the fold is +1. So the dry run needs `--allow-rise` (§6).

## 2. The definitions (Lean, verbatim up to docstrings)

```lean
noncomputable def chartAt (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (U : Fin g → 𝒢.G.left.Opens) (s : ∀ i, Γ(𝒢.G.left, U i)) (p : 𝒢.Pts τ) :
    𝒢.Pts τ → (Fin g → ℂ) :=
  fun q => coordMap 𝒢 τ U s (p⁻¹ * q)

def HasFormDensityAt (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (nu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) (p : 𝒢.Pts τ) : Prop :=
  letI := anTop 𝒢 τ
  letI := anBorel 𝒢 τ
  ∀ (U : Fin g → 𝒢.G.left.Opens) (hU : ∀ i, 𝒢.genericUnit ∈ U i) (s : ∀ i, Γ(𝒢.G.left, U i))
    (hm : ∀ i, 𝒢.G.left.presheaf.germ (U i) 𝒢.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk)
    (l : L), eta = l • 𝒢.wedge (fun i => ⟨_, hm i⟩) →
    ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 p, ∀ E ⊆ W, MeasurableSet E →
      |(nu E).toReal - ‖τ l‖ ^ 2 * (volume (chartAt 𝒢 τ U s p '' E)).toReal| ≤
        ε * (volume (chartAt 𝒢 τ U s p '' E)).toReal

def IsFormMeasure (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (nu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) : Prop :=
  @IsFiniteMeasure _ (anBorel 𝒢 τ) nu ∧ ∀ p, HasFormDensityAt 𝒢 τ nu eta p

def IsPrintedMetricSq (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (eta : 𝒢.hodgeSpace g) (r : ℝ) :
    Prop :=
  letI := anBorel 𝒢 τ
  (∃ nu : Measure (𝒢.Pts τ), IsFormMeasure 𝒢 τ nu eta) ∧
    ∀ nu : Measure (𝒢.Pts τ), IsFormMeasure 𝒢 τ nu eta → (nu univ).toReal = r

noncomputable def resFibre (𝒢 : GroupModel A L) (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] :
    Over (Spec (CommRingCat.of 𝔭.ResidueField)) :=
  (Over.pullback (sResP 𝔭)).obj 𝒢.G          -- sResP 𝔭 = Spec (𝓞_L → k(𝔭))

def IsSemistableRes (𝒢 : GroupModel A L) : Prop :=
  ∀ (𝔭 : Ideal (𝓞 L)) [𝔭.IsMaximal], HasSemiAbelianIdCompTorus (resFibre 𝒢 𝔭)

def IsPrintedStableHeight {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (𝒩 : GroupModel A L) (g : ℕ),
    𝒩.IsNeronModel ∧ IsSemistableRes 𝒩 ∧ A.dim = (g : WithBot ℕ∞) ∧
    ∃ eta ∈ printedDetLattice 𝒩 g, eta ≠ 0 ∧ secIndex (printedDetLattice 𝒩 g) eta ≠ 0 ∧
      ∃ r : (L →+* ℂ) → ℝ, (∀ τ, IsPrintedMetricSq 𝒩 τ eta (r τ)) ∧
        x = (Real.log (secIndex (printedDetLattice 𝒩 g) eta) -
          (1 / 2) * ∑ τ : L →+* ℂ, Real.log (r τ)) / Module.finrank ℚ L
```

The two leaves are verbatim the old rows over this definition:

- `BostLowerBoundPrinted`: `∀ K [NumberField K] A g, A.dim = g → ∀ x, IsPrintedStableHeight A x →
  −(g/2) log 2π ≤ x + (g/2) log π`.
- `GaudronRemondThm14Printed`: the `κ` bound with `IsPrintedStableHeight`.

Every object is Mathlib's or the kernel's: `Measure`, `volume`, `IsFiniteMeasure`, `Ideal.ResidueField`,
`Over.pullback`, `anTop` (the kernel's analytic topology), `coordMap`, `wedge`, `hodgeSpace`, `secIndex`,
`IsNeronModel`. Two more are earlier contributions: `printedDetLattice` (height-dict, `ω = ⋀^g Γ(S, e*Ω¹)` from
Kähler differentials) and `HasSemiAbelianIdCompTorus` (dict-models).

**Reading `HasFormDensityAt`.**

- `F = (f₁, …, f_g)` are regular functions vanishing at the origin, with `η = l·df₁ ∧ ⋯ ∧ df_g` at the origin.
- The invariant form `η̃` with `η̃(1) = η` is, by definition of invariance, `L_{p⁻¹}^* η̃(1)` at `p`. In the
  chart `q ↦ F(p⁻¹q)` its coefficient at `p` is therefore `l`.
- So `(i/2)^g η̃ ∧ η̄̃` has density `|τ(l)|²` there, relative to Lebesgue measure `dx₁dy₁⋯dx_gdy_g`, because
  `(i/2) dz ∧ dz̄ = dx ∧ dy`.
- The definition asks this at every point. It therefore defines the measure of the density chart by chart, the
  textbook definition of `∫_X` of a top-degree density on a manifold.
- The density is asked at the centre of each chart (with the `ε`-estimate), not on the whole chart domain.
  The uniqueness lemma `eq_of_density` shows that this pins the measure down: two finite measures with these
  densities everywhere coincide.

## 3. What is proved (all VERIFIED: compiled, standard axioms)

| lemma | statement | role |
| --- | --- | --- |
| `eq_of_density` | On a compact space, two finite measures `ν₁, ν₂` with `|νᵢ(E) − c·v_p(E)| ≤ ε v_p(E)` for all measurable `E` near each `p` (with `c > 0`) are equal | uniqueness of the integral; no Vitali covering is needed (finite subcover + induction) |
| `densAt_map`, `densAt_of_invariant` | translating a measure translates its densities; an invariant measure with density `c` at `1` has it everywhere | invariance of `η` ⇔ chart at `p` = translate of chart at `1` |
| `eq_of_densAt`, `isMulLeftInvariant_of_densAt` | measures with density `c > 0` everywhere coincide, hence are left-invariant | **invariance proved**, not assumed |
| `metrized_setup` | for a metrized model: `A_τ(ℂ)` is a compact topological group; `η ≠ 0` has a representation `l·df` with `τ l ≠ 0` | |
| `isFormMeasure_iff` | `IsFormMeasure ν η ↔` `ν` finite, left-invariant and normalized at `1` (height-dict's `IsNormalizedBy`) | height-dict's characterization is now a **theorem** |
| `isPrintedMetricSq_iff` | for `η ≠ 0`: `IsPrintedMetricSq M.model τ η r ↔ r = torusMetricSq (periods τ) (coeff τ η)` | **Haar uniqueness** (through height-dict's `volume_eq_of_normalized`) |
| `exists_chart` | for `η = l·df ≠ 0` and every `p`, `chartAt … p` agrees on an open neighbourhood of `p` with an `OpenPartialHomeomorph` onto an open subset of `ℂ^g` | **charts** (inverse function theorem `HasStrictFDerivAt.toOpenPartialHomeomorph`; `Φ` injective and open on a small ball) |
| `chartAt_comp`, `chartAt_comp_hasStrictFDerivAt` | in the coordinates of any analytic uniformization, `chartAt (Φ z₀) ∘ Φ = (F ∘ Φ)(· − z₀)`, strictly differentiable at `z₀` with derivative of determinant `jacDet Φ f` | the charts are holomorphic coordinates of `A^an ≅ ℂ^g/Λ` |
| `exists_metrized`, `existsUnique_isPrintedMetricSq`, `exists_isFormMeasure` | (T35) every group model of dimension `g = dim A` is metrizable; for every `τ` and `η ≠ 0` there is exactly one `r` with `IsPrintedMetricSq 𝒢 τ η r` | **existence for every case** the leaves quantify over |
| `isSemistable_of_res` | `IsSemistableRes 𝒢 → IsSemistable 𝒢` (Stacks 04KV, dict-models' `hasSemiAbelian_pullback_bar`, `pbCompIso`) | ascent `k(𝔭) ⇒ k̄` |
| `perfectField_residueField`, `isSemistableRes_of_geom` | residue fields of `𝓞_L` are finite, hence perfect; with the glue, `IsSemistable 𝒢 → IsSemistableRes 𝒢` | descent `k̄ ⇒ k(𝔭)`, through the glue |
| `isPrintedStableHeight_of` | (T35, glue) kernel height ⇒ printed height | consumer direction |
| `isStableFaltingsHeight_of_printed` | (T35, 04KV) printed height ⇒ kernel height; no `NeronMetrizable` hypothesis | faithfulness |
| `isPrintedStableHeight_iff` | the two coincide | |
| `bostLowerBound_of_printed`, `gaudronRemondThm14_of_printed` | the two fields | |
| `bostLowerBoundPrinted_of_kernel`, `gaudronRemondThm14Printed_of_kernel` | (T35, 04KV) the old rows imply the new leaves | the new leaves are never stronger than the old rows |

## 4. The remaining glue: `SemiAbelianDescendsPerfect`

```lean
def SemiAbelianDescendsPerfect : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom],
    letI : GrpObj ((Over.pullback (sφ (φbar k))).obj G) := Functor.grpObjObj
    HasSemiAbelianIdentityComponent ((Over.pullback (sφ (φbar k))).obj G) →
      HasSemiAbelianIdCompTorus G
```

**Why it is needed.**

- The fields are stated over the kernel's `IsStableFaltingsHeight`, whose semistability is read on the geometric
  fibre `𝒩 ×_{𝓞_L} κ̄(𝔭)`.
- The leaves have semistability in hypothesis position. To apply them to a kernel height `x`, `x` must be shown to
  be a printed height. That needs `k(𝔭)`-semistability of some semistable Néron model with height `x`.
- So the consumer direction is the *descent* `k̄ ⇒ k(𝔭)`.
- dict-models' step (`RaynaudSemistableOr.lean`) is the *ascent* `k(𝔭) ⇒ k̄`. It gives the other direction
  (printed ⇒ kernel), which is used here for `isStableFaltingsHeight_of_printed` and the iff, but not by the
  fields.

**Why it is true** (STANDARD argument, SPECULATIVE as a Lean statement; locators UNVERIFIED):

1. `G⁰` is open, with a rational point, and is geometrically connected (Stacks 04KV). So `(G⁰)_{k̄} = (G_{k̄})⁰`.
   That group is an extension of an abelian variety by a torus, hence smooth and commutative, so `G⁰` is smooth.
2. Chevalley's theorem over a perfect field gives `1 → H → G⁰ → B → 1` over `k`, with `H` smooth connected affine
   and `B` an abelian variety, compatible with base change (Conrad, J. Ramanujan Math. Soc. 17 (2002), Thm 1.1).
3. By uniqueness of the decomposition over `k̄`, `H_{k̄}` is the torus of `(G_{k̄})⁰`. So `H` is a torus, which
   is the `k(𝔭)` form.

**Why it is not proved here.**

- It needs Galois descent of the abelian quotient and of `π` from `k̄` to `k`, or Chevalley's theorem. Neither is
  in Mathlib 4.35 or in the tree.
- No route avoids it. Every leaf in the bundles that concludes semistability does so on a separably closed
  residue field (strict henselization) or on `κ̄`, and over a finite field passing from those to `k(𝔭)` is this
  same descent.
- It complements unipotent-b's `UnipotentForward.SemiAbelianDescendsSepClosed`, which handles separably closed,
  possibly imperfect, residue fields.

**How it could become a leaf.** I recall (UNVERIFIED, could not be checked offline) that SGA 7 IX §2 remarks that
semi-abelianness of a smooth connected commutative group over a field can be tested over `k̄`. If the print says
so, `SemiAbelianDescendsPerfect` is a consequence of that remark plus 04KV. A statement check of SGA 7 IX 2.1-2.2
decides this. If the remark is printed, the glue can be re-rated "pending reading", and the fold reaches −2.

## 5. Leaves, glue and ratings

| new row | bundle | kind | rating | reason |
| --- | --- | --- | --- | --- |
| `bostLowerBoundPrinted` (`ZInQ.HeightFix.BostLowerBoundPrinted`) | research (replaces `bostLowerBound`) | published | **printed form** | Bost's bound verbatim over a stable height built as the print builds it: Néron model, `k(𝔭)`-semistability as in SGA 7, `ω = ⋀^g Γ(S, e*Ω¹)`, metric `(i/2)^g ∫ η ∧ η̄` defined chart by chart and required to exist. Remaining caveats are those of the old row: display UNVERIFIED, and Deligne's normalization `h_D = h_F + (g/2) log π` |
| `gaudronRemondThm14Printed` (`ZInQ.HeightFix.GaudronRemondThm14Printed`) | research (replaces `gaudronRemondThm14`) | published | **printed form** | same definition, Faltings' original normalization `(i/2)^g` (Thm 1.4 p. 2060, read by the locator audit) |
| `semiAbelianDescendsPerfect` (`ZInQ.HeightFix.SemiAbelianDescendsPerfect`) | research | project glue | **GLUE** (not printed form) | descent of semi-abelian identity components from `k̄` to a perfect field, §4. It becomes a consequence of a printed remark if SGA 7 IX prints the `k̄` criterion |

Definition-level readings that remain (none is a theorem step):

- **R1.** Stalks of `Ω_{𝒩/S}` are Kähler differentials, and global sections of a lattice are the intersection
  of its stalks. Unchanged from height-dict.
- **R2.** `A_τ(ℂ)` with its analytic topology is `(𝒢(ℂ)_τ, anTop)`. Unchanged.
- **R3 is no longer a reading.** The integral is defined chart by chart, and its identification with the
  normalized Haar mass is proved (§3).
- **R4.** "Semistable reduction at `𝔭`" is defined in SGA 7 through the Néron model over the local ring
  `𝓞_{L,𝔭}`, while `IsSemistableRes` reads the fibre of the global Néron model at `𝔭`. These agree because Néron
  models localize (BLR §1.2 Prop. 4, the chain's printed leaf `blr_1_2_4`). The kernel's `IsSemistable` uses the
  same convention, and the review did not object to it.

Proposed `docs/research/locators.md` rows (not added, since locators.md is a shared note): the two leaves under
the same rows as `bostLowerBound` and `gaudronRemondThm14`. For the glue: SGA 7 I Exp. IX §2.1-2.2 (the `k̄`
criterion, to read) and Conrad 2002 Thm 1.1 (Chevalley over a perfect field).

## 6. Checks (all VERIFIED)

- `lake build ZInQKernel.Contrib.OneProof.PrintedStableHeight` succeeds. The file is 49 KB, imports
  `ZInQKernel.Contrib.OneProof.HeightDictionary` and `ZInQKernel.Contrib.OneProof.RaynaudSemistableOr`, and has no
  code that runs at build time.
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` succeeds (13698 jobs).
- `#discharges` (`scratch/height-fix/DischargesCheck.lean`; full output in `scratch/height-fix/discharges.txt`):

```
DISCHARGES [OpenResearchLeaves26.bostLowerBound] by ZInQ.HeightFix.bostLowerBound_of_printed
  still assumes: [ZInQ.HeightFix.BostLowerBoundPrinted,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 AvSplit.MumfordTorsionAlgClosed,
 ZInQ.HeightFix.SemiAbelianDescendsPerfect]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.gaudronRemondThm14] by ZInQ.HeightFix.gaudronRemondThm14_of_printed
  still assumes: [ZInQ.HeightFix.GaudronRemondThm14Printed,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 AvSplit.MumfordTorsionAlgClosed,
 ZInQ.HeightFix.SemiAbelianDescendsPerfect]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.javanpeykarBound] by ZInQ.HeightFix.javanpeykarBound_of_printed
DISCHARGES [OpenResearchLeaves26.pazukiCor13Upper] by ZInQ.HeightFix.pazukiCor13Upper_of_printed
#discharges: 56 open hypotheses, 3035 theorems checked, 18 discharge one
```

  The last two (optional, §7 of the file) assume their printed leaf, the same two textbook fields and the
  glue. The count of 18 also includes height-dict's and dict-models' theorems, which are in the build.
- **Autofold.** The spec is `scratch/height-fix/autofold.json`. It has two discharges:
  - `bostLowerBound` gets the new leaves `bostLowerBoundPrinted` (published, flag "locator UNVERIFIED (see the
    source)") and `semiAbelianDescendsPerfect` (project glue);
  - `gaudronRemondThm14` gets `gaudronRemondThm14Printed` (published, no flag, so the default "unread") and
    reuses `{n}.semiAbelianDescendsPerfect`.
- **Dry run on this base.** It reports `strict count: 34/11 on 45 -> 34/12 on 46; strictest 34/11 -> 34/12`
  and refuses without `--allow-rise`, because this base's `kinds.tsv` still rates both rows LEAF.
  - With `--allow-rise` it exits 0, and the module (`scratch/height-fix/FoldDryRun.lean`, the output without
    its first line) compiles; `HDec.HSyn.sixContactMin_of_open36` has the standard axioms.
  - On the re-rated base (both rows GLUE: 32/13) the same fold gives 34/12, i.e. −1 GLUE.

**Fold order.** This contribution imports dict-models' `RaynaudSemistableOr.lean`, so dict-models must be folded,
or at least its Contrib files merged, first. It replaces height-dict's spec (`scratch/height-dict/autofold.json`
and `autofold-all4.json`). Height-dict's `HeightDict.IsPrintedStableHeight` has the soundness defect and should
not be folded. Its lemmas (`isFaltingsMetricSq_of_metrized`, `exists_isNormalizedBy`, `TorusVolume`,
`Conormal`) are reused here.
