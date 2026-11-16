# faltings5-lower: the lower half of Faltings' Lemma 5, proved from the kernel's height

Task faltings5-lower, 2026-11-15, base fork main `9a100aa7` (leaf-fold22b), branch `wip/faltings5-lower`.

## Result

Contributor file `ZInQKernel/Contrib/OneProof/FaltingsLemma5Lower.lean` (namespace `GapHeight`), helpers in
`ZInQKernel/Contrib/OneProof/FaltingsLemma5Lower/` (13 files, about 110 KB in all, largest 16 KB). Built with
`lake build ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower` (VERIFIED, compiled; no `sorry`).

```lean
theorem GapHeight.faltingsLemma5Lower : ZInQ.HeightSplit.FaltingsLemma5Lower
```
```
'GapHeight.faltingsLemma5Lower' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**No hypotheses.** The semistability hypotheses of `FaltingsLemma5Lower` are not used, and the Néron property is
used only for `𝒩_B`, through the proved `CToPrinted.exists_extension`. (A first version used the bundle field
`milneIsogenyQuasiInverse` for the étaleness of `φ` at the origin; it was replaced by a proof of Cartier's argument,
`GapHeight.tangent_trivial` below.)

The statement (`ZInQKernel/OneProof/H/TailY.lean` L644, verbatim):
```lean
def FaltingsLemma5Lower : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (𝒩A : GroupModel A K) (𝒩B : GroupModel B K), 𝒩A.IsNeronModel → 𝒩B.IsNeronModel →
      IsSemistable 𝒩A → IsSemistable 𝒩B →
      ∀ x y : ℝ, 𝒩A.height = x → 𝒩B.height = y → -((1 / 2) * Real.log (isogDeg φ)) ≤ x - y
```

The other exported theorems (all with axioms `[propext, Classical.choice, Quot.sound]`, VERIFIED by
`scratch/faltings5-lower/Axioms.lean`):

```lean
-- Reduction.lean: the height inequality from three glue statements about the Néron extension f of φ
theorem GapHeight.faltingsLemma5Lower_of (h1 : IsogCotBijective) (h2 : IsogPtsSurjective)
    (h3 : IsogKerCard) : ZInQ.HeightSplit.FaltingsLemma5Lower
theorem GapHeight.faltingsLemma5Lower_of_cotBijective (h : IsogCotBijective) :
    ZInQ.HeightSplit.FaltingsLemma5Lower
-- the three glue statements, proved
theorem GapHeight.isogPtsSurjective : IsogPtsSurjective          -- Surj.lean
theorem GapHeight.isogKerCard : IsogKerCard                      -- Ker.lean
theorem GapHeight.isogCotBijective : IsogCotBijective             -- CotFinal.lean
-- TanFinite.lean: characteristic 0, tangent vectors killed by a finite homomorphism are trivial
theorem GapHeight.tangent_trivial {K : Type} [Field K] {A B : PkgI3.AbVar K} (φ : A.X ⟶ B.X)
    [IsMonHom φ] [IsFinite φ.left] [CharZero K] (v : ptR (K := K) (TrivSqZeroExt K K) ⟶ A.X)
    (hv : AtOrigin A v) (hvφ : v ≫ φ = 1) : v = 1
```
(`ptR`, `AtOrigin` are `ZInQ.Contrib.AbVarBC.Tangent`'s.)
with (Reduction.lean)
```lean
def IsogCotBijective : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (𝒩A : GroupModel A K) (𝒩B : GroupModel B K) (f : 𝒩A.G ⟶ 𝒩B.G) [IsMonHom f],
      CToPrinted.ExtendsIsogeny φ 𝒩A 𝒩B f → Function.Bijective (cotMap 𝒩A 𝒩B f)
def IsogPtsSurjective : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (𝒩A : GroupModel A K) (𝒩B : GroupModel B K) (f : 𝒩A.G ⟶ 𝒩B.G) [IsMonHom f],
      CToPrinted.ExtendsIsogeny φ 𝒩A 𝒩B f →
      ∀ τ : K →+* ℂ, Function.Surjective fun p : 𝒩A.Pts τ => p ≫ f
def IsogKerCard : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (𝒩A : GroupModel A K) (𝒩B : GroupModel B K) (f : 𝒩A.G ⟶ 𝒩B.G) [IsMonHom f],
      CToPrinted.ExtendsIsogeny φ 𝒩A 𝒩B f →
      ∀ τ : K →+* ℂ, Finite {p : 𝒩A.Pts τ // p ≫ f = 1} ∧
        Nat.card {p : 𝒩A.Pts τ // p ≫ f = 1} ≤ isogDeg φ
```
(`cotMap` is `GapHeight.cotMap`, H5Glue's `cotMap` for models of two different abelian varieties.)

The central analytic statement (Assembly.lean), for any number field `L`:
```lean
theorem GapHeight.height_le_of_metrized {g : ℕ} (M : MetrizedModel A L g) (𝒩 : GroupModel B L)
    (f : M.model.G ⟶ 𝒩.G) [IsMonHom f] (hcot : Function.Bijective (cotMap M.model 𝒩 f))
    (hsurj : ∀ τ : L →+* ℂ, Function.Surjective fun p : M.model.Pts τ => p ≫ f) (d : ℕ)
    (hker : ∀ τ : L →+* ℂ, Finite {p : M.model.Pts τ // p ≫ f = 1} ∧
      Nat.card {p : M.model.Pts τ // p ≫ f = 1} ≤ d) :
    𝒩.height ≤ ((M.hodge.modelHeight + (1 / 2) * Real.log d : ℝ) : EReal)
```

## `#discharges`

`scratch/faltings5-lower/Discharges.lean`, output saved as `scratch/faltings5-lower/discharges.txt` (VERIFIED, run):
```
DISCHARGES [OpenResearchLeaves21.gonzalezRotgerProp56X6] by GRCountX6.prop56X6_of_r5fpCount
  ... (the five discharges of contributions already in the tree, unchanged)
#discharges: 63 open hypotheses, 1806 theorems checked, 5 discharge one
```
As expected nothing new matches: `FaltingsLemma5Lower` is weaker than the field `faltingsLemma5Printed`
(`CToPrinted.FaltingsLemma5Printed`, the full identity), so this is a rerouting fold, not an autofold. No autofold
spec is written (there is no field whose statement is proved).

## The manual fold

Consumers of the field `faltingsLemma5Printed` at base `9a100aa7` (all `ZInQKernel/OneProof/H/`):

| file:line | what | live? |
| --- | --- | --- |
| TailZ23.lean:814 | `sixContactMin_of_open17` uses `(_root_.CToPrinted.faltingsLemma5BCLower_of_printed r.faltingsLemma5Printed)` | **the only live use** |
| TailZ19.lean:1898 | `researchLeaves11_of_open12` builds `faltingsLemma5BC := faltingsLemma5BC_of_printed r.faltingsLemma5Printed r.raynaudKernelBound` | not live |
| TailZ22.lean:309 | `researchLeaves12_of_open13`, copy `faltingsLemma5Printed := r.faltingsLemma5Printed` | not live |
| TailZ25.lean:123, TailZ26.lean:119, TailZ27.lean:112, TailZ28.lean:110, TailZ29.lean:107, TailZ33.lean:108, TailZ34.lean:102 | `openResearchLeavesN_of_OpenResearchLeavesN+1`, copy `faltingsLemma5Printed := n.faltingsLemma5Printed` | live, copies only |
| TailZ19.lean:1763 (`CToPrintedLeaves.faltings5`), 1864 (`OpenResearchLeaves12`), TailZ22.lean:202 (13), TailZ23.lean:659 (14), TailZ25.lean:59 (15), TailZ26.lean:55 (16), TailZ27.lean:49 (17), TailZ28.lean:49 (18), TailZ29.lean:49 (19), TailZ33.lean:48 (20), TailZ34.lean:45 (21) | field declarations | — |

Liveness was computed, not guessed: `scratch/faltings5-lower/LiveUses.lean` takes the dependency closure of
`ZInQ.OneProof.frozenTarget` (244 035 constants) and lists every constant whose name contains `altingsLemma5`. The
closure contains `CToPrinted.faltingsLemma5Lower_of_printed`, `CToPrinted.faltingsLemma5BCLower_of_printed`,
`ReductSplit.faltingsLemma5BCLower_final` and the projections `OpenResearchLeaves14..21.faltingsLemma5Printed`; it
contains neither `faltingsLemma5BC_of_printed` (TailZ19 L1898) nor `faltingsLemma5_of_printed`, nor any
`OpenResearchLeaves12/13` projection (VERIFIED). So nothing live needs the full identity.

**Replacement** (the only change of a term): at TailZ23.lean L813-814, in `sixContactMin_of_open17`
(`r : OpenResearchLeaves14`, `t : OpenTextbookLeaves10`, `l : OpenAddedLeaves12`), replace
```lean
    (_root_.CToPrinted.faltingsLemma5BCLower_of_printed r.faltingsLemma5Printed) hYu
```
by
```lean
    (_root_.ReductSplit.faltingsLemma5BCLower_final _root_.GapHeight.faltingsLemma5Lower) hYu
```
The module needs
`import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower`; that module imports only Mathlib, `TailY`, `TailZ19` (through
`Gen.lean`) and `ZInQKernel.Contrib.AbVarBC.KerUnit`, so no cycle with `TailZ20`+.

`scratch/faltings5-lower/FoldCheck.lean` (VERIFIED, compiled against the built `Main`) checks the hash-preserving
form of this fold: `sixContactMin_of_open17'` (the replacement above), copies `open18'` ... `open28'` of
`sixContactMin_of_open18` ... `_open28` (TailZ24 L835, TailZ25 L136, TailZ26 L192, TailZ27 L124, TailZ28 L123,
TailZ29 L120, TailZ30 L73, TailZ31 L69, TailZ32 L45, TailZ33 L121, TailZ34 L171) calling the primed predecessor, and
`frozenTarget'` (Main.lean L57-67 on `open28'`), with `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
The closure of `frozenTarget'` no longer contains `faltingsLemma5Lower_of_printed`,
`faltingsLemma5BCLower_of_printed` or `OpenResearchLeaves14.faltingsLemma5Printed`; the remaining
`OpenResearchLeaves15..21.faltingsLemma5Printed` occurrences are the copy assignments in the
`openResearchLeavesN_of_…` maps. The field is then "passed but never used", the sem-prune situation: the integrator
drops it from `OpenResearchLeaves14..21` and deletes the eight copy lines (TailZ25:123 ... TailZ34:102), as in
sem-prune/yu-prune.

**Counts** (OPEN.md at base: 56 H hypotheses; strict 45 published / 11 glue, 46/10 without the strictest flag;
kinds.tsv row 9: `faltingsLemma5Printed` published, LEAF in both columns). After the fold: 55 H hypotheses;
**strict 44 published / 11 glue (strictest), 45 / 10 without the strictest flag**; by kind published 47 → 46. No new
hypothesis, so neither GLUE count rises.

## Method

**Direction.** `GroupModel.height 𝒢 = ⨅ g (M : MetrizedModel A L g) (_ : M.model = 𝒢), M.hodge.modelHeight`
(`ZInQKernel/HDecomp/Faltings/Height.lean` L235). The lower half says `h(𝒩_B) ≤ h(𝒩_A) + ½ log deg φ`: an upper bound
of an infimum by an infimum, so it suffices to produce, for every metrization `M` of `𝒩_A`, one metrization `M'`
of `𝒩_B` with `h(M') ≤ h(M) + ½ log deg φ`. No independence of the metrization (`AnalyticUniformizationUnique`), no
product formula and no existence of metrizations (`AnalyticUniformizationExists`) is needed (VERIFIED: none is
used).

**The metrization `M'`** (`Assembly.lean`). Let `f : 𝒩_A → 𝒩_B` be the Néron extension of `φ`, `H = L ⊗ ⋀^g f^*`
(`hodgeMap`, the H5Glue construction copied for two abelian varieties in `Gen.lean`). If `f^*` is bijective on the
cotangent spaces at the origin, `H` is bijective, so `hodgeSpace 𝒩_B` is a line, and `H` maps `⋀^g ω_{𝒩_B}` into
`⋀^g ω_{𝒩_A}` (`hodgeMap_detLattice`), so `secIndex` can only go down. At each `τ : L → ℂ` the uniformization of
`𝒩_B` is `Φ_τ ≫ f`: a homomorphism, surjective if `f` is surjective on complex points, holomorphic on charts (pull
back the chart along `f`), with kernel `Λ'_τ = Φ_τ⁻¹(ker f(ℂ)) ⊇ Λ_τ` (`isogPeriods`); the coefficient map is
`coeff_τ ∘ H`, which matches `jacDet (Φ ≫ f)` by the chain rule (`jacDet_comp_genMap`). `[Λ'_τ : Λ_τ]` is the size
of the image of `Λ'_τ` in `𝒢(ℂ)`, at most `#ker f(ℂ)_τ` (`relIndex_isogPeriods`); a superlattice of finite index is
discrete and full (`Lattice.lean`), and `covol Λ_τ = [Λ'_τ : Λ_τ] · covol Λ'_τ` for any Haar measure on any
finite-dimensional real space (`covolume_eq_relIndex_mul`, from Mathlib's pi case
`ZLattice.covolume_div_covolume_eq_relIndex` and uniqueness of Haar measure). Faltings' formula `modelHeight_eq`
for a lattice vector `w` of `𝒩_B` and `Hw` of `𝒩_A`, summed over the `[L:ℚ]` embeddings, gives
`h(M') ≤ h(M) + ½ log d` (`modelHeight_isogHodge_le`).

**The three glue statements.**
* *Points* (`Transport.lean`). `theta`: points of a group model over `𝓞_K` with values in a `K`-scheme `T`
  (`(Over.map (Spec K → Spec 𝓞_K)).obj T ⟶ 𝒢.G`) are `T`-points of `A`, through `Over.mapPullbackAdj`, `gen` and the
  base change along `Spec K → Spec K`; multiplicative, natural in `T`, and compatible with `f` and `φ` by
  `ExtendsIsogeny`. So `ker f(ℂ)_τ ≃ {P : Spec ℂ → A over τ // P ≫ φ = 1}` (`kerEquiv`).
* *`IsogPtsSurjective`* (`Surj.lean`): the fibre `X ×_Y Spec ℂ` of the finite surjective `φ` is a nonempty finite
  `ℂ`-scheme; a closed point of it is a section (Mathlib's `pointOfClosedPoint`).
* *`IsogKerCard`* (`Ker.lean`): the kernel scheme `X ×_{φ, Y, e} Spec K` is finite over `K`, so affine with a finite
  `K`-algebra of sections `R`; its points with values in a field are ring maps out of `R` (Tangent.lean's `ptRing`).
  A complex point has image algebraic over `τ(K)`, hence inside `ι(K̄)` for a `K`-embedding `ι : K̄ → ℂ`
  (`mem_range_of_monic`: minimal polynomials over the algebraically closed `K̄` are linear), so every complex point of
  the kernel comes from a `K̄`-point (`kerSchPts_surj`); the `K̄`-points are finitely many (`Finite.algHom`). Hence
  `#ker f(ℂ)_τ ≤ #ker φ(K̄) = isogDeg φ`.
* *`IsogCotBijective`* (`CotPts.lean`, `Cot.lean`, `CotTan.lean`, `CotFinal.lean`). A local ring map
  `ρ : 𝒪_{𝒢,ξ} → Λ` gives the point `Spec ρ ≫ (Spec 𝒪_{𝒢,ξ} → 𝒢)` (`ptAt`, injective in `ρ` by Mathlib's
  `SpecToEquivOfLocalRing`, natural for `f`); `ε = ` evaluation along the unit section gives the trivial points.
  With the section `K → 𝒪_{𝒢,ξ}` extending the structure map, `f^*` is `K`-linear (`cotMapK`). If it were not onto,
  a nonzero functional vanishing on its image gives a derivation `D` at the origin killing `𝓞_K` and `f^*`; the
  point `ptAt (r ↦ ε r + D r ε)` is a tangent vector over `𝓞_K`, and `theta` turns it into a tangent vector `v` of `A`
  (`AtOrigin`) with `v ≫ φ = 1`. Then `v = 1` (`tangent_trivial`), so `D = 0`, a contradiction. Both cotangent
  spaces have `K`-dimension `dim A = dim B` (the kernel's `TangentDim`, from `tangentDim_of_regular`,
  `regularOrigin_of`, `dimOrigin_of`, `originStalkIso_of genericFibreStalkIso` and the proved `ZInQ.Contrib.Dim`
  facts; `dim A = dim B` by `topologicalKrullDim_eq_of_finite_surjective`), so `f^*` is bijective.
* *`tangent_trivial`* (`KerRing.lean`, `TanFinite.lean`; Cartier's argument, STANDARD: Mumford, *Abelian
  varieties*, §11, UNVERIFIED locator). Points of the kernel `G` with values in any `K`-algebra `Λ` are the
  `K`-algebra maps out of `R = Γ(G)` (`ringOf`, `ptOf`, natural in `Λ`). The tangent vector `v` is
  `ρ = e + εD : R → K[ε]`. The product `w = u'·v'` of the universal point `u ∈ G(R)` and `v`, both moved to
  `R[ε]`, is a ring map `ψ : R → R[ε]` with `fst ∘ ψ = id` (specialize along `ε ↦ 0`: `u·1`) and
  `liftTsze e ∘ ψ = ρ` (specialize along `e`: `1·v`), so `D̃ = snd ∘ ψ` is a derivation of `R` with `e ∘ D̃ = D`.
  For `x ∈ ker e`, the Artinian ring `R` (`IsArtinian.exists_pow_succ_smul_dvd`) gives `(1 - xy) x^N = 0`; applying
  `D̃` to `t x^{n+1} = 0` gives `t²(n+1) D̃(x) x^n = 0` with `e(t²(n+1)D̃ x) = e(t)²(n+1)D(x)`, nonzero in
  characteristic `0` if `D(x) ≠ 0`; descending to `n = 0` is a contradiction. So `D = 0` and `v = 1`.

## Remarks

* The upper half (`h(A) ≤ h(B) + ½ log deg φ`) is not on the chain since sem-prune and was not attempted.
* Kernel facts used and re-checked: `GroupModel.height` (Height.lean L235), `HodgeData.modelHeight_eq`,
  `torusMetricSq Λ c = ‖c‖² covol Λ` (HodgeData.lean L268), H5Glue's `secIndex_le_of_map`, `baseChange_map_bijective`,
  `hodgeLatticeNonzero_of_omegaSpans omegaSpans`, `CToPrinted.exists_extension` (TailZ19 L406).
