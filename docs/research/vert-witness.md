# vert-witness: `HeckeVertWitness` from good reduction of `Y₃`

Task vert-witness, 2026-11-13. Base: wip/vert-witness (8ec80711) with origin/wip/hecke-rest merged.
Lean: `scratch/vert-witness/`. The results log is `scratch/vert-witness/log.md`.

Model work only; no human has reviewed it. Marks used throughout:

- **VERIFIED**: compiled, computed, or read in a named file.
- **STANDARD**: a published result, with its reference.
- **SPECULATIVE**: an assessment.
- **UNVERIFIED**: a locator recalled from memory (there is no network here).

## 1. Main result

**`HeckeVertWitness` is proved in Lean from one new leaf and two glue Props (VERIFIED, compiled,
standard axioms only):**

```lean
theorem VertWitness.heckeVertWitness_of_goodReduction''
    (hL : ShimuraGoodReduction) (hU : SpecialFibreUniformizer) (hBD : ModelCoordinateGlue) :
    HeckeRestNV.HeckeVertWitness
```

(`heckeVertWitness_of_goodReduction'` is the same with `SpecialFibreDVR` in place of
`SpecialFibreUniformizer`; `specialFibreDVR_of_uniformizer` is compiled.)

- **Leaf `ShimuraGoodReduction`** (Morita 1981 / Carayol 1986 / Kottwitz 1992 / Buzzard 1997;
  locators UNVERIFIED). For each prime `p > 324` it asserts a smooth proper curve `𝒴` over
  `ℤ_(p)` with the universal family of level-3 QM abelian surfaces, the moduli bijection on
  `ℚ̄`-points, and the Hecke automorphisms over `ℤ_(p)`. It is stated over the kernel's genuine
  definitions (§3).
- **Glue `SpecialFibreUniformizer`** (standard scheme theory; Mathlib-only statement, not
  proved). A nonempty proper smooth relative curve over `ℤ_(p)` has a point `ξ` with
  `𝔪_ξ = (p)` and `p` a nonzerodivisor in `𝒪_{𝒴,ξ}`. The step from there to "the stalk is a DVR"
  (`SpecialFibreDVR`) is compiled: `dvr_of_maximalIdeal_eq_span`, Stacks 00PD, Mathlib only.
- **Glue `ModelCoordinateGlue`** (not proved). It does two things:
  - it compares the model's generic fibre with any triple `(Y, Φ, π)`;
  - it shows that the coordinate `X = π` has transcendental reduction at that point.

  Its proof needs the tame quotient `𝒴/Γ' ≅ P¹_{ℤ_(p)}` (§4.3). **This is where the remaining
  work is.**

**Composites (VERIFIED, `VertAll.lean`).** These replace hecke-rest's input
`hV : HeckeVertWitness`:

```lean
theorem VertWitnessAll.coverModelOfHecke_of_goodReduction (hconn : Y3Connected) (hRR : R1R2fp)
    (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hL : ShimuraGoodReduction) (hU : SpecialFibreUniformizer) (hBD : ModelCoordinateGlue) :
    CoverModelOfHecke
theorem VertWitnessAll.propTSAll_of_goodReduction ... (same three new inputs) : PropTSAll
```

**Lemma NV.** Route NV (h-b1 §3) would avoid a new *literature* leaf, but it does not avoid new
glue. That glue is harder to state in Lean today (§5). Neither route closes `HeckeVertWitness`
outright. The GR route is the one carried out here.

**Honest scope.**

- The compiled part is commutative algebra plus the wiring:
  - from a DVR in `E` to an unramified vertical prime (`vertGaussWitness_of_DVR`,
    `vertLocalWitness_of_gauss`, and hecke-rest's `vertUnramWitness_of_local`);
  - the DVR criterion `dvr_of_maximalIdeal_eq_span`;
  - `modelGaussGlue_of`, where nonemptiness of the model comes from R1fp's `ℚ̄`-point.
- The geometric content of good reduction is in the two glue Props. The leaf itself only says
  that the model exists.
- `ModelCoordinateGlue` is a substantial piece of arithmetic geometry: comparison of models, and
  tame quotients commuting with base change. Neither is in Mathlib 4.35.

## 2. Lean files (VERIFIED: `lake env lean`, 0 errors, no `sorry`, no `axiom`)

| File | Contents | Time |
|---|---|---|
| `VertWitness.lean` | `scratch/hecke-rest/NoVert.lean` lines 1-1265 (verbatim; `cmp` checked), then `VertMain.lean.part` | ~12 s |
| `VertAll.lean` | all of `scratch/hecke-rest/HeckeRestAll.lean` (verbatim; `cmp` checked) + `VertMain.lean.part` + `VertAllMain.lean.part` (the two composites) | ~60-80 s |

- `assemble.sh` builds both files.
- `compile_out.txt` and `compile_all.txt` hold the `#print axioms` lines. Every new declaration
  reads `[propext, Classical.choice, Quot.sound]`.
- The target `HeckeVertWitness` and hecke-rest's `VertLocalWitness` and `HeckeNoVertRam` are
  used unchanged (verbatim prefix).

| Declaration (namespace `VertWitness`) | Kind | Status |
|---|---|---|
| `VertGaussWitness E p` | def (valuation form of the output) | — |
| `vertLocalWitness_of_gauss` | `VertGaussWitness E p → VertLocalWitness E p` | compiled |
| `vertUnramWitness_of_gauss`, `heckeVertWitness_of_gauss` | wiring | compiled |
| `VertDVRWitness E p` | def (DVR form of the output) | — |
| `vertGaussWitness_of_DVR` | `VertDVRWitness E p → VertGaussWitness E p` | compiled |
| `IsShimuraModel p 𝒴 𝒜`, `ShimuraSmoothModel p` | the data asserted by the leaf | — |
| `ShimuraGoodReduction` | **leaf** | stated (§3) |
| `SpecialFibreDVR` | glue (scheme theory) | `specialFibreDVR_of_uniformizer : SpecialFibreUniformizer → SpecialFibreDVR`, compiled |
| `dvr_of_maximalIdeal_eq_span` | Noetherian local ring with `𝔪 = (t)`, `t ∈ R⁰` ⇒ domain and DVR | compiled (Mathlib only) |
| `SpecialFibreUniformizer` | **glue** (scheme theory) | stated, not proved (§4.2) |
| `ModelCoordinateGlue` | **glue** (comparison + coordinate) | stated, not proved (§4.3) |
| `ModelGaussGlue` | glue (the two together) | `modelGaussGlue_of : SpecialFibreDVR → ModelCoordinateGlue → ModelGaussGlue`, compiled |
| `heckeVertWitness_of_goodReduction`, `…'`, `…''`, `heckeNoVertRam_of_goodReduction` | composites | compiled |

### 2.1 The commutative algebra (compiled)

**`VertGaussWitness E p`.** There is a valuation subring `A ⊆ E` such that:

- `v_A ≤ 1` on the image of `ℤ[X]`;
- `v_A(f) < 1 ⟺ f ∈ p ℤ[X]`, so `v_A` restricts to the Gauss valuation;
- `v_A(x) < 1 ⟹ v_A(x) ≤ v_A(p)`, so `p` generates `𝔪_A`.

**Proof of `vertLocalWitness_of_gauss`.**

- The integral closure `B` of `ℤ[X]` in `E` lies in `A`. This uses `Valuation.Integers` and
  `isIntegral_iff_v_le_one`.
- Take `ψ : B → A` and `Q = ψ⁻¹(𝔪_A)`. Then `Q ∩ ℤ[X] = p ℤ[X]` by the second clause.
- Suppose `p ∈ 𝔪_A²`. Every element `y` of `𝔪_A²` has `v(y) ≤ v(p)²` (induction on
  `Submodule.mul_induction_on`). But `0 < v(p) < 1` gives `v(p)² < v(p)`, a contradiction.
- hecke-rest's `vertUnramWitness_of_local` then gives `e(Q) = 1`.

**`VertDVRWitness E p`.** There is a DVR `R` with an injective map `ι : R → E` such that:

- `E = Frac(ι R)`;
- `𝔪_R = (p)`;
- every `f ∈ ℤ[X]` is `ι(s)` with `s ∈ 𝔪_R ⟺ f ∈ p ℤ[X]`.

**Proof of `vertGaussWitness_of_DVR`.**

- `ι R` is a valuation subring of `E`, using `ValuationRing.cond`.
- Units of `ι R` correspond to units of `R`.
- If `v(ι s) < 1`, then `s ∈ (p)`, so `s = p t` and `v(ι s) = v(p) v(ι t) ≤ v(p)`.

**`modelGaussGlue_of`.**

- `𝒴` is nonempty: `Y` has a `ℚ̄`-point (R1fp), its object is a fibre of `𝒜` (the leaf's
  surjectivity clause), and `Spec ℚ̄` has a point.
- `SpecialFibreDVR` gives `ξ`.
- `ModelCoordinateGlue` gives `ι : 𝒪_{𝒴,ξ} → E`.
- `vertGaussWitness_of_DVR` finishes.

## 3. The leaf `ShimuraGoodReduction`

**Lean form.** `∀ p [Fact p.Prime], 324 < p → ∃ 𝒴 𝒜, IsShimuraModel p 𝒴 𝒜`. Here
`𝒴 : Over (Spec ℤ_(p))`, with `ℤ_(p) = Localization.AtPrime (span {p})`, and
`𝒜 : QMFamily 𝒴.left`. `QMFamily` is the kernel's: proper smooth of relative dimension 2, with
`ι(a)` and level sections `η(a)`. `IsShimuraModel` has eight clauses:

1. `IsProper 𝒴.hom`;
2. `SmoothOfRelativeDimension 1 𝒴.hom`;
3. *(fibres)* for every field `K ⊇ ℚ` and every `y : Spec K → 𝒴`, some `P : QML3 K` has
   `IsFibreOf 𝒜 y P`;
4. *(injective on `ℚ̄`-points)* two `ℚ̄`-points with isomorphic fibres are equal;
5. *(surjective on `ℚ̄`-points)* every `P : QML3 ℚ̄` is a fibre;
6. *(Hecke, twists)* each `α ∈ Aut 𝒪` is induced on `ℚ̄`-points by an automorphism of `𝒴` over
   `ℤ_(p)`;
7. *(Hecke, `𝒪^×`)* each `u ∈ 𝒪^×` is induced in the same way, through `M3.rightMul`;
8. *(guard, as in R1fp)* `𝒴` has a `ℚ̄`-point. Without it, `𝒴 = ∅` would satisfy every clause if
   `QML3 ℚ̄` were mis-encoded as empty. Added on the reviewer's advice.

**Published statement (STANDARD; locators UNVERIFIED).** Take an indefinite quaternion algebra
over `ℚ` of discriminant `D`, a maximal order `𝒪`, and a neat level `K` that is maximal at
`p ∤ D`. Then the moduli problem of abelian surfaces with `𝒪`-action and `K`-level structure is
representable over `ℤ_(p)` by a smooth proper curve. Polarized (PEL) or not depends on the
source. Sources:

- Kottwitz, J. AMS 5 (1992), 373-444, §5 (the bibliographic identity is established in locators.md row R1; §5 itself was unread by that audit): smooth PEL moduli for neat `K^p` and hyperspecial `K_p`,
  proper for division `B`. This covers level at `3 ∣ D`, since `3 ≠ p`. Cite it first.
- Buzzard, Duke 87 (1997): the polarization-free problem over `ℤ[1/DN]`.
- Morita, Hokkaido Math. J. 10 (1981): good reduction at `p ∤ D·level`.
- Carayol, Compositio 59 (1986). Its main construction is for totally real `F ≠ ℚ`.

At `3 ∣ D` the level structure is harmless (reviewer). `A[3]` is étale over `ℤ_(p)`, `T₃A` is
free of rank 1 over `𝒪₃`, and `η : (𝒪/3𝒪)_S ≅ A[3]` is the `K₃`-structure.

Here `D = 6`, `K = K₃` (full level 3, neat) and `p > 324`.

**Why the Lean form is a consequence and never stronger** (the same pattern as R1fp's reviewed
leaf, `ZInQKernel/HDecomp/QM/Leaves.lean`):

- Clauses 3-5 restrict the representing isomorphism to fields of characteristic 0. Clause 3 is
  `y*` of the universal object, the shape of `IsFibreOf`, as in `R1famProps`.
- In characteristic 0, `Hom(ℤ_(p), K)` is a singleton, so any `Spec K → 𝒴` is a point over
  `ℤ_(p)`.
- Clauses 4-5 use only `K = ℚ̄`. There the polarization is dropped by Lemma P, exactly as in R1fp.
- Clause 8 holds because the Shimura curve has `ℚ̄`-points.
- Clauses 6-7: `twist α` and `rightMul u` are automorphisms of the moduli functor on
  `ℤ_(p)`-schemes, because they are defined on families. By Yoneda they act on `𝒴` over `ℤ_(p)`.
- The leaf asserts only `p > 324`; the published range is `p ∤ 6`.
- Nothing about a coordinate or the quotient `𝒴/Γ'` is asserted. That is glue.

**Narrowness.** Each clause is used:

- 1-2 by `SpecialFibreDVR`;
- 5 by the nonemptiness step (compiled);
- 3-5 by the comparison (b);
- 6-7 by the quotient (d).

No clause concerns positive-characteristic points. This avoids the question of whether the
polarization-free and polarized problems agree in characteristic `p`.

**Caveat (SPECULATIVE).** The level `K₃` sits at `3 ∣ D`. It is maximal at `p` and neat, which
is what the cited theorems require. Which of the four sources states the full-level-3 case at a
prime dividing the discriminant, literally and without modification, is UNVERIFIED and needs a
human check. This caveat is of the same kind as the one on R1fp in locators.md.

## 4. The glue

### 4.1 Where the arithmetic sits

`HeckeVertWitness` asks for one prime of `B` over `p ℤ[X]` with `e = 1`. hecke-rest showed that
this is equivalent to `HeckeNoVertRam`. It is also equivalent to `VertGaussWitness` and to
`VertDVRWitness` (take `R = B_Q`). So the reductions in §2.1 change the *shape* of the statement
to "a DVR of `E` restricting to the Gauss valuation with `p` a uniformizer". Its content is
unchanged.

The content enters only through the leaf and the two glue Props below. ts-hecke §6 records why no
argument from branch data alone can work: `E = ℚ(X)(√(pX))` has the same branch data and is
vertically ramified.

### 4.2 `SpecialFibreUniformizer` / `SpecialFibreDVR` (STANDARD scheme theory; statements use Mathlib only)

**Statements.** Let `𝒴 / ℤ_(p)` be proper, smooth of relative dimension 1 and nonempty.

- `SpecialFibreDVR`: some `ξ` has `𝒪_{𝒴,ξ}` a DVR with `𝔪 = (p)`.
- `SpecialFibreUniformizer`: some `ξ` has `𝔪_ξ = (p)` with `p` a nonzerodivisor of `𝒪_{𝒴,ξ}`.

The first follows from the second by step 3 below, which is compiled
(`specialFibreDVR_of_uniformizer`). That proof gets Noetherian stalks from
`LocallyOfFiniteType.isLocallyNoetherian` and then applies `dvr_of_maximalIdeal_eq_span`.

**Proof outline.**

1. Smooth implies flat, so `𝒴 → Spec ℤ_(p)` is open (flat and of finite presentation). It is also
   closed (proper). Its image is nonempty and `Spec ℤ_(p)` is connected, so the map is
   surjective, and the special fibre `𝒴_p` is nonempty.
2. `𝒴_p` is smooth over `𝔽_p`, hence reduced. Let `ξ` be the generic point of one of its
   components. Then `𝒪_{𝒴,ξ}/p = 𝒪_{𝒴_p,ξ}` is a reduced local ring of dimension 0, so it is a
   field. Hence `𝔪_ξ = (p)`.
3. `p` is a nonzerodivisor (flatness), and `𝒪_{𝒴,ξ}` is Noetherian. A Noetherian local ring whose
   maximal ideal is generated by a nonzerodivisor is a DVR (Stacks 00PD; UNVERIFIED tag).
   **Compiled** as `dvr_of_maximalIdeal_eq_span`. Krull's intersection theorem writes each nonzero
   `a` as `tⁿ·unit`; then the ring is a domain, and
   `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization` applies.

**Lean for steps 1-2 (`SpecialFibreUniformizer`).** Not done. It needs:

- the fibre `𝒴_p` and its stalks as quotients of the stalks of `𝒴` (infra-stalks'
  `pullback_stalkGen` is the surjectivity half);
- "smooth over a field ⇒ reduced", which is not in Mathlib 4.35 (searched `RingTheory/Smooth/`,
  `RingTheory/Etale/`, `RingTheory/Unramified/`; `AlgebraicGeometry/Morphisms/Smooth.lean` assumes
  `IsReduced`). An alternative avoids it: use a local étale map to `𝔸¹_{ℤ_(p)}` and
  `Algebra.FormallyUnramified.map_maximalIdeal` (in `RingTheory/Unramified/LocalRing.lean`);
- flatness of stalk maps for the nonzerodivisor (`Smooth ⇒ Flat` is an instance);
- generic points of components of a fibre.

All are standard. **Size: medium** (SPECULATIVE: a few hundred lines).

### 4.3 `ModelCoordinateGlue` (route GR; not proved)

**Statement.** Take the model `(𝒴, 𝒜)` at `p > 324`, any `ξ` with `𝒪_{𝒴,ξ}` a DVR with
`𝔪 = (p)`, any triple `(Y, Φ, π)` with R1fp, R1hecke and R2fp, and any finite Galois `E/ℚ(X)`
with the normalization chart. Then there is an injective `ι : 𝒪_{𝒴,ξ} → E` with:

- `E = Frac(ι 𝒪_{𝒴,ξ})`;
- every `f ∈ ℤ[X]` equal to `ι(s)` for some `s`, with `s ∈ 𝔪_ξ ⟺ f ∈ p ℤ[X]`.

**Proof outline.**

- **(b) Comparison.**
  - Pull `𝒜` back to the generic fibre `𝒴_ℚ`. Its field fibres are objects (clause 3).
  - `R1univProps` of `Y` gives `g : 𝒴_ℚ → Y`. `g` is compatible with the classes, so it is
    bijective on `ℚ̄`-points (clauses 4-5 against `Φ`).
  - A morphism of smooth proper curves over `ℚ` that is bijective on `ℚ̄`-points is an
    isomorphism: it is quasi-finite and proper, hence finite; it has degree 1 in characteristic
    0; and it is finite birational onto a normal target.
  - `Y` is irreducible: a component on which `π ≡ ∞` would carry infinitely many `ℚ̄`-points with
    twist-equivalent pairs, which R2fp and finiteness of level structures exclude. All other
    `ℚ̄`-points lie in the dense image of the chart `Spec B`. So `𝒴` is integral (flat, with
    irreducible generic fibre), and `ℚ(𝒴) = ℚ(Y) = Frac B = E`.
  - `ι` is the germ map to the function field. Mathlib has `germ_injective_of_isIntegral` and
    `IsFractionRing (X.presheaf.stalk x) X.functionField`.
- **(d) The coordinate.**
  - Clauses 6-7 give automorphisms of `𝒴` over `ℤ_(p)` (an automorphism is determined by its
    generic fibre, since `𝒴` is flat and separated). They generate a finite group `G'`, whose
    image on `E` is `Gal(E/ℚ(X))` (R2fp: the `π`-fibres are the `Γ'`-orbits), of order
    `≤ 324 < p`.
  - The quotient `𝒵 = 𝒴/G'` exists (`𝒴` is projective). Since `p ∤ |G'|`, its formation commutes
    with base change (SGA 1 V.1; UNVERIFIED locator).
  - So `𝒵` is proper and flat over `ℤ_(p)`, with normal fibres. Its generic fibre is `P¹_ℚ` in
    the coordinate `π`, and its special fibre `𝒴_p/G'` is a smooth curve of genus 0.
  - The CM points over `0, ∞, −16/27` extend to sections, and their reductions in `𝒵` are
    distinct. Suppose two of them, `y_b` and `y_{b'}`, had the same reduction `z` in `𝒴` (after
    moving `y_{b'}` within its `G'`-orbit). Then:
    - the stabilizer of `z` is cyclic (it is tame and acts faithfully on the cotangent line);
    - it contains the stabilizers of `y_b` and `y_{b'}`, of orders `4, 6, 2`;
    - so its unique involution fixes both `y_b` and `y_{b'}`;
    - but the fixed scheme of a tame automorphism of the smooth proper `𝒴` is finite étale over
      `ℤ_(p)` (Edixhoven, Compositio 97 (1995), Prop. 3.4; UNVERIFIED), so distinct generic fixed
      points have distinct reductions. Contradiction.
  - A smooth proper genus-0 curve over `ℤ_(p)` with three pairwise disjoint sections is
    `P¹_{ℤ_(p)}`, in the unique coordinate sending them to `0, ∞, −16/27` (these values are
    distinct mod `p`, since `p ∤ 6`). That coordinate is `π`.
  - Hence `π : 𝒴 → P¹_{ℤ_(p)}` is finite and surjective on special fibres, `π ∈ 𝒪_{𝒴,ξ}`, and
    its reduction is transcendental.
  - So `f(π) ∈ 𝔪_ξ` iff the reduction `f̄` vanishes, i.e. iff `f ∈ p ℤ[X]`.

**What it needs beyond Mathlib** (SPECULATIVE sizing, large):

- the generic fibre as a `ℚ`-scheme with the pulled-back family;
- "bijective on `ℚ̄`-points ⇒ isomorphism" for smooth proper curves;
- quotients of projective schemes by finite groups, and their base change in the tame case;
- genus-0 curves with a section over a DVR are `P¹`;
- disjointness of the CM sections.

The tame-quotient statement and "genus 0 with section ⇒ `P¹`" are textbook theorems (SGA 1
Exp. V; Hartshorne IV.1). They could be added as *textbook leaves* if the project prefers that to
proving them.

## 5. Route NV, compared

Lemma NV (h-b1 §3) argues as follows:

- tameness;
- residue fields of the CM points unramified at `p` (R1rec);
- the local structure at the height-2 primes `(p, X − b)` (two-dimensional Abhyankar);
- the inertia of the `W = (ℤ/2)²` layer `X₆ → P¹` (from R2/X6 and genus 0 of `X₆`).

Assessment (SPECULATIVE):

- **No new literature leaf.** Two-dimensional Abhyankar at a normal-crossings point of `P¹_ℤ` is
  glue from the bundle's T2 (`PkgI2.AbhyankarDVR`, DVR form) plus purity in dimension 2
  (t-purity3's `purityGlobalDim2'`, proved), via the Kummer trick (adjoin `p^{1/e}` and
  `(X − b)^{1/e}`; the result is regular, and purity applies).
- **New glue, harder than GR's in Mathlib today:**
  - inertia groups at height-2 primes of `B` and their containments (`I_q ⊂ I_𝔓 ⊃ I_{Q_b}`, via
    going-down for the flat `B` over `ℤ_(p)[X]`);
  - the Kummer local model and the residue-degree count of the branch of `Q_b` at `𝔓`;
  - the `W`-quotient's inertia.
- **A transfer problem.** `HeckeVertWitness` is quantified over every triple satisfying R1fp,
  R1hecke and R2fp, but R1rec and X6 are bundle facts about *one* triple (`R1R2fp`). The proof
  would need qm-pin's comparison (`Pin.MobiusGlue`) to move residue fields and the `W`-layer to an
  arbitrary triple.
- GR's comparison (b) does the corresponding job through `R1univProps` and needs no bundle
  clause beyond R1fp.
- The reviewer suggests an alternative: state two-dimensional Abhyankar as a *textbook leaf* (SGA 1
  Exp. XIII 5.2-5.3; UNVERIFIED numbers) instead of deriving it. That leaf would be general and
  well located, arguably safer than the Shimura-specific GR leaf whose locators are unverified.
  It would still leave the inertia-group glue and the transfer.

**Recommendation.** For the announcement, list `ShimuraGoodReduction` as the literature input for
no vertical ramification, and `SpecialFibreUniformizer` plus `ModelCoordinateGlue` as project
glue. Keep
NV as the alternative that trades the Morita/Carayol leaf for two-dimensional inertia glue.

## 6. Independent review

A read-only model agent reviewed the leaf and the glue statements. It had no Lean, and it saw the
version before the guard clause and before `SpecialFibreUniformizer`.

### 6.1 Verdicts

- **`ShimuraGoodReduction`: TRUE as a weaker consequence** of representability (Kottwitz for neat
  `K^p` and hyperspecial `K_p`; Buzzard without polarization).
  - Field points are automatically over `ℤ_(p)`.
  - Level at `3 ∣ D` is harmless.
  - The polarization matters only at characteristic-0 points, via Lemma P as in R1fp.
  - The Hecke automorphisms exist over `ℤ_(p)` in both formulations.
  - **Fixes applied:** the vacuity guard (clause 8), and the citation order (Kottwitz and Buzzard
    first).
- **`SpecialFibreDVR`: TRUE.** It needs nonemptiness, which is present.
- **`ModelCoordinateGlue`: TRUE for every `ξ`, triple and `E`.**
  - Every admissible `ξ` is a generic point of a special-fibre component.
  - `Y` is irreducible because the chart meets every component.
  - `X = h*π.f` agrees with `π` on `ℚ̄`-points, and `B` is reduced and Jacobson.
  - **Fix applied:** the disjointness of the CM sections is argued from finite étale fixed loci
    and cyclic stabilizers, not from Hurwitz sums (Hurwitz totals agree whether or not points
    collide).
  - **Also stated now:** `𝒪^× ↠ (𝒪/3𝒪)^×` (strong approximation for `𝒪¹` plus a unit of norm
    `−1`), and smoothness of `𝒵`'s fibres.
- **`ModelGaussGlue`, `VertGaussWitness`, `VertDVRWitness`: TRUE, with no hidden triviality.**
  Clause 2 of `VertGaussWitness` excludes the trivial valuation and extensions of `v_p` under
  which `X` has constant reduction. For Galois `E` it is equivalent to `NoVerticalRam`.
- **NV:** it would need the glue signature to carry the R1R2fp bundle, plus Abhyankar at height-2
  primes. See §5. Within GR, a leaf is unavoidable: smoothness of the model is exactly its
  content.

## 7. What remains (for the announcement)

| Prop | Kind | Status |
|---|---|---|
| `ShimuraGoodReduction` | **leaf** (Morita/Carayol/Kottwitz/Buzzard; locators UNVERIFIED; the level-3-at-`3 ∣ D` coverage needs a human check) | stated in Lean |
| `SpecialFibreUniformizer` | glue (standard scheme theory; `SpecialFibreDVR` follows, compiled) | stated, not proved |
| `ModelCoordinateGlue` | glue (comparison of models; tame quotient `𝒴/Γ' ≅ P¹_{ℤ_(p)}`) | stated, not proved |
| `Y3Connected`, `R1R2fp`, `TorsionStructure`, `QMAutCard`, `SerreRigidity3`, `ALFixedPoints` | leaves (existing, from ts-hecke and hecke-rest) | unchanged |

`CoverModelOfHecke` and `PropTSAll` follow from these by compiled composites
(`VertWitnessAll.coverModelOfHecke_of_goodReduction`, `VertWitnessAll.propTSAll_of_goodReduction`).
