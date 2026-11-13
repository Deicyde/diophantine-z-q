# g0-mod-galois: glue steps G8-G12 (the Galois side of `ModularConstituent`)

Task g0-mod-galois, 2026-11-13. Lean: `scratch/g0-mod-galois/part_galois.lean`, `part_matrix.lean`,
`part_det.lean` and `part_bundle.lean` (namespace `G0Galois`). `scratch/g0-mod-galois/build.sh`
appends them, in that order, to g0-split's `scratch/g0-split/Split.lean`, giving
`scratch/g0-mod-galois/ModGalois.lean`. Log: `scratch/g0-mod-galois/log.md`. The base merges
`origin/wip/g0-split` (c20fa62b) for `Split.lean`.

## 1. Result

**The range G8-G12 is proved, with no `sorry`, from three groups of inputs.**

- **Leaves:** the leaf bundles, plus two leaves outside them: Burnside's theorem
  (`BurnsideAbsIrred`, textbook) and R14 with its published determinant clause (`R14Det`).
- **Earlier steps:** their outputs (`G2Out`, `G3Out`, `G6Out`, `G7Out`).
- **Five named glue Props:** `G9Glue` (N5's de Rham descent lemma), `G10Glue` (oddness),
  `G12Weight` (the Hodge–Tate weight comparison), `DetTate` (`det V_ℓ(A) = χ_ℓ^{dim A}`, from T9)
  and `ResQFiniteIndex` (`[G_ℚ : G_K] < ∞`).

The first-draft pieces `G8Matrix` (linear algebra) and `G12Det` (the determinant identities) are
now proved: `g8Matrix_of_burnside` and `g12Det_of`.

The conclusion is delivered in the exact form that g0-mod-newform's range takes as input (its
`G12Out`), by `G0Galois.newformG12Out_of_galois`. That step needs one more named Prop,
`FiniteCharDirichlet` (the Kronecker–Weber step).

VERIFIED: `lake env lean scratch/g0-mod-galois/ModGalois.lean` gives 0 errors and no
`declaration uses sorry` (run11, 2m31s). `#print axioms` gives `[propext, Classical.choice,
Quot.sound]` for these theorems:
- `G0Galois.g8`, `g11`, `g12`;
- `g8_g12`, `g8_g12_of_leaves`;
- `g8Matrix_of_burnside`, `g12Det_of`;
- `commonConstituent_of_sides`, `isConstituentOf_of_intertwines`, `newformG12Out_of_galois`.

```
theorem G0Galois.g8_g12_of_leaves (r : HSyn.ResearchLeaves) (t : HSyn.TextbookLeaves)
    (m : GaloisPieces)
    {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (T : Finset ℕ)
    (h2 : G2Out K T) (h6 : G6Out A) (h3 : G3Out A 5 T)
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a β : PkgI4.GQ → PadicAlgCl 5)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl 5) (Vb A 5))
    (h7 : G7Out A 5 Tm c ε a β u) :
    ∃ r₅ : GaloisRep 5 2, G8Out A 5 (GlueDescent.rho Tm a β) r₅ ∧ G9Out r₅ ∧ G10Out r₅ ∧
      G11Out T r₅ ∧ G12Out r₅
```

`m : GaloisPieces` bundles the two extra leaves (`BurnsideAbsIrred`, `R14Det`) and the five named
glue Props (§3). The same statement at
any prime `ℓ`, without G12, is `G0Galois.g8_g11` (used at `ℓ = 3` by G14-G15). The version with
the leaves as separate hypotheses is `G0Galois.g8_g12`.

**What is proved, not assumed.**

- **G8** (`G0Galois.g8`). Inputs: `G7Out`, the leaves R9a, R9b, T6, T26, and glue-ssbc's proved
  `SemisimpleBaseChange`. The descended operators `ρ = β⁻¹ a Tm` form a representation of `G_ℚ`
  (glue-descent's `rhoRep`). `ρ` commutes with the matrix units of `B ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)` and is the
  Tate action on `G_{L'}`. `dim (ℚ̄_ℓ ⊗ V_ℓ(A)) = 4` comes from T26 with `dim A = 2`, so
  `W = e₀₀ V ≠ 0`. C2 (`PkgI3.C2_absolutelyIrreducible`), applied to `splitEquiv`, makes `ρ|_W`
  absolutely irreducible on `G_{L'}`. The step from there to a continuous
  `r : G_ℚ → GL₂(ℚ̄_ℓ)` in Burnside form is `G8Matrix`, which is **proved**
  (`g8Matrix_of_burnside`, `part_matrix.lean`) from `BurnsideAbsIrred`. That proof takes a basis
  of `W` (`finBasisOfFinrankEq`) and the matrix hom through `toMatrixAlgEquiv` and `toHomUnits`.
  Continuity comes from `G7Out`'s weak continuity through the functionals `b.coord i ∘ e₀₀`
  (`Units.continuous_iff`, `continuous_matrix`). The intertwining comes from `splitEquiv` and
  `toMatrix_mulVec_repr`.
- **G11** (`G0Galois.g11`). Proved from `G2Out`, `G3Out` and G8's intertwining, with no named
  glue: an inertia element above `p ∉ T ∪ {ℓ}` lies in `G_K` (G2). It acts trivially on
  `V_ℓ(A)` (G3 with R7a), so trivially on `r ⊕ r`, so `r(σ) = 1`.
  `finitelyRamified_of_g11` gives Pan's finite-ramification hypothesis with `S = T ∪ {ℓ}`.
- **G12** (`G0Galois.g12`). Pan∘Berger (`PkgI4.PanBerger`, the bundle's `r11r12`) is applied at
  `p = 5`. Its hypotheses come from:
  - irreducibility: G8, through `isIrreducible_of_g8`;
  - finite ramification: G11;
  - de Rham, and distinct weights `0 ≠ −1`: G9;
  - oddness: G10.

  Pan gives an eigenform `g` of some weight `k ≥ 1` and a continuous twist `ψ`. The named piece
  `G12Weight` gives `{n, n+1−k} = {0, −1}`. The proved `PkgI4.weight_match` then gives `k = 2`
  (and `n = 0`). `G12Det` gives the determinant identities. It is **proved** (`g12Det_of`,
  `part_det.lean`) from four inputs: R14Det; `DetTate`; `ResQFiniteIndex`; and T18 (the bundle's
  `FrobeniusDense`, with c9-rhof's `eq_of_eq_on_arithFrob` copied).

  The proof first shows that the traces of `r` and `ψ ⊗ ρ_g` agree at Frobenius elements, hence
  everywhere. Then `det M = (tr(M)² − tr(M²))/2` gives `det r = ψ² det ρ_g = ε χ₅ ψ²`. Finally
  `(det r)² = det V₅(A) = χ₅²` on `G_K`, through `e`, `LinearMap.det_conj` and `det_prodMap`.
  The proved `GlueAssembly.twist_finite` turns these identities into finiteness of `ψ`.
- **Link to `ModularConstituent`** (`G0Galois.commonConstituent_of_sides`, proved). G8's `e`,
  together with what G13-G16 must deliver on the `J₁(N)` side (`JSide`), gives
  `HSyn.G0Split.CommonConstituent A J`, the last field of `ModularConstituent`, with `ℓ = 5` and
  `E = ℚ̄₅`.

## 2. The interface (all `def … : Prop` in `part_galois.lean`, with docstrings)

The coefficient field is `ℚ̄_ℓ = PadicAlgCl ℓ` throughout (Pan's coefficients). The model is
`A : PkgI3.AbVar K` over `K = L'`. ModularConstituent's model is
`ZInQ.DefFaltings.AbVar L.K`, which `LeafAdopt.abVarEquiv` carries to `PkgI3.AbVar`.
`resQ K : G_K →* G_ℚ` is the restriction along the fixed embedding `qEmb K : ℚ̄ → K̄`
(`IsAlgClosed.lift`; `res` copied from scratch/e1-sub), so `qEmb K ∘ resQ K τ = τ ∘ qEmb K`
(`resQ_spec`), and `resQ K τ` is the unique such element (`eq_resQ`). `tate A ℓ` is the
`G_K`-action on `ℚ̄_ℓ ⊗ V_ℓ(A)` (`GlueI3.repBaseChange` of pkg-I3's `galRep`). The names
`G2Out`, `G7Out`, `G12Out` also occur in the partner files, as different definitions in other
namespaces (`G0ModField`, `G0ModNewform`). Here they are `G0Galois.G2Out` and so on.

**Inputs (outputs of earlier steps).**

| Prop | step | content |
|---|---|---|
| `G2Out K T` | G2 (PR(i)) | every inertia element of `G_ℚ` above `p ∉ T` lies in `resQ K (G_K)` (`K = L'` unramified outside `T`) |
| `G3Out A ℓ T` | G3 (PR(ii)) + R7a | for `p ∉ T`, `p ≠ ℓ`, inertia elements of `G_K` above `p` act trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` (instantiation of `PkgI2.inertiaTrivial_of_goodReduction`) |
| `G6Out A` | G5-G6 | `End_K(A)` is a division ring (`PkgI3.EndDivision`) and is noncommutative |
| `G7Out A ℓ Tm c ε a β u` | G7 (+ A9, G4) | `dim A = 2`; `rank_ℤ End_K(A) = 4`; operators `Tm σ = a_σμ_σ∘σ` with `Tm g Tm h = c(g,h) Tm(gh)`; `a_g a_h c(g,h) = ε(g,h) a_{gh}`; `β_gβ_h = ε(g,h)β_{gh}`, `β ≠ 0`; on `G_{L'}`: `Tm = tate`, `a = β = 1`; matrix units `u` commuting with every `Tm σ`; weak continuity of `β⁻¹ a Tm` |

**Outputs of this range.**

| Prop | step | content |
|---|---|---|
| `G8Out A ℓ ρ r` | G8 | `ρ ∘ resQ = tate`; `e : ℚ̄_ℓ ⊗ V_ℓ(A) ≅ ℚ̄_ℓ² × ℚ̄_ℓ²` intertwines `ρ(g)` with `r(g) ⊕ r(g)` for every `g ∈ G_ℚ`; the matrices `r(σ)`, `σ ∈ G_{L'}`, generate `M₂(ℚ̄_ℓ)` (absolutely irreducible) |
| `G9Out r` | G9 | `LocalIsDeRham ℓ 2 (r|G_{ℚ_ℓ})` and `HasHTWeightsAtSelf ℓ {0, −1}` |
| `G10Out r` | G10 | `r.IsOdd` |
| `G11Out T r` | G11 | `r` unramified at every prime `p ∉ T`, `p ≠ ℓ` |
| `G12Out r₅` | G12 | `∃ N ≥ 1, χ, g ∈ S₂(Γ₁(N))` normalized eigenform with nebentypus `χ`, `ψ` continuous of finite image, `ιC`, `ιL`, `S` finite: `r₅.AttachedUpToTwist ψ ιC ιL g S` |

## 3. What remains: two extra leaves (Burnside, R14Det), five named glue Props, and one more for the newform feed

Sizes are SPECULATIVE (small < 500 lines, medium 0.5-3k, large 3-10k).

| Prop | content | inputs named in it | why true | size |
|---|---|---|---|---|
| `BurnsideAbsIrred` (replaces `G8Matrix`, which is proved from it) | a representation of a monoid on a finite-dimensional `F`-space that stays irreducible after every field extension has image generating `M_n(F)` (any basis) | none: a textbook leaf | Burnside (Lang, *Algebra* XVII §3; Curtis–Reiner §27; locators UNVERIFIED). Mathlib's `jacobson_density` is the route to a proof | small-medium |
| `G9Glue` | R10 → T23 → (`ℚ̄_ℓ ⊗ V_ℓ(A) ≅ r\|G_K ⊕ r\|G_K`, `dim A = 2` ⇒ `G9Out r`) | R10 (`DeRhamComparison`), T23 | N5's appendix lemma (h-trust C3, two model reviews) with the Galois choice of the local field. Needs base change of `PkgI3.AbVar` to a completion, the identification of pkg-I3's and pkg-I4's `AbVar` copies, and the reduction to a finite coefficient field | medium-large |
| `G10Glue` | T11 → T12 → R9b → (`K` Galois, `End_K(A)` rank 4, division, noncommutative, the same splitting ⇒ `r` odd) | T11, T12 (opaque placeholders), R9b | N5 L742-751 (h-trust C5). For any extension `r`, `φ = ρ(c)∘c⁻¹` is `B`-linear and in `Hom(A^c, A) ⊗ ℚ̄_ℓ` (Faltings), so it equals `a·μ_c`, and the Betti argument applies. SPECULATIVE as a reduction; each step STANDARD or model-reviewed | medium (needs analytification) |
| `G12Weight` | R14 → R13 → R15 → T18 → T19 → (Pan's output for an irreducible `r` with weights `{0,−1}` ⇒ `∃ n, {n, n+1−k} = {0,−1}`) | R13, R14, R15, T18, T19 | `r ≅ ρ_g ⊗ ψ` (Chebotarev, Brauer–Nesbitt), weights of a twist shift by the weight of `ψ`. For `k = 1`, Deligne–Serre gives weights `{0,0}`, which contradicts `{0,−1}` (h-trust C8) | medium (HT weights of tensor products) |
| `R14Det` (leaf, replaces the R14 clause that `G12Det` needed) | R14 with its published determinant: the semisimple `ρ_g` attached to `g` has `det ρ_g = ε·χ_ℓ^{k−1}`, `ε` of finite image | none: a leaf (Shimura 1971 Thm 7.14, Deligne 1971, Deligne–Serre 1974; locators UNVERIFIED) | the published theorems state the determinant | — |
| `DetTate` | `det(tate A ℓ σ) = χ_ℓ(resQ σ)^{dim A}` on `G_K` | (T9) | Weil pairing of a polarization: `G_K` acts through `GSp_{2g}` with multiplier `χ_ℓ` (Mumford §20, §23; STANDARD) | medium (T9's pairing on torsion → determinant on `V_ℓ`) |
| `ResQFiniteIndex` | `(resQ K).range` has finite index in `G_ℚ` | none | the index is `[K:ℚ]` (Galois theory of `ℚ̄/ℚ`) | small-medium |
| `FiniteCharDirichlet` (only for the newform feed, §4.1) | T17 → (a continuous `ψ : G_ℚ → ℚ̄_ℓ^×` of finite image is, at arithmetic Frobenius above `p ∉ S`, `ιL(β)` with `ιC(β) = ψD(p)` for a Dirichlet character `ψD` mod `m`) | T17 (Kronecker–Weber) | the kernel field is finite abelian, so it lies in `ℚ(ζ_m)`; the values are roots of unity, which lie in `ιL(ℚ̄)` (h-trust C8 item 4) | small-medium |

**A leaf gap found (VERIFIED by reading the statement), now handled by `R14Det`.** The determinant argument needs `det ρ_g = ε_g χ_c`
(at `k = 2`). The bundle's R14 (`HSyn.EigenformRepExists`, consequence form) omits the
determinant: its docstring says "the published statements also give the determinant". Its
`AttachedTo` gives only traces of arithmetic Frobenius elements at `p ∤ Nℓ`. These do not fix
`det ρ_g(Frob_p)`, since `Frob_p²` is not an arithmetic Frobenius at `p`. So either R14 is
strengthened to the published statement with `det ρ_g = ε_g χ_c^{k−1}` (still a consequence of
the published theorem, so still a leaf), or `G12Det` keeps this as glue from Eichler–Shimura.
Recommendation: strengthen R14 (one clause). This file does so as the separate leaf `R14Det`
(`part_det.lean`), so `HSyn.ResearchLeaves.r14` can be replaced by it.

**The split of `G12Det` (done, `g12Det_of`, VERIFIED run10-11).** `cycQ ℓ : G_ℚ → ℚ̄_ℓ^×` is the
`ℓ`-adic cyclotomic character, defined like `PkgI4.cyc` but on `G_ℚ`, from Mathlib's
`cyclotomicCharacter`. `G12Det` follows from three pieces and T18:

1. **R14Det** (leaf, R14 with its published determinant clause): the semisimple `ρ_g` attached to
   `g` has `det ρ_g = ε · χ_ℓ^{k−1}`, with `ε` of finite image.
2. **DetTate** (glue from T9): `det(tate A ℓ σ) = χ_ℓ(resQ σ)^{dim A}` for `σ ∈ G_K`.
3. **ResQFiniteIndex** (glue, Galois theory): `(resQ K).range` has finite index.

These are combined by proved steps:

- `det r = det(ρ_g ⊗ ψ)`. The traces agree at Frobenius elements, so they agree everywhere:
  c9-rhof's `eq_of_eq_on_arithFrob` from T18 does this. Then `det_fin_two_eq_trace` gives
  `det M = (tr(M)² − tr(M²))/2` for `2 × 2` matrices.
- `det(r ⊕ r) = (det r)²` through `e`, with `LinearMap.det_conj`, `det_prodMap` and `det_toLin'`.

## 4. How the conclusion feeds G13-G16 and `ModularConstituent`

`ModularConstituent` (scratch/g0-split/part_split.lean) asks, for `u ∉ 𝒞` and a fibre object
`P`, for the following:

- `L'`, an embedding `L' → ℚ̄` and a model `A/L'` of `P.A`;
- `N ≥ 1` and `J` with `IsJ1 N J`;
- `N ≤ QM²` and `[L':ℚ] ≤ QM`;
- `CommonConstituent A (J_{L'})`.

**The three ranges already interlock through verbatim copies of this file's definitions.**
VERIFIED by a token comparison script (log, 02:55-03:00) against the partners' pushed files:

- g0-mod-field (origin 9f698815) has `G0ModField.GaloisCopy`, a copy of `resQ`, `Vb`, `tate`,
  `G2Out`, `G7Out`. All five are identical to the current definitions here.
- g0-mod-newform (origin 8ab403b1) has a copy of `resQ`, `Vb`, `tate`, `Intertwines`, `G8Out`,
  `G12Out` (the last two renamed `GalG8Out`, `GalG12Out`). All six are identical.

(Between 02:16 and 02:50 this file had a different `resQ`, `res (qEmb K)`. It was restored to
Mathlib's `Field.absoluteGaloisGroup.map`, which both partners copied. `qEmbRing` is the embedding
that `map` chooses, and `resQ_spec` is proved for it.)

### 4.1 The composite, step by step

1. **From G2-G7 (g0-mod-field).** Its `G7Data u P L A ε N χ β L' hLL'` gives:
   - `L'` (finite Galois, `[L':ℚ] ≤ QM`, unramified outside `T u`) and the model `A_{L'}`;
   - this file's `G2Out L' (T u)`, through their **proved** `galoisG2Out_of_g7Data` (with their
     proved `ResQRange`: the image of `resQ L'` is `Fix(L')`);
   - this file's `G7Out (A_{L'}) ℓ …` at each `ℓ`, through their **stated, unproved**
     `TateBridge` (the Tate functor on the points-level `m_σ`, coefficients in `ℚ̄_ℓ`, matrix
     units). `TateBridge` also takes `dim A_{L'} = 2` and `rank End = 4` as hypotheses.
2. **Inputs from outside the three ranges.**
   - `G3Out A ℓ T`: G3's good reduction outside `T` (on leaf-qm-fp's objects
     `LeafQM.AV.QML3.goodReduction`; g0-mod-field's `IsQMModel` makes `A` such a base change), with
     R7a.
   - `G6Out A`: `EndDivision`, which g0-split's `FibreSimple` covers, and noncommutativity of
     `End_{L'}(A)` (G5-G6).
3. **This range.**
   - `g8_g12` (or `g8_g12_of_leaves`) at `ℓ = 5` gives `r₅` with `G8Out`, `G9Out`, `G10Out`,
     `G11Out`, `G12Out`.
   - `g8_g11` at `ℓ = 3` gives `r₃` with `G8Out`, …, `G11Out`.
4. **Into G13-G16 (g0-mod-newform).**
   - Their **proved** `g12Spec_of_galois (hDF : DirichletOfFinite) A ρ5 ρ3 r5 r3 h5 h3 h12` turns
     `G8Out` at 3 and 5 and `G12Out r₅` into `∃ i ιC ι5, ∀ ι3, G12Spec ⟨i, ιC, ι5, ι3, r5, r3⟩`.
     Their `DirichletOfFinite` is this file's `FiniteCharDirichlet`.
   - Clause (iii) of their `G15RamG` is exactly `G11Out` (their proved
     `localUnram_of_unramifiedAt` does the global-to-local inertia step).
   - With their remaining Props (`G14TraceCompat`, clauses (i)-(ii) of `G15RamG`), their
     `modularConstituent_tail_G` gives `N`, `J`, `0 < N`, `IsJ1 N J`, `N ≤ QM²` and
     `CommonConstituent A (J.baseChange L')`.
5. **Output.** Together with step 1's `[L':ℚ] ≤ QM` and model, that is `ModularConstituent`. The
   remaining checks are `abVarEquiv` against `baseChange` (g0-mod-newform §3 step 4; probably
   definitional) and putting all three files into one environment (§6).

This file proves the same bridge as step 4 itself (`newformG12Out_of_galois`, with
`isConstituentOf_of_intertwines` and `panOutput_of_g12`), over its own copy of g0-mod-newform's
definitions (`G0Galois.NF`). It also proves `commonConstituent_of_sides` (G8's `e` plus a `J`-side
embedding gives `CommonConstituent`), an alternative to their `g13` for the last field.

### 4.2 What G14 and G15 still need from this range

- **G14.** g0-mod-newform's `G14TraceCompat D` compares traces of `r₃`, `r₅` at Frobenius elements
  outside `G_{L'}`. Its proof needs the descent link that `G8Out` keeps:
  `Intertwines (GlueDescent.rho Tm a β) r.mat e` on all of `G_ℚ`. `G12Spec` forgets it, so a proof
  of `G14TraceCompat` should take `G8Out` at 3 and 5 (with the points-level `m_σ` of `G7Data`), as
  their docstring says.
- **G15 (i)-(ii).** These concern ramification of `r_ℓ` at `p ∈ T`, and need the same link
  (`β`'s wild part, Raynaud on `V_ℓ(A)`).
- **Normalization (their review caveat 1).** Here Pan enters as `PkgI4.PanBerger`. It is already
  stated in the arithmetic-Frobenius trace form with a general continuous twist (its docstring
  derives this from Pan's geometric form with `ψ = ψ'ε^{1−k}`). The weight comparison and the
  determinant argument are then done in the same (Tate-module) normalization: R13's weights
  `{0, 1−k}` and R14Det's `det ρ_g = εχ^{k−1}`. Finiteness of `ψ` is derived (`g12Det_of`,
  `twist_finite`), not assumed. So `G12Out` holds in the reading their `PanOutput` needs.

## 5. Checks

- **Truth of the named Props.** Each was checked as a statement about the genuine objects (model
  check, no human review); the arguments are in the docstrings and §3. Two points:
  - `G8Matrix` first had `dim A = 2` as hypothesis. Then it is true but not provable without T26.
    It now takes `dim (ℚ̄_ℓ ⊗ V_ℓ(A)) = 4`, which `g8` proves from T26.
  - `G10Glue` needs `K` Galois over `ℚ`. Glazer's `L'` is Galois (N5 L711-712).
- **No vacuity from the inputs.** The input Props are satisfiable: with `c = ε = 1` on `G_{L'}`
  they are consistent, and the matrix units must commute with the Tate action, which the
  `B`-action does.
- **T11, T12 are opaque placeholders** in the bundle. `G10Glue` names them as inputs for
  documentation only; logically they carry no content.

## 6. Status of the files

- `scratch/g0-mod-galois/part_galois.lean` (502 lines): objects (`resQ` via `qEmb`/`res`,
  `Vb`, `tate`, `restrictRep`, `Intertwines`), the input and output Props, the five named glue
  Props, and the theorems `g8`, `g11`, `finitelyRamified_of_g11`, `isIrreducible_of_g8`, `g12`,
  `g8_g11`, `g8_g12`.
- `scratch/g0-mod-galois/part_matrix.lean` (87 lines): `BurnsideAbsIrred` and
  `g8Matrix_of_burnside`.
- `scratch/g0-mod-galois/part_det.lean`: `cycQ`, `R14Det`, `DetTate`, `ResQFiniteIndex`,
  `FrobeniusDenseQ` (with `frobeniusDenseQ_of` from the bundle's T18), the copied
  `eq_of_eq_on_arithFrob`, `det_fin_two_eq_trace` and `g12Det_of`.
- `scratch/g0-mod-galois/part_bundle.lean`: `GaloisPieces`,
  `g8_g12_of_leaves`, `JSide`, `commonConstituent_of_sides`, the copied newform interface
  (`NF.*`), `FiniteCharDirichlet`, `isConstituentOf_of_intertwines`, `panOutput_of_g12`,
  `newformG12Out_of_galois`.
- `ModGalois.lean` is generated (`build.sh`). It is g0-split's `Split.lean` followed by the four
  parts. The leaf statements (PanBerger, DeRhamComparison, EigenformHT, T23, the bundles) exist
  only in `Split.lean` (from `Leaves.lean`), not in `ZInQKernel/HDecomp/`.
- **Different environments.** g0-mod-field and g0-mod-newform compile over
  `ZInQKernel/HDecomp/` imports. The shared names (`PkgI3.AbVar`, `PkgI4.GaloisRep`,
  `GlueI3.repBaseChange`, `GlueDescent.MatrixUnits2`) are the same definitions in both. To
  assemble `ModularConstituent`, either move the three parts into one environment (the leaf
  statements into an HDecomp module), or copy the two partner parts after `Split.lean`.
