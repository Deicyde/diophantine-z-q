# infra-smooth-dim: dimension theory of smooth schemes over a field

Task infra-smooth-dim, 2026-11-13. Base f90cf864 (origin/wip/integrate-w38b), with
origin/wip/mul-rigidity (60a480e0) merged. Scratch: `scratch/infra-smooth-dim/` (results log
`log.md`). No file under `ZInQKernel/` or `blueprint/` was edited, and no other task's notes or
scratch files. This is model work; no human has reviewed it.

Marks: **VERIFIED** means compiled, or read in Mathlib's or the kernel's sources. **STANDARD** means
a textbook fact. **UNVERIFIED** marks a locator recalled from memory (there is no network here).

## 0. Main result

**For `X` smooth of relative dimension `n` over a field `K` and `x` a closed point of `X`, the local
ring `𝒪_{X,x}` is regular of Krull dimension `n`, and `dim_{κ(x)} 𝔪_x/𝔪_x² = n`. If `X` is also
irreducible, then `dim X = n`.** This is proved in Lean from Mathlib v4.35 alone, with no sorry and
only the axioms `propext`, `Classical.choice`, `Quot.sound` (VERIFIED: compiled, `#print axioms`).

This closes **every glue Prop that the task names as blocked**. Each is proved against its own
statement, unchanged:

| Prop | Origin | Status | Lean |
| --- | --- | --- | --- |
| `LeafQM.AV.Pin.SmoothStalkDimOne` (C1b) | curve-facts | **proved** | `smoothStalkDimOne` (SmoothDimProps.lean; CurveFactsClosed.lean, which uses curve-facts' own file) |
| `ZInQ.DefFaltings.HodgeLattice.RegularAtOrigin` (V1) | hodge-lattice, kernel `HDecomp/Faltings/HodgeLattice.lean` | **proved** | `regularAtOrigin` |
| `ZInQ.DefFaltings.HodgeLattice.DimAtOrigin` (V2) | same | **proved** | `dimAtOrigin` |
| `ZInQ.DefFaltings.HodgeLattice.TangentDimAtOrigin` (V) | same | **proved** | `tangentDimAtOrigin` |
| `ZInQ.DefFaltings.HodgeLattice.DimBaseChange` | same | **proved** (g0-dim's lemma, applied to the kernel's statement) | `dimBaseChange` |
| **`ZInQ.DefFaltings.HodgeLatticeTheorem`** (the algebraic third of AN3) | kernel `HDecomp/Faltings/Models.lean` | **proved, with no hypotheses** | `hodgeLatticeTheorem` (HodgeLatticeClosed.lean) |
| mul-rigidity's dimension input `QuasiFiniteEndSurjective` | mul-rigidity | already a theorem there (VERIFIED, docs/research/mul-rigidity.md) | (none needed) |

Downstream consequences that also compile (VERIFIED):
- curve-facts: C1a `SmoothCurveNoIsolatedPoint` and C1 `GeomCompInfinite` now hold outright, and
  `curveFacts_of_C2K_C3K : ConstOrOntoAlgClosed → RatFactorAlgClosed → CurveRatFactor ∧ CurveSurj`.
  So the two curve facts rest on the textbook leaf C2K (Hartshorne II.6.8, UNVERIFIED numbering) and
  the glue C3K only.
- `HodgeLatticeTheorem` is one of the three Props that the kernel's docstrings
  (`HDecomp/Faltings/Height.lean`, `stableFaltingsHeight`; Leaves.lean, leaf-adopt) list as needed to
  make the index set of the stable-height infimum nonempty. The other two,
  `AnalyticUniformizationExists` and `AnalyticUniformizationUnique`, remain open.

## 1. The general lemmas (Mathlib-only; all VERIFIED)

Namespace `InfraSmoothDim`. There is one file per layer; later files repeat earlier ones verbatim
because scratch files cannot import each other.

**`MaxHeight.lean`**
- `height_isMaximal_mvPolynomial`: for a field `k`, a finite `ι` and `M` maximal in `k[x_ι]`,
  `M.height = |ι|`. The proof is by induction on `ι` through `Option`. It uses the
  `Polynomial`/`MvPolynomial` equivalence and Mathlib's dimension of polynomial rings.

**`CotQuot.lean`**
- `spanFinrank_add_card_le`: let `B` be a Noetherian local ring, `C` local, and `ψ : B → C` with
  `𝔪_B C = 𝔪_C`, and let `ψ` kill `f : σ → 𝔪_B`, where the `f_i` have linearly independent classes
  in `𝔪_B/𝔪_B²`. Then `spanFinrank 𝔪_C + |σ| ≤ spanFinrank 𝔪_B`. This says that killing part of a
  minimal generating system lowers the embedding dimension.

**`StdSmoothLocal.lean`**
- `linearIndependent_relCot`: let `P` be a submersive presentation `S = k[x_ι]/(f_σ)` with
  invertible Jacobian, and `M ⊇ ker` a maximal ideal. Then the classes of the `f_i` in `𝔪/𝔪²` of
  `k[x]_M` are linearly independent over `κ`. The proof takes the derivative of a relation
  `∑ c_i f_i ∈ M²` and reduces the Jacobian modulo `M`. It goes through `derivation_mem_of_mem_sq`,
  `jacobiMatrix_det_notMem`, `coeffs_mem_of_sum_mem_sq` and `sum_mem_sq_of_cotangent`. One
  monolithic version hit a kernel deterministic timeout; splitting it into three lemmas fixed that.
- **`ringKrullDim_and_spanFinrank_localization`**: for a submersive presentation `P` of `S` over a
  field and a maximal ideal `𝔪` of `S`, `ringKrullDim S_𝔪 = P.dimension` and
  `spanFinrank 𝔪S_𝔪 = P.dimension`. The proof:
  - Lower bound: Krull's height theorem (`Ideal.height_le_height_add_spanFinrank_of_le`) with
    `ht M = |ι|`.
  - Upper bound: `k[x]_M` is regular (`MvPolynomial.isRegularRing_of_isRegularRing`), so its
    embedding dimension is `|ι|`. `CotQuot` lowers it by `|σ|`. Then
    `ringKrullDim_le_spanFinrank_maximalIdeal` finishes.

**`SmoothStalk.lean`** (§0-§3 are StdSmoothLocal verbatim; §4 is the scheme layer)
- `stalk_dim_of_chart`: the local form on an affine chart where `f.appLE` is standard smooth of
  relative dimension `n`. It is transported along `IsAffineOpen.isLocalization_stalk`.
- **`stalk_dim_of_smoothOfRelativeDimension`**: if `[SmoothOfRelativeDimension n f]` with
  `f : X ⟶ Spec K` and `x` is closed, then `ringKrullDim 𝒪_{X,x} = n ∧ spanFinrank 𝔪_x = n`.
- `exists_stalk_dim_of_smooth`: the same for `[Smooth f]`, with some `n`.
- `exists_nbhd_stalk_dim`: around each point there is an open set on which all closed points have
  the same `n`.
- `stalk_dim_eq_of_closed`: on an irreducible smooth `X`, all closed points have equal stalk
  dimension. The proof uses Jacobson density, `nonempty_inter_closedPoints`.
- **`topologicalKrullDim_eq_of_smooth`**: for an irreducible smooth `X` and a closed point `x`,
  `dim X = dim 𝒪_{X,x} = spanFinrank 𝔪_x`. It uses Mathlib's `ringKrullDim_stalk_eq_coheight`.
- Corollaries:
  - `isRegularLocalRing_stalk_of_smooth`;
  - `finrank_cotangentSpace_of_smoothOfRelativeDimension` (`finrank_{κ(x)} 𝔪_x/𝔪_x² = n` at closed
    points);
  - `isClosed_of_section` (a `K`-point is closed);
  - **`stalk_dims_of_section`** (at a `K`-point `s`, `dim 𝒪 = n` and the cotangent space has
    dimension `n`);
  - **`topologicalKrullDim_eq_of_smoothOfRelativeDimension`** (irreducible, relative dimension `n`
    ⇒ `dim X = n`).

## 2. The Props

- **`SmoothDimProps.lean`** (imports Mathlib + `ZInQKernel.HDecomp.Objects`). It contains
  SmoothStalk §0-§4, then the four Props copied verbatim (`SmoothStalkDimOne`, `originPt`,
  `RegularAtOrigin`, `DimAtOrigin`, `TangentDimAtOrigin`) and their proofs. A text comparison
  checked the statements against the source files. The origin is a closed point because the unit
  section is a closed immersion (`isClosedImmersion_of_comp_eq_id`). An abelian variety is
  irreducible (`GeometricallyIrreducible.irreducibleSpace_of_subsingleton`). Then
  `topologicalKrullDim_eq_of_smooth` gives all three hodge-lattice facts at once.
- **`HodgeLatticeClosed.lean`** (imports Mathlib + `ZInQKernel.HDecomp.Faltings.HodgeLattice`).
  It does **not** copy the statements: it proves the kernel's own `RegularAtOrigin`, `DimAtOrigin`,
  `DimBaseChange` and `TangentDimAtOrigin`, and then
  `hodgeLatticeTheorem := hodgeLatticeTheorem_of_abVarFacts regularAtOrigin dimAtOrigin dimBaseChange`.
  §5 copies g0-dim's §1-§2 verbatim (`G0Dim.dim_baseChange`).
- **`CurveFactsClosed.lean`** (imports Mathlib + `ZInQKernel.HDecomp.QM.Pairs` + Lagrange). It
  contains curve-facts' `CurveFacts.lean` verbatim (without its imports and `#print` lines), then
  SmoothStalk §0-§4, then C1b, C1a, C1 and `curveFacts_of_C2K_C3K`.

The files are generated from the parts by `assemble.py`. Compile times are 10-50 s each.

## 3. What remains (not part of this task, or out of reach in the time)

- **mul-rigidity**: its remaining glue `KerUnitOpenOfCotangentSurj` and `CotangentMulN` are not
  dimension theory.
  - The first needs the local ring of the fibre `ker f` at the origin, which means stalks of a
    pullback in Mathlib.
  - The second needs the group law to first order: the cotangent map of `μ ∘ (f, g)`.
  - Neither is touched here.
- **`MetrizationDimUnique`** (a GluePieces2 field). Its intended proof has two parts:
  - (a) `finrank (hodgeSpace g) = C(dim A, g)`. With `CotangentRank` now unconditional, this still
    needs base change of exterior powers, which Mathlib v4.35 lacks (hodge-lattice §0).
  - (b) excluding `g = 0` when `dim A ≥ 1`. This needs `A_τ(ℂ)` to have more than one point. The
    Jacobson and dimension part is available now (`topologicalKrullDim_eq_of_smooth`: one closed
    point ⇒ dimension 0); the identification of `model.Pts τ` with closed points of `A_ℂ` is not
    done.
- **e1-sub**: `dim (A' × Z) = dim J` for an isogeny needs "finite surjective preserves dimension".
  That is an integral-extension argument (g0-dim's `ringKrullDim_eq_of_isIntegral_of_injective`) on
  an affine cover. It is not done.
- **Integration**: `HodgeLatticeClosed.lean` §6 and `SmoothStalk.lean` §0-§4 are ready to become a
  kernel module, e.g. `ZInQKernel/HDecomp/Faltings/HodgeLatticeProved.lean` importing a Mathlib-only
  `ZInQKernel/HDecomp/SmoothDim.lean`. `CurveFactsClosed.lean` §6 can join curve-facts once
  curve-facts is integrated.
