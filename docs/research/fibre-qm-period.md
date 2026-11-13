# fibre-qm-period: `FibreQMPeriod` reduced to the leaf's own triple and to named Props

Task fibre-qm-period, 2026-11-13. Base 2dd83306, with `origin/wip/qm-pin` and
`origin/wip/mobius-glue` merged in (g0-thetapoint was already in the base). Lean:
`scratch/fibre-qm-period/FibreQM.lean`, assembled by `build.sh` from three pieces:

- g0-thetapoint's `ThetaPoint.lean`, with qm-pin's full edit of `R1fpProps` applied;
- `part_pin.lean`, qm-pin's comparison lemmas copied verbatim;
- `part_fqm.lean`, the new section `HSyn.G0Split.FibreQM`.

Results log: `scratch/fibre-qm-period/log.md`. No file under `ZInQKernel/`, `blueprint/` or another
task's directory was edited. This is model work only; there has been no human review.

## 1. Result

**Verdict.** `ThetaPt.FibreQMPeriod` is true as far as model review can tell, and it is not
vacuous. The statement is unchanged; `fibreQMPeriod_iff` checks this by `Iff.rfl`. It is proved
in Lean, with no `sorry`, in three steps:

1. it is restated for the leaf's own triple;
2. that restatement is proved from named Props;
3. the large Props are split further.

Every `#print axioms` gives `[propext, Classical.choice, Quot.sound]` (VERIFIED, §5).

The finest form of the main theorem:

```lean
theorem HSyn.G0Split.FibreQM.fibreQMPeriod_of_leaves_glue (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsC)
    (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h))
    (hS : UnifStructure) (hL : QMLatticeAlgebra) (hG : PeriodMapGlue (ownY h) (ownΦ h) (ownπ h))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hT : UnifTransport) :
    ThetaPt.FibreQMPeriod
```

The coarser forms also compile:

- `fibreQMPeriod_of_named` takes `QMComplexUnif`, `QMPeriodValue` (own triple), `QMDenZeroCM3`,
  `UnifTransport`, `QMHauptmodul` and `MobiusGlue`.
- `fibreQMPeriod_of_parts` and `fibreQMPeriod_of_parts'` are intermediate forms.
- `fibreQMPeriod_of_named_all` needs no `MobiusGlue`, but needs the comparison for every triple.
- `fibreQMPeriod_of_named_rep` starts from the bundle form `LeafAdopt.R1R2fpRep`.

**Step 1: qm-pin's reduction (compiled).**

- `FibreQMPeriodAt Y Φ π` is the body of `FibreQMPeriod` for one triple.
- `FibreQMPeriodOwn h` is `FibreQMPeriodAt (ownY h) (ownΦ h) (ownπ h)`, for the triple that
  `Classical.choice` extracts from the bundle `R1R2fp` through `R1R2fp_Y`.
- `fibreQMPeriod_of_own : R1R2fp → MobiusGlue → FibreQMPeriodOwn h → FibreQMPeriod` instantiates
  qm-pin's `Pin.pointwise_of_witness_mor` with the predicate "every model `A` of the object `P`
  over `J(u)` satisfies the conclusion".
- `own_of_fibreQMPeriod` gives the converse.
- `Pin.MobiusGlue` is proved in `scratch/mobius-glue/MobiusGlue.lean` from `CurveRatFactor`,
  `CurveSurj` and the textbook leaf T5 (`mobiusGlue_of_curves`). That file is built on the kernel
  module `QM.Leaves`, so here `MobiusGlue` stays a hypothesis.

**Step 2: the own-triple statement from named Props (compiled, `fibreQMPeriodAt_of`).** Fix a triple
with `R1fpProps`, and a model `A/K` with `FibreOver` data `emb : K → ℚ̄`, `y`, `P`, `π(y) = J(u)`,
`A_ℚ̄ ≅ P.A`.

1. Fix `ι = IsAlgClosed.lift : ℚ̄ → ℂ`.
2. R1fp's naturality clause gives `Q/ℂ`, the base change of `P` along `ι`.
3. `QMComplexUnif` gives `τ ∈ ℍ` and an `ι`-compatible uniformization of `Q.A` with kernel exactly
   `Λ_τ`.
4. `UnifTransport` gives a uniformization of `A(ℂ)_{ι∘emb}` with the same kernel, so `F = id`.
5. `QMPeriodValue` gives `f(τ) = ι(π(y)) = J(u)`, where `f` is `QMHauptmodul`'s function.
6. `QMDenZeroCM3` and the `−3` clause of `QMHauptmodul` give `jDen(Ω(τ)) ≠ 0`, so
   `jNum/jDen(Ω(τ)) = f(τ) = J(u)` (`jRatio_of_value`).

**Step 3: the two large Props split further (compiled).**

- `QMPeriodValue ⇐ QMPeriodMap + HauptmodulUnique` (`qmPeriodValue_of`). This separates moduli
  theory from complex analysis.
- `QMPeriodMap ⇐ R1bFamily + PeriodMapGlue` (`qmPeriodMap_of`). `R1bFamily` is a concrete Lean
  statement of R1(b), the input the task names. It replaces, at the triple, the placeholder
  `HSyn.R01b_ComplexUniformization`, which is an `opaque … : Prop` and so carries no content.
- `QMComplexUnif ⇐ UniformizationExistsC + UnifStructure + QMLatticeAlgebra` (`qmComplexUnif_of`).
  The proof uses the new lemma `isUniformization_comp`: a uniformization composed with a linear
  automorphism `F⁻¹` is a uniformization with kernel `F(Λ)`.

## 2. The named Props

All of them are in namespace `HSyn.G0Split.FibreQM`, each a `def … : Prop` with a docstring
giving its step, sources and argument. Sizes are SPECULATIVE.

| Prop | kind | statement (informal) | sources / argument | size |
|---|---|---|---|---|
| `PkgI1.QMHauptmodul` | existing composite leaf (pkg-I1) | `j_θ∘Ω` is a normalized Hauptmodul of `Γ*` | Baba–Granath, Lin–Yang, Igusa | — |
| `UniformizationExistsC` | TEXTBOOK leaf | an abelian surface over `ℂ` has an analytic uniformization (`IsUniformization` at `id`) | Mumford §1 with GAGA (UNVERIFIED locators). bp-analytic's `UniformizationLeafAll` gives it for some `g`; `g = 2` is the missing identification | small |
| `R1bFamily Y Φ π` | LEAF (R1(b), family form, concrete) | a map `τ ↦ y_τ : ℍ → Y(ℂ)` whose object is `ι`-compatibly `ℂ²/ι(𝒪)(τ,1)ᵀ`, with `τ ↦ π(y_τ)` continuous and holomorphic into `P¹(ℂ)` (`IsR1bFamily`, `IsHolP1At`) | Shimura 1967 Main Thm I; Deligne 1971 §4.15 (UNVERIFIED locators). For the genuine `Y₃`: the published `φ : ℍ → V(ℂ)` composed with `π`. For other pinned triples: qm-pin's comparison (argued), so its truth does not depend on the choice | — (cited) |
| `UnifStructure` | GLUE | a uniformization's kernel is a full lattice; `End(A)` acts by a ring homomorphism `ρ` of `ℂ`-linear lifts preserving `Λ` | bp-analytic proves the lifting for its own form (`exists_complexLinear_endo`, `analyticRep_*`). Missing: converting this file's `IsUniformization` to bp-analytic's | small-medium |
| `QMLatticeAlgebra` | GLUE (one textbook input) | a full lattice in `ℂ²` stable under a ring homomorphism `ρ : 𝒪 → End_ℂ(ℂ²)` is `F⁻¹(Λ_τ)`, `τ ∈ ℍ`, with `Fρ(a) = ι(a)F` | Skolem–Noether over `ℂ` (in the kernel, `TSkolemKW`); class number one of `𝒪` (Eichler; Vignéras III.5.7, Voight 28.5.17, UNVERIFIED numbers); the unit `1+i` of norm `−1` moves `τ` into `ℍ` | medium |
| `QMPeriodValue Y Φ π` | GLUE (proved from the next two) | for `f` with `QMHauptmodul`'s clauses: `f(τ) = ι(π(y))` whenever the base change of the object at `y` is `ι`-compatibly `ℂ²/Λ_τ` | — | — |
| `PeriodMapGlue Y Φ π` | GLUE | for a family as in `R1bFamily`, `h = π∘y_τ` has `Γ*`-orbit fibres and the three CM values, and computes `ι(π(y))` at the period of `y` | GAGA; R2fp extended to `ℂ`-points; Shimura's description of isomorphisms of QM tori; CM: `ι(x)v_τ = λv_τ` makes `z ↦ λz` an `𝒪`-linear automorphism | large |
| `HauptmodulUnique` | GLUE (complex analysis) | a continuous `h : ℍ → P¹(ℂ)`, holomorphic into `P¹`, with `Γ*`-orbit fibres and the three CM values, equals `QMHauptmodul`'s `f` | `Γ*\ℍ` is compact (`B` is a division algebra); `h∘f⁻¹` is a homeomorphism of `P¹`, holomorphic off finitely many points, so a Möbius map fixing `0, ∞, −16/27`, so the identity | medium-large |
| `QMDenZeroCM3` | GLUE / leaf candidate | `Σθ_m⁸(Ω(τ)) = 0` only at fixed points of `ι(x)` with `x² − x + 1 = 0` | Lin–Yang's divisor of `ψ₄`; independently, the valence formula (§4) | small (given the valence formula) |
| `UnifTransport` | GLUE | a uniformization of `Q.A`, where `Q` is the base change of the fibre object along `ι`, gives one of `A(ℂ)_{ι∘emb}` with the same kernel | base change of complex points (pullback pasting); rigidity (Mumford §4 Cor. 1) to recentre the scheme isomorphism of `FibreOver`; translations are morphisms | medium |
| `Pin.MobiusGlue` | GLUE, **proved** in mobius-glue from two curve facts and T5 | `π' = π∘g` on `ℚ̄`-points | qm-pin §3.2, mobius-glue | done (other file) |

Proved here (Lean, `part_fqm.lean`):

- `fibreQMPeriod_iff` and `qmHauptmodul_iff`, both by `Iff.rfl`;
- `fibreQMPeriod_of_own` and `own_of_fibreQMPeriod`;
- `jRatio_of_value`, `fibreQMPeriodAt_of` and `fibreQMPeriodOwn_of`;
- `isUniformization_comp`, `qmComplexUnif_of`, `qmPeriodValue_of` and `qmPeriodMap_of`;
- the main theorems listed in §1.

## 3. Checks on the statement and on the new Props

These are model checks unless marked otherwise.

- **Verbatim (VERIFIED, Lean).** `FibreQMPeriodAt` is the body of `FibreQMPeriod` (`Iff.rfl`).
  `QMHauptmodulFn` is the body of `PkgI1.QMHauptmodul` (`Iff.rfl`).
- **Which `R1fpProps`.** This file uses qm-pin's fully repaired list, with `R1famProps` and
  `R1univProps` as conjuncts 5 and 6. qm-pin recommends that edit for integration, and the
  own-triple reduction needs it. g0-thetapoint's file has the old list. Under the old list, for an
  exotic relabelled triple, `FibreOver … u K A` could be the fibre over some other value. The
  truth of `FibreQMPeriod` would then depend on qm-pin §6's open question: whether two rational
  fibres of `Y₃ → P¹` are ever `ℚ`-isomorphic. With the repaired list, the truth does not depend
  on that question.
- **Not vacuous.** The hypotheses are those of g0-split's other pieces. The conclusion is
  existential, and its witnesses are genuine: an analytic uniformization, `τ ∈ ℍ`, the identity
  map, and bp-analytic's `qmLattice`.
- **Universal `f` in `QMPeriodValue` and `HauptmodulUnique`.** Quantifying over every `f` with
  `QMHauptmodul`'s clauses costs nothing, because such an `f` is unique. It is continuous and
  equals `jNum/jDen∘Ω` off the zeros of `jDen∘Ω`, a discrete set by `QMDenZeroCM3`.
- **`ι`-compatibility is needed.** Without it, `QMPeriodValue` would claim `f(τ) = ι(π(y))` for any
  lattice isomorphic to the torus. A non-`ι`-compatible isomorphism transports `ι` to another
  embedding `𝒪 → End`. On the CM locus that embedding need not be conjugate by `Aut 𝒪`, so the
  hypothesis is kept.
- **Orientation of the action.** Points act on the right (`P ↦ P ≫ e`), and `endPt` is a ring
  homomorphism. So `Φ(ι(a)z) = Φ(z) ≫ ι_Q(a)` is a left action on both sides, consistent with
  `ι(ab) = ι(a)ι(b)` (VERIFIED by reading `endPt`).
- **The order.** `LeafQM.O` (`ofInt n = n₀ + n₁i + n₂(1+j)/2 + n₃(i+ij)/2`) has the same basis as
  pkg-I1's and bp-analytic's `oBasis`. `LeafQM.B`, `PkgI1.B` and `BPAnalytic.QM.B` are all
  `QuaternionAlgebra ℚ 2 0 (-3)` (VERIFIED by reading; `qmMat` typechecks).
- **CM normalization.** The fixed point of `ι(x)` with `x² = −1` gives `ℂ²/Λ_τ` the automorphism
  `z ↦ λz`, with `λ² = −1`, commuting with `ι(𝒪)`: `λι(y)v_τ = ι(yx)v_τ ∈ Λ_τ`. That is `HasCM4`.
  The same holds for `−3` and `−24`. So `QMHauptmodul`'s and R2fp's CM clauses refer to the same
  points.
- **`QMComplexUnif` is true for all of `QML3 ℂ`.** `QML3` carries no polarization, but a QM
  surface over `ℂ` has `H₁ ≅ 𝒪` (class number one), and the analytic representation is `ι` up to
  `GL₂(ℂ)`. If `Im τ < 0`, the unit `u = 1+i` (with `u⁻¹ = −1+i ∈ 𝒪` and `nrd u = −1`) gives
  `ι(𝒪)v_τ = ι(𝒪)ι(u)v_τ`, and `ι(u)v_τ ∝ (τ', 1)` with `τ' = −(1+√2)²τ ∈ ℍ`.

## 4. Numerical check of `QMDenZeroCM3`

The script is `scratch/fibre-qm-period/py/psi4_zeros.py`, with output `psi4_zeros_out.txt`. It
uses mpmath at 40 digits and re-implements `Ω(τ)` from pkg-I1's definitions.

Let `S = Σ_{m even} θ_m⁸ ∘ Ω` (which is `jDen^{1/5}`), `P = ∏_{m even} θ_m² ∘ Ω`, and
`dF(τ) = (τ−3)(τ+1)`, which is proportional to `det F'(τ)` (`QMLattice.det_Fp`).

1. **Weights (VERIFIED numerically).** For `γ = ι((1+j)/2)`, `ι(i+j)`, `ι(3+2i)` and two values of
   `τ`, the following hold to at least 9 digits:
   - `|S(γτ)/S(τ)| = |cτ+d|⁸ |dF(τ)/dF(γτ)|⁴`;
   - `|P(γτ)/P(τ)| = |cτ+d|²⁰ |dF(τ)/dF(γτ)|¹⁰`.

   So `S·dF⁴` and `P·dF¹⁰` behave like automorphic forms of weight 8 and 20 for `Γ*`, in absolute
   value. `S` itself is not of weight 8: the `dF` factor is the normalization `F'(τ)` of the
   symplectic basis.
2. **Orders (VERIFIED numerically).**
   - At the `−3` point `i√3`: `ord S = 2` and `ord P = 2`.
   - At the `−4` point `√2+i`: `ord S = 0` and `ord P = 2`.
   - At the `−24` point `4.1815…i`: both orders are 0.
3. **Valence formula (STANDARD).** For a cocompact Fuchsian group of signature `(0; 2, 4, 6)`
   (Baba–Granath §3.1, as quoted in the file), a holomorphic weight-`k` form has
   `Σ ord_P/e_P = (k/2)(−2 + 1/2 + 3/4 + 5/6) = k/24`.
   - For `k = 8` the budget is `1/3 = 2/6`. The order-2 zero at the order-6 point `P₋₃` uses all of
     it, so `S∘Ω` has no other zero on `ℍ`. That is `QMDenZeroCM3`.
   - For `k = 20` the budget is `5/6 = 2/6 + 2/4`, which matches the orders found for `P`.
   - This also fits pkg-I1's observation of a pole of `j_θ` of order 6 at `i√3`
     (`2·2·2 − 5·2 = −6`) and Lin–Yang's picture: one pole at `P₋₃`, one zero at `P₋₄`.

So `QMDenZeroCM3` follows from three ingredients: the published signature, the textbook valence
formula, and a weight and an order that are numerical, not proved. The weight follows from R4
(`ThetaModularity`) and the modular embedding `γ ↦ M_γ ∈ Sp₄(ℤ)`; that part is glue.

## 5. Lean outcomes (all VERIFIED; outputs in `scratch/fibre-qm-period/run_*.txt`)

| run | file | outcome |
|---|---|---|
| prereq | `lake build ZInQKernel.HDecomp.Analytic.QMLattice ZInQKernel.Hypotheses.JHeight` | OK, 2m0s |
| run_base | `FQMBase.lean` (ThetaPoint + qm-pin full edit + `part_pin`, 20634 lines) | 0 errors, 2m52s |
| run_dev2-5 | `Dev.lean` = `import FQMBase` + `part_fqm.lean` (olean of the base via `lean -o`) | 0 errors, about 5s each; 16 axioms lines standard |
| run_full1 / run_full2 | `FibreQM.lean` (assembled), `lake env lean` | 0 errors, no `sorry`; every axioms line of §F standard (run_full2 is the final file) |

To reproduce, run from the repository root:

- `scratch/fibre-qm-period/build.sh`, then `lake env lean scratch/fibre-qm-period/FibreQM.lean`;
- before that, build the prerequisites in the table.

`FQMBase.lean` is regenerated by `build.sh` and is not committed.

## 6. Integration notes

- `part_fqm.lean` needs qm-pin's full edit of `R1fpProps` (`QM-Leaves-full.patch` and
  `Split-full.patch`) and the qm-pin `Pin` lemmas in `part_pin.lean`, which qm-pin proposes as
  `ZInQKernel/HDecomp/QM/Pin.lean`.
- `R1bFamily` is a concrete replacement for the placeholder `HSyn.R01b_ComplexUniformization`, at
  the leaf's triple. In a bundle it would be the clause `R1bFamily Y Φ π` on the triple of
  `R1R2fpRep` (with `π = π₆ ∘ fY`). It should then be classified as a leaf, with the
  "qualified consequence" caveat of R1 and the SPECULATIVE premise bp-qmmoduli §2.2.
- `QMComplexUnif` (R1(b)(a)) is no longer needed as a leaf: it is proved from
  `UniformizationExistsC`, `UnifStructure` and `QMLatticeAlgebra`.

## 7. What remains

- **Glue to formalize:**
  - `PeriodMapGlue` (large: GAGA, R2fp on `ℂ`-points, isomorphisms of QM tori);
  - `HauptmodulUnique` (medium-large, pure complex analysis, statable over Mathlib now);
  - `UnifTransport` (medium: scheme bookkeeping and rigidity);
  - `QMLatticeAlgebra` (medium: algebra, with class number one);
  - `UnifStructure` (small-medium: a bridge to bp-analytic);
  - `QMDenZeroCM3` (valence formula and the weight and order inputs).
- **Leaves to check by a human:**
  - `R1bFamily`: the faithfulness of the family form to Shimura's Main Theorem I, and the transfer
    to pinned triples;
  - `UniformizationExistsC`.
- No human review has been done. Like every leaf-qm-fp object, the Shimura-curve inputs inherit
  the SPECULATIVE premise bp-qmmoduli §2.2.
