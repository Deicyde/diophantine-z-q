# fibre-qm-period: `FibreQMPeriod` reduced to the leaf's own triple and then to named Props

Task fibre-qm-period, 2026-11-13. Base 2dd83306 merged with `origin/wip/qm-pin` and
`origin/wip/mobius-glue`; g0-thetapoint was already in the base.

Lean file: `scratch/fibre-qm-period/FibreQM.lean`. `build.sh` assembles it from three pieces:
- g0-thetapoint's `ThetaPoint.lean`, with qm-pin's full edit of `R1fpProps` applied;
- `part_pin.lean`, qm-pin's comparison lemmas, copied verbatim;
- `part_fqm.lean`, this task's sections `FibreQMNorm` and `HSyn.G0Split.FibreQM`.

Results log: `scratch/fibre-qm-period/log.md`. No file under `ZInQKernel/`, `blueprint/` or another
task's directory was edited. Model work only, no human review.

## 1. Result

**Verdict.** As far as model review can tell, `ThetaPt.FibreQMPeriod` is true and not vacuous.
Its statement is unchanged: `fibreQMPeriod_iff` holds by `Iff.rfl`. It is proved in Lean, with no
`sorry`, in two steps:
- it is restated for the leaf's own triple (qm-pin's reduction);
- the restated form is proved from named Props.

Every `#print axioms` gives `[propext, Classical.choice, Quot.sound]` (VERIFIED, §6). The final form:

```lean
theorem HSyn.G0Split.FibreQM.fibreQMPeriod_main (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hCN : QMClassNumberOne)
    (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h)) (hG : PeriodMapGlue (ownY h) (ownΦ h) (ownπ h))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hCP : CPtsTransport) :
    ThetaPt.FibreQMPeriod
```

The hypotheses fall into three groups.

- **Leaves.**
  - `PkgI1.QMHauptmodul`: existing composite leaf.
  - T35 `UniformizationExistsT35` and T11a `T11aRiemannEnd`: verbatim copies of the kernel's textbook
    leaves, already in leaf-adopt3's `TextbookLeaves`.
  - `QMClassNumberOne`: textbook (Eichler class number one, lattice form).
  - `R1bFamily`: R1(b) in family form, stated concretely.
- **Glue.**
  - `Pin.MobiusGlue`: already proved by mobius-glue.
  - `PeriodMapGlue`, `HauptmodulUnique`, `QMDenZeroCM3`, `CPtsTransport`: open.
- **The bundle `R1R2fp`**, which supplies the triple.

Skolem–Noether over `ℂ` for N5's order (`QMSkolemNoetherC`) is **proved** here
(`qmSkolemNoetherC_proof`), so it is no longer a hypothesis.

Coarser forms also compile, each with fewer, larger Props: `fibreQMPeriod_of_named`,
`fibreQMPeriod_of_parts`, `fibreQMPeriod_of_textbook`, `fibreQMPeriod_final`,
`fibreQMPeriod_final'`, `fibreQMPeriod_final''` (which still takes `QMSkolemNoetherC`),
`fibreQMPeriod_of_named_all` (no `MobiusGlue`, comparison for every triple), and
`fibreQMPeriod_of_named_rep` and `fibreQMPeriod_main_rep` (both from `LeafAdopt.R1R2fpRep`).

### Step 1: qm-pin's reduction (compiled)

- `FibreQMPeriodAt Y Φ π` is the body of `FibreQMPeriod` for one triple.
- `FibreQMPeriodOwn h := FibreQMPeriodAt (ownY h) (ownΦ h) (ownπ h)` uses the triple that
  `Classical.choice` takes from `R1R2fp` (through `R1R2fp_Y`).
- `fibreQMPeriod_of_own : R1R2fp → MobiusGlue → FibreQMPeriodOwn h → FibreQMPeriod` instantiates
  `Pin.pointwise_of_witness_mor` with the predicate "every model `A` of the object `P` over `J(u)`
  satisfies the conclusion". The CM objects come from `Pin.cm_objects_of_R1R2fp`.
- `own_of_fibreQMPeriod` is the converse.

### Step 2: the own-triple statement (compiled, `fibreQMPeriodAt_of`)

Fix a triple with `R1fpProps`; only its naturality clause is used. Fix `FibreOver` data:
`emb : K → ℚ̄`, `y`, `P`, `π(y) = J(u)`, `A_ℚ̄ ≅ P.A`.

1. `ι = IsAlgClosed.lift : ℚ̄ → ℂ`, and R1fp naturality gives the base change `Q/ℂ` of `P`.
2. `QMComplexUnif` gives `τ ∈ ℍ` and an `ι`-compatible uniformization of `Q.A` with kernel exactly
   `Λ_τ`.
3. `UnifTransport` gives a uniformization of `A(ℂ)_{ι∘emb}` with kernel `Λ_τ`, so we may take
   `F = id`.
4. `QMPeriodValue` gives `f(τ) = ι(π(y)) = J(u)`, where `f` is `QMHauptmodul`'s function.
5. `QMDenZeroCM3` and the `−3` clause of `QMHauptmodul` give `jDen(Ω(τ)) ≠ 0`, so
   `jNum/jDen(Ω(τ)) = J(u)` (`jRatio_of_value`).

### Step 3: the intermediate Props reduced (all compiled)

- `QMPeriodValue ⇐ QMPeriodMap + HauptmodulUnique` (`qmPeriodValue_of`).
- `QMPeriodMap ⇐ R1bFamily + PeriodMapGlue` (`qmPeriodMap_of`). `R1bFamily` is a concrete Lean
  statement of R1(b). It replaces, at the triple, the placeholder
  `HSyn.R01b_ComplexUniformization`, which is an `opaque` Prop with no content.
- `QMComplexUnif ⇐ T35 + T11a + QMLatticeAlgebra` (`qmComplexUnif_of_textbook`). Proved along the
  way:
  - `isUniformization_comp`: a uniformization composed with `F⁻¹` is a uniformization with kernel
    `F(Λ)`;
  - `lift_unique`: two linear lifts with the same image are equal, because `ℝ` is connected and `Λ`
    is discrete;
  - `unif_ring_hom`: T11a's lifts form a ring homomorphism `End(A) → End_ℂ(ℂ²)` that preserves `Λ`.
- `QMLatticeAlgebra ⇐ QMLatticeFree` (`qmLatticeAlgebra_of_free`), via `FibreQMNorm.normalize`
  (proved):
  - if `w` is not a complex multiple of a real vector, then `ι(𝒪)w = c·Λ_τ` with `c ≠ 0` and
    `τ ∈ ℍ`;
  - when `Im(w₀/w₁) < 0`, the unit `1 + i` (reduced norm `−1`) moves `τ` into `ℍ`
    (`qmOrbit_unit`: eight vector identities over `ℚ(√2)`, with coefficients computed by
    `py/unit_coeffs.py`).
- `QMLatticeFree ⇐ QMSkolemNoetherC + QMClassNumberOne` (`qmLatticeFree_of`). The lattice is
  transported by Mathlib's `ZLattice.comap` along `G⁻¹`.
- `QMSkolemNoetherC` is proved (`qmSkolemNoetherC_proof`). Put `R = ρ(i)`, `S = ρ(j)`, so
  `R² = 2`, `S² = −3` and `RS = −SR`.
  - `R` has an eigenvector `e₁` for `√2`; otherwise `R = −√2`, which forces `S = 0`.
  - `e₂ = Se₁` is an eigenvector for `−√2`, and `e₁, e₂` are independent.
  - In the basis `(e₁, e₂)`, `R` and `S` are N5's `ι(i)` and `ι(j)`.
  - Every `a ∈ 𝒪` is `(2n₀ + 2n₁i + n₂(1+j) + n₃(i+ij))/2`, so the intertwining extends to all
    of `𝒪`.
- `UnifTransport ⇐ CPtsTransport` (`unifTransport_of`): `Φ_A = ψ ∘ Φ_Q`.

## 2. The named Props of the final form

All are in namespace `HSyn.G0Split.FibreQM`, each a `def … : Prop` with a docstring giving its
step, sources and argument. Sizes are SPECULATIVE.

| Prop | kind | statement (informal) | sources / argument | size |
|---|---|---|---|---|
| `PkgI1.QMHauptmodul` | existing composite leaf (pkg-I1) | `j_θ∘Ω` is a normalized Hauptmodul of `Γ*` | Baba–Granath, Lin–Yang, Igusa | — |
| `UniformizationExistsT35` | TEXTBOOK leaf T35 (verbatim kernel copy) | `A(ℂ)_σ ≅ ℂ^g/Λ` by an analytic uniformization, `Λ` a full lattice | Mumford §1, GAGA | — |
| `T11aRiemannEnd` | TEXTBOOK leaf T11a (verbatim kernel copy) | endomorphisms of `A/ℂ` are exactly the `Λ`-preserving linear maps of `ℂ^g` | Mumford §§1-2, Birkenhake–Lange 1.2.1, GAGA | — |
| `QMSkolemNoetherC` | **proved** (`qmSkolemNoetherC_proof`) | every unital ring homomorphism `ρ : 𝒪 → End_ℂ(ℂ²)` is conjugate to N5's `ι` | eigenvector argument (Step 3) | done |
| `QMClassNumberOne` | TEXTBOOK | every `ι(𝒪)`-stable full lattice in `ℂ²` is `ι(𝒪)w`, with `w` not a complex multiple of a real vector | Eichler: the maximal order of the indefinite algebra of discriminant 6 has class number one (Vignéras III.5.7, Voight 28.5.17, UNVERIFIED numbers) | medium |
| `R1bFamily Y Φ π` | LEAF (R1(b), family form, concrete) | `τ ↦ y_τ : ℍ → Y(ℂ)` whose object is `ι`-compatibly `ℂ²/ι(𝒪)(τ,1)ᵀ`, with `τ ↦ π(y_τ)` continuous and holomorphic into `P¹(ℂ)` (`IsR1bFamily`, `IsHolP1At`) | Shimura 1967 Main Thm I; Deligne 1971 §4.15 (UNVERIFIED locators). Genuine `Y₃`: Shimura's `φ : ℍ → V(ℂ)` composed with `π`. Other pinned triples: qm-pin's comparison (argued), so truth does not depend on the choice | — |
| `PeriodMapGlue Y Φ π` | GLUE | for such a family, `h = π∘y_τ` has `Γ*`-orbit fibres and the three CM values, and `h(τ) = ι(π(y))` when the base change of the object at `y` is `ι`-compatibly `ℂ²/Λ_τ` | GAGA; R2fp on `ℂ`-points; Shimura's description of isomorphisms of QM tori; CM: `ι(x)v_τ = λv_τ` makes `z ↦ λz` an `𝒪`-linear automorphism | large |
| `HauptmodulUnique` | GLUE (complex analysis) | a continuous `h : ℍ → P¹(ℂ)`, holomorphic into `P¹`, with `Γ*`-orbit fibres and the three CM values, is `QMHauptmodul`'s `f` | `Γ*\ℍ` is compact; `h∘f⁻¹` is a homeomorphism of `P¹`, holomorphic off finitely many points, hence a Möbius map fixing `0, ∞, −16/27`, hence the identity | medium-large |
| `QMDenZeroCM3` | GLUE (argued, numerics) / leaf candidate | `Σθ_m⁸(Ω(τ)) = 0` only at fixed points of `ι(x)`, `x² − x + 1 = 0` | Lin–Yang's divisor of `ψ₄`; independently the valence formula (§4) | small, given the valence formula |
| `CPtsTransport` | GLUE | a group isomorphism `Q.A(ℂ) ≅ A(ℂ)_{ι∘emb}` compatible with regular functions | base change of points (pullback pasting with `FibreOver` and `IsBaseChangeOf`); rigidity (Mumford §4 Cor. 1) to recentre; translations are morphisms | medium |
| `Pin.MobiusGlue` | GLUE, **proved** in mobius-glue | `π' = π∘g` on `ℚ̄`-points | `mobiusGlue_of_curves` (from `CurveRatFactor`, `CurveSurj`, T5) | done (other file) |

**Proved in this task.** All of the following are in `part_fqm.lean` and compiled:
- the `Iff.rfl` checks `fibreQMPeriod_iff` and `qmHauptmodul_iff`;
- `fibreQMPeriod_of_own`, `own_of_fibreQMPeriod`, `jRatio_of_value`, `fibreQMPeriodAt_of`,
  `fibreQMPeriodOwn_of`;
- `isUniformization_comp`, `uniformizationExistsC_of`, `lift_unique`, `unif_ring_hom`,
  `qmComplexUnif_of`, `qmComplexUnif_of_textbook`;
- `oI_sq`, `oJ_sq`, `oI_oJ`, `two_mul_eq`, `two_qmMat`, `qmSkolemNoetherC_proof`;
- `qmPeriodValue_of`, `qmPeriodMap_of`;
- `FibreQMNorm.qmLattice_eq_orbit`, `gen_eq`, `qmOrbit_smul`, `qmOrbit_unit`, `smulMap_comp`,
  `normalize`;
- `qmLatticeAlgebra_of_free`, `qmLatticeFree_of`, `unifTransport_of`;
- the main theorems.

**Intermediate named Props, now proved from the above.** `QMComplexUnif` (R1(b)(a)),
`QMPeriodValue`, `QMPeriodMap`, `QMLatticeAlgebra`, `QMLatticeFree`, `UnifTransport`,
`UniformizationExistsC`. `UnifStructure` is not used by the final form; T35 and T11a replace it.

## 3. Checks on the statement and on the new Props

These are model checks unless marked otherwise.

- **Verbatim (VERIFIED, Lean and Python).**
  - `FibreQMPeriodAt` is the body of `FibreQMPeriod` (`Iff.rfl`).
  - `QMHauptmodulFn` is the body of `PkgI1.QMHauptmodul` (`Iff.rfl`).
  - The copies of T35 and T11a equal the kernel's text once the `PkgI3.` prefix is dropped
    (whitespace-normalized comparison).
- **Which `R1fpProps`.** This file uses qm-pin's fully repaired list (`R1famProps` and
  `R1univProps` as conjuncts 5 and 6). qm-pin recommends that edit for integration, and the
  own-triple reduction needs it. g0-thetapoint's file has the old list. Under the old list, for an
  exotic relabelled triple, `FibreOver … u K A` could pick out the fibre over another value. The
  truth of `FibreQMPeriod` would then hinge on qm-pin §6's open question: are two rational fibres
  of `Y₃ → P¹` ever `ℚ`-isomorphic? Under the repaired list it does not.
- **Not vacuous.** The hypotheses are those of g0-split's other pieces. The conclusion's
  existentials are witnessed by genuine objects: an analytic uniformization, `τ ∈ ℍ`, the
  identity, and bp-analytic's `qmLattice`.
- **Quantifying over every `f` costs nothing.** `QMPeriodValue` and `HauptmodulUnique` quantify
  over every `f` with `QMHauptmodul`'s clauses. Such an `f` is unique: it is continuous and equals
  `jNum/jDen∘Ω` off the zeros of `jDen∘Ω`, which form a discrete set by `QMDenZeroCM3`.
- **`ι`-compatibility is kept.** A non-`ι`-compatible isomorphism transports `ι` to another
  embedding `𝒪 → End`, which on the CM locus need not differ by `Aut 𝒪`. So `PeriodMapGlue` and
  `QMPeriodValue` assume compatibility rather than risk being false.
- **Orientation (VERIFIED by reading).** Points act by `P ↦ P ≫ e`, and `endPt` and
  `(f*g).hom = g.hom ≫ f.hom` make this a left action. So `Φ(ι(a)z) = Φ(z) ≫ ι_Q(a)` matches
  `ι(ab) = ι(a)ι(b)`.
- **Same order and algebra (VERIFIED by reading).**
  - `LeafQM.O` (`ofInt n = n₀ + n₁i + n₂(1+j)/2 + n₃(i+ij)/2`) has the basis of pkg-I1's and
    bp-analytic's `oBasis`.
  - `LeafQM.B`, `PkgI1.B` and `BPAnalytic.QM.B` are all `QuaternionAlgebra ℚ 2 0 (-3)`.
- **CM normalization.** At the fixed point of `ι(x)`, `ι(x)v_τ = λv_τ`, and `z ↦ λz` preserves
  `Λ_τ` (`λι(y)v_τ = ι(yx)v_τ`) and commutes with `ι(𝒪)`. So `QMHauptmodul`'s CM clauses and R2fp's
  `HasCM4`, `HasCM3`, `HasCM24` refer to the same points.
- **The lattice facts hold for every input.**
  - `QMSkolemNoetherC`: proved in Lean.
  - `QMClassNumberOne`: `ℚΛ = ι(B)w₀`, and `I = {b : ι(b)w₀ ∈ Λ}` is a left `𝒪`-ideal (`𝒪`
    maximal), principal by class number one, so `Λ = ι(𝒪)ι(β)w₀`.
  - Fullness excludes a real direction for `w`.

## 4. Numerical check of `QMDenZeroCM3`

Script `scratch/fibre-qm-period/py/psi4_zeros.py`, output `psi4_zeros_out.txt`; mpmath at 40
digits; `Ω(τ)` re-implemented from pkg-I1's definitions.

Notation: `S = Σ_{m even} θ_m⁸ ∘ Ω` (`= jDen^{1/5}`), `P = ∏_{m even} θ_m² ∘ Ω`, and
`dF(τ) = (τ−3)(τ+1)`, proportional to `det F'(τ)` (`QMLattice.det_Fp`).

1. **Weights (VERIFIED numerically).** For `γ = ι((1+j)/2)`, `ι(i+j)`, `ι(3+2i)` and two values of
   `τ`, to at least 9 digits:
   - `|S(γτ)/S(τ)| = |cτ+d|⁸ |dF(τ)/dF(γτ)|⁴`;
   - `|P(γτ)/P(τ)| = |cτ+d|²⁰ |dF(τ)/dF(γτ)|¹⁰`.

   So `S·dF⁴` and `P·dF¹⁰` transform with weight 8 and 20 under `Γ*`, in absolute value.
2. **Orders (VERIFIED numerically).**

   | point | `ord S` | `ord P` |
   |---|---|---|
   | `−3` (`τ = i√3`) | 2 | 2 |
   | `−4` (`τ = √2+i`) | 0 | 2 |
   | `−24` (`τ = 4.1815…i`) | 0 | 0 |
3. **Valence formula (STANDARD).** For a cocompact group of signature `(0; 2, 4, 6)` (Baba–Granath
   §3.1, as quoted in the file), the orders satisfy `Σ ord_P/e_P = k/24`.
   - Weight 8: the total is `1/3 = 2/6`, used up by the order-2 zero at the order-6 point `P₋₃`.
     So `S∘Ω` has no other zero on `ℍ`, which is `QMDenZeroCM3`.
   - Weight 20: the total is `5/6 = 2/6 + 2/4`, consistent with the orders of `P`.
   - Both agree with pkg-I1's pole of order 6 of `j_θ` at `i√3`.

So `QMDenZeroCM3` follows from the published signature, the textbook valence formula, and a weight
and an order that are numerical, not proved. The weight would follow from R4 and the modular
embedding.

## 5. Integration notes

- **Prerequisites.**
  - `part_fqm.lean` needs qm-pin's full edit of `R1fpProps` (`QM-Leaves-full.patch`,
    `Split-full.patch`).
  - It also needs qm-pin's `Pin` lemmas (`part_pin.lean`; qm-pin proposes them as
    `ZInQKernel/HDecomp/QM/Pin.lean`).
  - `FibreQMNorm` imports nothing beyond `ZInQKernel.HDecomp.Analytic.QMLattice`. Its development
    file is `scratch/fibre-qm-period/dev_Norm.lean`, and it could become a kernel module.
  - The Skolem–Noether proof was developed in `dev_SN.lean`, which imports the compiled base.
- **T35 and T11a in the kernel.** These are `ZInQ.LeafPush2.UniformizationExists` and
  `T11a_RiemannEnd`. In a kernel version the copies would be replaced by the originals.
- **`R1bFamily` replaces the R1(b) placeholder.** It is the concrete replacement for
  `HSyn.R01b_ComplexUniformization`, at the leaf's triple. In a bundle it would be the clause
  `R1bFamily Y Φ π` on the triple of `R1R2fpRep` (`π = π₆ ∘ fY`). It carries R1's "qualified
  consequence" caveat and the SPECULATIVE premise bp-qmmoduli §2.2.

## 6. Lean outcomes (all VERIFIED; outputs in `scratch/fibre-qm-period/run_*.txt`)

| run | file | outcome |
|---|---|---|
| prereq | `lake build ZInQKernel.HDecomp.Analytic.QMLattice ZInQKernel.Hypotheses.JHeight` | OK, 2m0s |
| run_base | `FQMBase.lean` (ThetaPoint + qm-pin full edit + `part_pin`, 20634 lines) | 0 errors, 2m52s |
| run_dev2-13 | `Dev.lean` = `import FQMBase` + `part_fqm.lean` (base compiled to an olean with `lean -o`) | final run_dev13: 0 errors, 31 axioms lines standard |
| run_full1-6 | `FibreQM.lean` (assembled), `lake env lean` | 0 errors, no `sorry`; every axioms line of §N and §F standard. run_full6 checks the final file: 32 lines, 2m33s |

To reproduce, from the repository root:
1. build the prerequisites above;
2. run `scratch/fibre-qm-period/build.sh`;
3. run `lake env lean scratch/fibre-qm-period/FibreQM.lean`.

`FQMBase.lean` is regenerated by `build.sh` and is not committed.

## 7. What remains

- **Glue to formalize.**
  - `PeriodMapGlue` (large): GAGA, R2fp on `ℂ`-points, isomorphisms of QM tori.
  - `HauptmodulUnique` (medium-large): pure complex analysis, statable over Mathlib today.
  - `CPtsTransport` (medium): pullbacks of points and rigidity.
  - `QMDenZeroCM3`: the valence formula, the weight (from R4 and the modular embedding), and the
    order at `P₋₃`.
- **Textbook facts to formalize.**
  - `QMClassNumberOne` (medium): Eichler's theorem for the maximal order of discriminant 6, in
    lattice form.
- **Leaves for a human to check.**
  - `R1bFamily`: is the family form faithful to Shimura's Main Theorem I, and does the transfer to
    pinned triples hold?
- **Inherited caveat.** No human review has been done. Like every leaf-qm-fp object, the
  Shimura-curve inputs inherit the SPECULATIVE premise bp-qmmoduli §2.2.
