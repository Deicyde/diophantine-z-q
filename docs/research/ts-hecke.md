# ts-hecke: the five Hecke Props under `CoverModelOfHecke`, settled and reduced

Task ts-hecke, 2026-11-13. The targets are the five open glue Props of prop-ts-glue
(docs/research/prop-ts-glue.md §4; `scratch/prop-ts-glue/PropTSGlue.lean`, Part C):

- `HeckeIrreducible`;
- `HeckeNormalizationIrr`;
- `HeckeDegree`;
- `HeckeBranch`;
- `HeckeNoVertRam`.

They are used unchanged, copied verbatim.

| File | Contents |
|---|---|
| `scratch/ts-hecke/TSHecke.lean` | the Lean file (4190 lines), assembled by `assemble.py` |
| `scratch/ts-hecke/TSHeckeMain.lean.part` | the new part (Parts 1-5) |
| `GenericFibre.lean`, `RamCount.lean`, `Units.lean` | development files, compiled; pasted verbatim into `TSHecke.lean` |
| `pi0_check.py` / `pi0_check.out` | the computation behind `HeckeIrreducible` |
| `units_table.py` | the table of 72 units of `𝒪` |
| `check_identical.py` | checks the verbatim copies |
| `log.md`, `compile_out.txt` | results log; compiler output |

Model work only; no human has reviewed it. Marks: **VERIFIED** means compiled, computed or read
in a named source. **STANDARD** means a published result with its reference. **SPECULATIVE**
means an assessment. Locators from memory are **UNVERIFIED** (no network).

## 1. Main result

**All five statements are true. None is false, vacuous or inert, and none was changed.**

- **`HeckeIrreducible`, settled.** It was marked SPECULATIVE; it is now settled by computation.
  `Y₃` has exactly two geometric components, and complex conjugation swaps them, so `Y₃` is
  `ℚ`-irreducible (VERIFIED, `pi0_check.py`). In Lean it is reduced to a single leaf, the
  connectedness of `Y₃` over `ℚ` (R1conn). The leaf is also necessary.
- **`HeckeDegree`, proved from the kernel's existing textbook leaf `TorsionStructure`**
  (Mumford §4) alone.
- **`HeckeNormalizationIrr`** is reduced to one statement of curve theory with no moduli in it
  (`CurveGaloisChart`), plus `TorsionStructure`. All the moduli input, fibre transitivity under
  R1hecke, is proved.
- **`HeckeBranch`** is reduced to three inputs:
  - `CurveChartInf` (curve theory: the chart at `∞`);
  - `HeckeFibreSizes` (the moduli count behind Baba–Granath's elliptic table);
  - the leaves `TorsionStructure` and `R1R2fp`.

  Its commutative-algebra input, `RamOfFibreCount` (`e · #fibre = degree`), is **proved**.
- **`HeckeNoVertRam`** (Lemma NV) stays open. §6 gives the analysis and two routes.

**What is VERIFIED:**

- `lake env lean scratch/ts-hecke/TSHecke.lean` gives 0 errors. The warnings are linter warnings
  only.
- All 56 `#print axioms` lines read `[propext, Classical.choice, Quot.sound]`; none has `sorryAx`.
- `check_identical.py` prints `ALL OK`. Each of the following is contained verbatim:
  - the prop-ts prefix (PropTSGlue.lean 3-906, which equals `scratch/prop-ts/PropTS.lean`);
  - the Hecke Props and prop-ts-glue's two composition theorems (PropTSGlue.lean 3356-3442);
  - aut-o-finite's `AutOFinite.lean` (lines 3-1037);
  - infra-smooth-dim's `SmoothStalk.lean` (lines 3-388);
  - curve-glue's `ComponentIrreducible` and `CIproof.lean.part`.

**The final composite** (compiled) is:

```lean
theorem TSHecke.coverModelOfHecke_of_tsHecke (hconn : Y3Connected) (hRR : R1R2fp)
    (hT : ObjBridge.TorsionStructure) (hCG : CurveGaloisChart) (hCI : CurveChartInf)
    (hF : HeckeFibreSizes) (hV : HeckeNoVertRam) : CoverModelOfHecke
```

| Target | Compiled reduction | Remaining hypotheses |
|---|---|---|
| `HeckeIrreducible` | `heckeIrreducible_of_connected : Y3Connected → HeckeIrreducible`; conversely `connected_of_heckeIrreducible : R1R2fp → HeckeIrreducible → Y3Connected` | leaf R1conn (`Y3Connected`) |
| `HeckeDegree` | `heckeDegree_of_torsion : ObjBridge.TorsionStructure → HeckeDegree` | kernel leaf I2-Tors only |
| `HeckeNormalizationIrr` | `heckeNormalizationIrr_of : CurveGaloisChart → TorsionStructure → HeckeNormalizationIrr` | glue `CurveGaloisChart` |
| `HeckeBranch` | `heckeBranch_of' : R1R2fp → CurveChartInf → HeckeFibreSizes → TorsionStructure → HeckeBranch` | glue `CurveChartInf`, `HeckeFibreSizes` |
| `HeckeNoVertRam` | none | open glue (§6) |

## 2. `HeckeIrreducible` (Part 1)

### 2.1 The computation (VERIFIED, `pi0_check.py`, output `pi0_check.out`)

Setting: `𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩ ⊂ B = (2,−3)`, in the kernel's coordinates (`ofInt`,
`mulCoord` of `Structures.lean`; checked against the quaternion product).

1. `|𝒪/3𝒪| = 81` and `|(𝒪/3𝒪)^×| = 72` (`3` is ramified in `B`). An element is a unit iff
   `nrd ≢ 0 mod 3`, and `nrd mod 3` takes both values `1` and `2`.
2. The units of `𝒪` (338 with coordinates in `[−3, 3]`, 156 of norm `−1`) generate all of
   `(𝒪/3𝒪)^×`.
3. Shimura's uniformization (STANDARD) gives `Y₃(ℂ) = 𝒪^× \ (ℍ^± × (𝒪/3𝒪)^×)`, with
   `u·(z, a) = (u z, a u⁻¹)`. On `π₀(ℍ^±) × (𝒪/3𝒪)^×` this action has exactly 2 orbits, of 72
   points each, separated by the invariant `s · nrd(a) mod 3`.
4. **Complex conjugation `(s, a) ↦ (−s, a)` swaps the two orbits.** So the two geometric
   components are conjugate and `Y₃` is `ℚ`-irreducible.
5. Consistency checks:
   - Riemann–Hurwitz for one geometric component (degree 72 over `P¹`, indices 4, 6, 2) gives
     `g = 4`. This matches the area of `Γ₃ ⊂ 𝒪¹/±1` (index 18, so `18 · 1/3 = 6 = 2g − 2`).
   - `x² + x + 1` (constant field `ℚ(ζ₃)`) is irreducible over `ℚ`. Over `𝔽_p` (`p = 5..37`) it
     splits iff `p ≡ 1 mod 3`.

There is no explicit equation of `Y₃` to factor. The orbit count is the decisive computation.
It agrees with Deligne's description of `π₀`:
`π₀ = ℤ̂^×/nrd(K₃) = ℤ_3^×/(1 + 3ℤ_3) ≅ (ℤ/3)^×`, with `Gal(ℚ̄/ℚ)` acting through the cyclotomic
character, hence transitively.

### 2.2 Lean

- **`exists_surjective_of_R1fp`.** Any two triples with R1fp are related by a **surjective**
  morphism `g : Y' ⟶ Y`. It is `phi_part`'s morphism. It is onto because each point `x` is the
  image of its own `κ(x)`-point, `Φ'` is onto, and `Φ` is injective. So connectedness and
  irreducibility transfer between triples (`connectedSpace_of_R1fp`, `irreducibleSpace_of_R1fp`).
- **`irreducibleSpace_of_connected`.** A connected proper smooth curve over a field is
  irreducible. This uses curve-glue's `componentIrreducible`, copied with infra-smooth-dim's stalk
  dimensions.
- **Leaf R1conn**, `Y3Connected := ∃ Y Φ, R1fpProps Y Φ ∧ ConnectedSpace Y.left`.
  - *Published statement* (UNVERIFIED locators): Deligne, *Travaux de Shimura* (Bourbaki 389,
    1971) §§2-3 and *Variétés de Shimura* (1979) 2.1, 2.6.3; Milne, *Introduction to Shimura
    varieties* §5, §13. The components of `Sh_K` form `ℚ_{>0}^× \ 𝔸_f^× / nrd(K)`, and Galois acts
    through the reciprocity map.
  - *Consequence used*, with the computation of §2.1: `Y₃` is connected over `ℚ`.
- `heckeIrreducible_of_connected : Y3Connected → HeckeIrreducible`, and the converse
  `connected_of_heckeIrreducible : R1R2fp → HeckeIrreducible → Y3Connected`. So R1conn is exactly
  what is needed.

## 3. `HeckeDegree` (Part 2): proved from `TorsionStructure`

The bound `324 = 4 · 81` counts the `ℚ̄`-points in one fibre of `π`.

**`twistFibre_count`** (compiled). For `P : QML3 ℚ̄`, the set `twistFibre P` is the set of classes
whose QM pair is an `Aut(𝒪)`-twist of `P`'s. It is finite with at most 324 elements:

- `Aut(𝒪)` modulo inner automorphisms has 4 classes (aut-o-finite's `autO_mod_inner_exact`,
  copied). Inner twists are isomorphic (`innerIso`).
- A level structure on a fixed pair is determined by `u₀ mod 3𝒪`, so there are at most 81. This
  uses the kernel's `Level3.torsor`, which rests on the leaf `ObjBridge.TorsionStructure`, after
  transport along QM isomorphisms (`pullLevel`, `pullIso`, `exists_sub_liftO`).

**`GenericFibreCount`, proved** (`GenericFibre.lean`, Mathlib only). For finite `E/ℚ(X)` and
`B = integralClosure ℚ[X] E`, some `t ∈ ℚ` has at least `[E : ℚ(X)]` maps `B → ℚ̄` with
`X ↦ t`. The proof:

1. Take a primitive element and make it integral.
2. Its minimal polynomial `f` lies in `ℚ[X][T]`, since `ℚ[X]` is integrally closed.
3. Separability with denominators cleared (`integerNormalization`) gives `a f + b f' = D(X)`.
4. Choose `t` with `D(t) ≠ 0`. Then `f(t, T)` has `n` distinct roots in `ℚ̄`.
5. Each root map extends to `B`, by lying over and `IsAlgClosed.lift` (`GFC.exists_extend`).

**`heckeDegree_of`.** Those `n` maps give `n` distinct `ℚ̄`-points of `Y`, through the chart `h`
of `NormalizationModel` (`cancel_mono`, `Spec.map_injective`). They lie in one `π`-fibre. R2fp
puts their classes in one twist fibre, and `Φ` is injective. So `n ≤ 324`.

## 4. `HeckeNormalizationIrr` (Part 3)

**Proved, the moduli input (fibre transitivity):**

- **`Units.lean`: `𝒪^× → (𝒪/3𝒪)^×` is onto** (`exists_unit_congr`).
  - A table of 72 explicit units, `tbl_spec`, is checked by `decide +kernel`.
  - The reduced norm in coordinates (`nrdC`) is multiplicative (`ring`).
  - The inverse of a unit is `±` its conjugate.
- **`fibre_transitive`.** If `π(y) = π(y')` on `ℚ̄`-points, then
  `Φ(y') = rightMul u (twist α (Φ y))` for some `α ∈ Aut 𝒪` and `u ∈ 𝒪^×`. The ingredients are
  R2fp, `pullLevel`, `Level3.torsor` and `exists_unit_congr`.
- **`fibre_transitive_aut`.** The same with automorphisms: `y' = y ≫ g₁ ≫ g₂`, where `g₁, g₂` are
  R1hecke's automorphisms.
- `pi_invariant_twist` and `pi_invariant_rightMul`: these automorphisms preserve `π` on
  `ℚ̄`-points.
- `fibre_finite`: the `π`-fibres on `ℚ̄`-points are finite.

**Glue `CurveGaloisChart`** (curve theory with no moduli). Let `Y` be a proper smooth irreducible
curve over `ℚ`, and `π : Y → P¹` a morphism with finite `ℚ̄`-fibres. Suppose any two `ℚ̄`-points
with the same `π`-value differ by a `π`-preserving automorphism. Then there is a finite Galois
`E/ℚ(X)` with `NormalizationModel Y π E`.

STANDARD (Hartshorne II.6.7-6.8; Stacks 02OG; Artin's theorem; UNVERIFIED locators):

1. `π` is quasi-finite and proper, hence finite.
2. `Y` is normal, so `π⁻¹(𝔸¹) = Spec B`.
3. The automorphisms act faithfully on `E` and transitively on a generic geometric fibre of
   `n = [E : ℚ(X)]` points. So `n ≤ |G| ≤ n`, and `E` is Galois over `ℚ(X)`.

**Compiled:**

- `heckeNormalizationIrr_of : CurveGaloisChart → TorsionStructure → HeckeNormalizationIrr`;
- `heckeNormalization_of : Y3Connected → CurveGaloisChart → TorsionStructure →
  HeckeNormalization`.

## 5. `HeckeBranch` (Part 4)

The proof goes through three facts:

- `e(Q) · #(geometric fibre) = [E : ℚ(X)]` for a Galois extension;
- the geometric fibres of the charts are the `π`-fibres;
- the `π`-fibres are twist fibres, whose sizes are those of the elliptic table.

| Prop | kind | status |
|---|---|---|
| `RamOfFibreCount` | glue (commutative algebra) | **proved** (`ramOfFibreCount`, details below) |
| `NormalizationModelInf` | definition | the chart at `∞`: an open immersion `Spec B_∞ → Y` covering `π ≠ 0`, with `π = ∞` exactly where `s = 0` |
| `CurveChartInf` | glue (curve theory) | open. STANDARD: a chart over `𝔸¹` gives one over `P¹ ∖ {0}`, since finite fibres force `Y` irreducible with function field `E` |
| `HeckeFibreSizes` | glue from leaves (moduli count) | open. There is `M` (`= 144 = |Γ'|`) with: every twist fibre `≤ M`; `= M` without CM by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]`; and `M ∣ 4F`, `6F`, `2F` at those (sizes 36, 24, 72). Source: Shimura uniformization, Baba–Granath §3.1 elliptic orders, h-b1 M9 (VERIFIED enumeration) |

`RamOfFibreCount` is a statement about Galois `E` and a prime `Q` over `ker(X ↦ t)`:
`e(Q) · #{ψ : B → ℚ̄ | ψ X = t} = [E : ℚ(X)]`. It has an `∞` clause and a junk-zero clause. Its
proof:

- `RamCount.lean`, `RamCount.ramCount`, for a PID base, uses five ingredients:
  - Mathlib's `sum_ramification_inertia_eq_finrank`;
  - `ramificationIdx_eq_of_isGaloisGroup`, with `Gal(E/F)` acting on `B` through
    `IsGaloisGroup.of_isFractionRing`;
  - the fibre equivalence `{ψ | ker ψ = q} ≃ (B/q →ₐ[A/P] Ω)`;
  - `AlgHom.natCard_of_splits`;
  - `inertiaDeg_eq_of_isMaximal`.
- `isFractionRing_infCoord` shows that `ℚ(X)` is the fraction field of `ℚ[s]` via `s ↦ X⁻¹`, using
  `Polynomial.reflect`.

**Compiled:**

- `chart_count`, `chart_count_inf`: the `ℚ̄`-points of the charts are the `π`-fibres;
- `fibre_ncard`: a `π`-fibre is a twist fibre;
- `ker_eval_rat`, `exists_ker_eval`, `finrank_le_twistFibre`;
- **`heckeBranch_of`**, and `heckeBranch_of'`, which takes the CM objects from `R1R2fp` and
  `RamOfFibreCount` from its proof.

The proof derives `[E : ℚ(X)] = M` through the generic value `1`, using lying over. Then:

- off the branch points, `e = 1`;
- at `0`, `e · F₀ = M` with `M ∣ 4 F₀`, so `e ∣ 4`;
- likewise at `−16/27`, `e ∣ 2`, and at `∞`, `e ∣ 6`.

## 6. `HeckeNoVertRam`: open, with analysis

**It is true.** Two arguments are available:

- **(NV, h-b1 §3)** Lemma NV. Its steps:
  - tameness;
  - residue fields over the branch points are unramified at `p ≥ 5` (the bundle clause
    `R1recProps`, compiled as `residue_unramified_over_branch`);
  - local analysis at `(p, X − b)` by Abhyankar (T2);
  - the `W = (ℤ/2)²` argument with the inertia of `X₆ → P¹`.
- **(GR)** Good reduction:
  - `Y₃` has a smooth proper model over `ℤ_(p)` for `p ∤ 6` (Morita 1981; Carayol 1986;
    UNVERIFIED locators);
  - its tame quotient by `Γ'` is `P¹_{ℤ_(p)}`, with the branch sections `0, ∞, −16/27` disjoint
    mod `p`;
  - so the model is the normalization of `P¹_{ℤ_(p)}` in `E`;
  - its special fibre is reduced, hence `e = 1` at every vertical prime.

**Why the branch data alone cannot give it.** The example `E = ℚ(X)(√(pX))` has branch points
`0, ∞` of index 2 and residue fields `ℚ` over both. Yet `p` ramifies vertically, since `v_p(pX)`
is odd. Any reduction must therefore use the arithmetic of the `ℚ`-form: NV's `W`-argument, or an
integral model.

**Not done:** a Lean decomposition. Its pieces would be inertia groups at the height-2 primes
`(p, X − b)` of the integral closure of `ℤ[X]`, or an integral model over `ℤ_(p)`. Mathlib has
inertia groups for Galois actions (`Ideal.inertia`, `HilbertTheory.lean`) and the Dedekind theory
over `ℤ[X]_(p)`. The two-dimensional local analysis (Abhyankar at a closed point of `P¹_ℤ`) is
the missing piece.

## 7. Independent review (read-only model agent, no Lean)

**Verdict:** every new Prop is true as stated, and none is vacuous or a disguised conclusion. The
Props reviewed:

- `Y3Connected`;
- `GenericFibreCount`;
- `CurveGaloisChart`;
- `RamOfFibreCount`. For clause (a), a prime over `⊥` is `⊥`, and `ramificationIdx_bot_eq_one`
  applies;
- `NormalizationModelInf` and `CurveChartInf`;
- `HeckeFibreSizes`, with `M = 144` and sizes 144, 36, 24, 72. CM points of discriminants `−8`
  and `−12` do not exist on `X₆`.

The reductions have no hidden triviality. The reviewer's docstring improvements were applied to
ts-hecke's own Props. One point is outside ts-hecke's files: prop-ts's `NormalizationModel`
docstring (PropTSGlue.lean about line 708) still calls `ℚ`-irreducibility SPECULATIVE. It can now
cite `Y3Connected` and §2.1. That file was not edited.

## 8. What remains (for the announcement)

| Prop | kind | content | suggested source / route |
|---|---|---|---|
| `Y3Connected` | **leaf** | `Y₃` is connected over `ℚ` | Deligne/Shimura `π₀` and reciprocity, with §2.1's computation; or the uniformization plus complex conjugation |
| `CurveGaloisChart` | glue | finite map, normalization chart, Artin | Hartshorne II.6; Stacks 02OG |
| `CurveChartInf` | glue | the chart at `∞` | as above |
| `HeckeFibreSizes` | glue from leaves | twist-fibre sizes 144, 36, 24, 72 | uniformization and Baba–Granath §3.1; or `End(A)` of QM surfaces (QM dichotomy) with CM units |
| `HeckeNoVertRam` | glue | Lemma NV | §6 (NV or GR) |
| `ObjBridge.TorsionStructure`, `R1R2fp` | existing leaves | — | already in the bundle |
