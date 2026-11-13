# curve-glue: C2K and C3K reduced, and the CM-point gap in `MobiusGlue` closed

Task curve-glue, 2026-11-13. Base f90cf864, merged with `origin/wip/infra-smooth-dim` (2b0e44f4).
Scratch: `scratch/curve-glue/` (results log `log.md`). No file under `ZInQKernel/`, `blueprint/` or
another task's directory was edited. This is model work only; no human has reviewed it.

Marks: **VERIFIED** means compiled, computed, or read in a file. **STANDARD** means published, with
a reference. **UNVERIFIED** means a theorem number recalled without a source (there is no network
here).

## 1. Result

**The kernel's `MobiusGlue` now follows from five named statements, and every step between them is
compiled Lean.** The five are two textbook leaves and three pieces of standard curve glue:

| | name | kind | one-line content |
|---|---|---|---|
| (L0) | `FiniteGlobalSections` | **textbook leaf** | `Γ(W, 𝒪)` is finite over `K` for `W` clopen in a proper `K`-scheme (EGA III 3.2.1) |
| T5 | `ObjBridge.TorsionStructure` | **textbook leaf** (existing) | `A(K̄)[n] ≅ (ℤ/n)^{2g}` |
| (CI) | `ComponentIrreducible` | glue | connected components of a smooth curve over a field are irreducible |
| (AD) | `AlgDep` | glue | two maps `σ, ρ : X → P¹` satisfy a nonzero polynomial relation on a component (the function field has transcendence degree 1) |
| (IC) | `ImageClosed` | glue | the image of a component under `(σ, ρ)`, intersected with `𝔸²`, is Zariski closed (properness) |

The proof uses no other assumption. In particular, C1b `SmoothStalkDimOne` was proved by the
parallel task infra-smooth-dim; its branch was merged and its proof is copied verbatim.

`scratch/curve-glue/MobiusFinal.lean` compiles with 0 errors and axioms
`[propext, Classical.choice, Quot.sound]` (VERIFIED, `run_MobiusFinal.txt`):

```lean
theorem LeafQM.AV.CurveGlue.mobiusGlue_of_L0_CI_AD_IC_T5 (hL0 : FiniteGlobalSections)
    (hI : ComponentIrreducible) (hA : AlgDep) (hC : ImageClosed)
    (hT : ObjBridge.TorsionStructure) : LeafQM.AV.Pin.MobiusGlue
theorem LeafQM.AV.CurveGlue.mobiusGlueNoCM_of_L0_CI_AD_IC_T5 (hL0 : FiniteGlobalSections)
    (hI : ComponentIrreducible) (hA : AlgDep) (hC : ImageClosed)
    (hT : ObjBridge.TorsionStructure) (h : R1R2fp) : MobiusGlueNoCM
theorem LeafQM.AV.Pin.curveFacts_of_L0_CI_AD_IC (hL0 : FiniteGlobalSections)
    (hI : ComponentIrreducible) (hA : AlgDep) (hC : ImageClosed) : CurveRatFactor ∧ CurveSurj
```

- `LeafQM.AV.Pin.MobiusGlue` is the kernel's definition in `ZInQKernel/HDecomp/QM/Pin.lean`. The
  file imports that module and does not redefine the name.
- `MobiusGlueNoCM` is `MobiusGlue` without its CM-object premise.
- The same file has the coarser variants `mobiusGlue_of_L0_CI_G1''_T5`, `mobiusGlue_of_L0_G1'_T5`,
  `mobiusGlue_of_L0_G1_T5` and `mobiusGlue_of_L_G1_T5`.
- `MobiusEnd.lean` is lighter: it does not import all of Mathlib, and it proves
  `mobiusGlue_of_glue`, which takes C1b as a hypothesis.

**The assigned Props:**

| assigned Prop | result | Lean | file |
|---|---|---|---|
| C2K `ConstOrOntoAlgClosed` | **proved from (L)** `GlobalFunctionsConst`, which is **proved from (L0)** | `constOrOntoAlgClosed_of`, `globalFunctionsConst_of` | `C2K.lean`, `L0.lean` |
| C3K `RatFactorAlgClosed` | **proved from C2K, (CI), (AD) and (IC)**, through the intermediate statements (G1''), (G1'), (G1) and Lean-proved algebra | `ratFactorAlgClosed_of_AD` (and `_of_irr`, `_of_closed`, `_of`) | `C3K.lean`, `ClauseC.lean.part`, `AlgDep.lean.part` |
| CM-point gap in `MobiusGlue` | **closed**: the CM points exist on every triple, derived from `CMExists`, `X6Surj` and the bijectivity of `Φ`; the premise is discharged by the leaf bundle (§3) | `cm_points_of_R1R2fp(Rep)`, `mobiusGlue_noCM_of` | `CMPoints.lean` |

The algebra used for C3K: resultants, Gauss's lemma, separability in characteristic 0, Bezout-type
finiteness, and the choice of an irreducible factor.

No statement was changed. Every copied declaration is textually identical to its source; the check
is `py/verbatim.py`, all IDENTICAL, output `verbatim.txt` (VERIFIED). The only exception is one
proof line in the copied `mobiusGlue_of_curveFacts`, described in §7.

## 2. The chain and the intermediate statements

Each arrow below is a compiled Lean theorem.

```
(L0) ──globalFunctionsConst_of──▶ (L) ──constOrOntoAlgClosed_of──▶ C2K
C2K, (CI), (AD), (IC) ──imagePlaneCurveIrr_of──▶ (G1'')
(CI), (G1'') ──imagePlaneCurveClosed_of──▶ (G1')
C2K, (G1') ──imagePlaneCurve_of──▶ (G1) ──ratFactorAlgClosed_of──▶ C3K
C1b (proved), C2K, C3K ──curveFacts_of_leaves (curve-facts)──▶ CurveRatFactor ∧ CurveSurj
CurveRatFactor, CurveSurj, T5 ──mobiusGlue_of_curves (mobius-glue)──▶ MobiusGlue
MobiusGlue, R1R2fp ──mobiusGlue_noCM_of──▶ MobiusGlueNoCM
```

**Intermediate statements.** All are proved; they are kept as named Props because they make the
proof structure readable.

- (L) `GlobalFunctionsConst`. Let `K = K̄`, `X → Spec K` proper and smooth of relative dimension 1,
  and `W` open, closed and preconnected. Then every `s ∈ Γ(X, W)` differs from a constant `c ∈ K`
  by a nilpotent.
- (G1) `ImagePlaneCurve`. Either `ρ ≡ ∞` on the `K`-points of the component `W`, or there is an
  irreducible `P ∈ K[x][y]` of `y`-degree at least 1 such that:
  - (a) `P(σ, ρ) = 0` at the `K`-points of `W` where both values are finite;
  - (b) every root `(t, u) ∈ K²` of `P` is `(σ(p), ρ(p))` for a `K`-point `p` of `W`;
  - (c) if `σ(p) = t` is finite and `ρ(p) = ∞`, then `lc_y(P)(t) = 0`.
- (G1') `ImagePlaneCurveClosed`: (G1) with (b) replaced by (b''), "the affine image is the zero set
  of some `S ⊆ K[x][y]`".
- (G1'') `ImagePlaneCurveIrr`: (G1') without (c).

**Lean-proved lemmas:**

| lemma | content |
|---|---|
| `Alg.exists_two_roots` | `P` irreducible with `deg_y P ≥ 2`, `K = K̄` of characteristic 0 ⇒ some fibre `P(t, ·)` has two distinct roots |
| `Alg.finite_common_zeros` | `P` irreducible with `deg_y P ≥ 1` and `P ∤ Q` ⇒ `{P = Q = 0} ⊆ K²` is finite |
| `Alg.isCoprime_coeff_of_irreducible` | `P = A y + B` irreducible ⇒ `A`, `B` coprime |
| `exists_factor_vanishing` | if `P(F, G)` vanishes at the `K`-points of an irreducible open, so does `q(F, G)` for some irreducible factor `q` of `P` |
| `lc_eval_eq_zero_of_irreducible` | clause (c) from (a) and irreducibility |
| `exists_nilpotent_sub_of_finite` | a finite algebra over `K = K̄` with only the trivial idempotents is `K` plus nilpotents |
| `idempotent_trivial_of_isPreconnected` | an idempotent section over a preconnected open is `0` or `1` |
| `isUnit_of_ev_ne_zero` | a section nonzero at every `K`-point of its domain is a unit (Jacobson) |
| `ev_cst`, `ev_polySec` | values of constants, and of `P(F, G)`, at `K`-points |
| `cm_points_of_objects`, `cm_points_of_R1R2fp(Rep)` | the CM points over `0, ∞, −16/27` exist |

## 3. The CM-point gap

**The concern.** The proof of `MobiusGlue` (mobius-glue's `mobiusGlue_of_curveFacts`) uses
`ℚ̄`-points of `Y'` whose objects have CM by `ℤ[i]`, `ℤ[ζ₃]` and `ℤ[√−6]`, together with the values
`0, ∞, −16/27` at those points. `R2fpProps` only states the one-way implications "CM ⇒ value".

**How it is settled.** All of the following is compiled in `CMPoints.lean`.

1. **`MobiusGlue` already assumes the CM objects.** Its fifth premise in the kernel
   (`ZInQKernel/HDecomp/QM/Pin.lean`) is the existence of `QML3` objects over `ℚ̄` of the three CM
   types.
2. **Objects give points.** On every triple with `R2fpProps`, the CM points exist because `Φ Qbar`
   is a bijection onto `M3 Qbar`. The point is `y = (Φ Qbar).symm (M3.mk P)`, and the one-way
   clause gives its value (`cm_points_of_objects`).
   - Only the one-way clauses are used.
   - The converse clauses are never needed. The Möbius map is pinned by three points at which both
     `π'` and `π ∘ g` are known.
3. **The bundle gives the objects.** In `R1R2fp`, `CMExists` supplies CM points on `X₆`. The second
   half of `X6Surj` says that every QM pair over `ℚ̄` has a level-3 structure. The kernel's
   `cm_objects_of_R1R2fp` combines the two, giving `cm_points_of_R1R2fp`.
4. **The repaired bundle also works.** `R1R2fpRep` (leaf-adopt) has no `CMExists`; it has
   `R2X6PropsIff` instead. There `CMExists` follows from the biconditionals together with the first
   half of `X6Surj` (`π₆` is onto) (`cmExists_of_iff`, copied). This gives
   `cm_points_of_R1R2fpRep`.
5. **So the premise costs nothing.** `mobiusGlue_noCM_of : MobiusGlue → R1R2fp → MobiusGlueNoCM`.
   The consumers already supply the premise this way (pin-apply's `sameTripleMor_of_leaves`).

Nothing needs to be added to `MobiusGlue`'s hypotheses.

## 4. C2K from (L), and (L) from (L0) (`C2K.lean`, `L0.lean`)

**Values.**

- `ev p : Γ(X, O) →+* K` is the value at a `K`-point `p`: the residue map, then the embedding
  `κ(x) → K` of `p`. This is how `ToP1.val` evaluates.
- `cst f O c` is the constant `c`, the image of `c` under `K = Γ(Spec K) → Γ(X, O)`.
- `ev_cst`: a constant evaluates to itself at every section `p` of `f`. Proof: Mathlib's
  `Scheme.germ_stalkClosedPointTo` and `p ≫ f = 𝟙`.
- `isUnit_of_ev_ne_zero`: a section that is nonzero at every `K`-point of its domain is a unit.
  This uses Jacobson and Mathlib's `pointOfClosedPoint`.

**C2K** (`constant_of_missed`). Let `W` be the component of `p₀`; it is open since `X` is
Noetherian. Suppose `σ = [U, V, f, g]` misses a value `t` on the `K`-points of `W`.

- **`t = ∞`.** Then `W ⊆ U`, and `f|_W` is constant by (L).
- **`t = a ∈ K`.**
  1. `f − a` is a unit on `W ∩ U`, and `1 − a g` is a unit on `W ∩ V`.
  2. `1/(f − a)` and `g/(1 − a g)` glue to `h ∈ Γ(X, W)` (Mathlib's `objSupIsoProdEqLocus`).
  3. By (L), `h` takes one value `c` at the `K`-points of `W`.
  4. If `W ∩ U` has a `K`-point, then `c ≠ 0`. This forces `W ⊆ U` (because `g = 0` off `U`), and
     then `σ = a + 1/c` on `W`.
  5. Otherwise `σ ≡ ∞` on `W`.

**(L) from (L0).** By (L0), `Γ(X, W)` is a finite `K`-algebra.

- Its idempotents are 0 and 1. At each point, the germ of an idempotent is 0 or 1, so `W` splits
  into the disjoint opens `D(e)` and `D(1 − e)`, and `W` is preconnected.
- In an Artinian ring with only trivial idempotents, every element is a unit or nilpotent.
  Fitting's argument: `s^n = s^{n+1} y` makes `s^n y^n` idempotent.
- For an eigenvalue `c` of multiplication by `s`, `s − c` is a zero divisor, hence nilpotent.

## 5. C3K (`C3K.lean`, `ClauseC.lean.part`, `AlgDep.lean.part`)

**(G1'') from C2K, (CI), (AD) and (IC)** (`imagePlaneCurveIrr_of`). Suppose `ρ ≢ ∞` on `W`.

1. **An irreducible open.** `O = W ∩ {σ ≠ ∞} ∩ {ρ ≠ ∞}` is a nonempty open subset of the
   irreducible set `W` given by (CI), so it is irreducible.
2. **A relation.** (AD) gives `P ≠ 0` with `P(σ, ρ) = 0` on the `K`-points of `O`.
3. **An irreducible factor.** Factor `P` in the UFD `K[x][y]`. The zero loci of the sections
   `q(σ, ρ)`, for the factors `q`, are closed and cover `O` (Jacobson). Since `O` is irreducible, one
   factor `q` vanishes on all of `O` (`exists_factor_vanishing`).
4. **`deg_y q ≥ 1`.** Otherwise `q = a(x)` with `a ≠ 0`. Then the section `a(σ)` on
   `W ∩ {σ ≠ ∞}` vanishes on the dense open `O`, hence everywhere there. So `σ` takes only the
   finitely many roots of `a` as finite values, contradicting C2K (`σ` is onto).
5. **The closed-image clause.** (b'') is (IC).

**(G1') from (CI) and (G1'')** (`lc_eval_eq_zero_of_irreducible`). Clause (c) remains.

- Consider the section `P^rev(σ, 1/ρ)` on `W ∩ {σ ≠ ∞} ∩ {ρ ≠ 0}`, where `P^rev` is the reverse of
  `P` in `y`.
- It vanishes on the dense open subset `{ρ ≠ ∞}`, by (a) and `eval₂_reverse_mul_pow`.
- Its zero locus is closed, so it vanishes at a point where `ρ = ∞`. There its value is `lc_y(P)(t)`
  (`coeff_zero_reverse`).
- The required nonempty intersection comes from preirreducibility of `W`.

**(G1) from C2K and (G1')** (`imagePlaneCurve_of`).

1. By C2K and (c), the affine image `Im` is infinite.
2. `Im = V(S) ⊆ V(P)`.
3. Every `Q ∈ S` is divisible by `P`. Otherwise `V(P, Q) ⊇ Im` would be finite
   (`Alg.finite_common_zeros`, from `Res_y(P, Q) ≠ 0`).
4. Hence `V(P) ⊆ Im`.

**C3K from (G1)** (`ratFactorAlgClosed_of`).

- If `deg_y P ≥ 2`, two roots `u ≠ u'` of some fibre are hit (`Alg.exists_two_roots`: Gauss's
  lemma, then separability in characteristic 0, then `Res_y(P, ∂_y P) ≠ 0`). This gives two points
  of `W` in one `σ`-fibre with different `ρ`, which is impossible.
- So `P = A y + B` with `A, B` coprime, and `ρ = [−B : A] ∘ σ`. Clause (c) handles `ρ = ∞`.
- If `ρ ≡ ∞`, take `[1 : 0]`.

**Characteristic 0.** C3K is false in characteristic `p` (take `σ = ρ^p`). Characteristic 0 enters
only in `Alg.exists_two_roots`. None of (CI), (AD) or (IC) assumes it, and all three hold in every
characteristic.

## 6. Why the named statements are true (STANDARD; numbering UNVERIFIED)

- **(L0).** `W` is clopen, hence a closed subscheme, and proper over `K`. Then `Γ(W, 𝒪_W)` is
  finite-dimensional by the finiteness theorem for proper morphisms: EGA III₁ 3.2.1, or Hartshorne
  II.5.20 / III.8.8 in the projective case.
  - Smoothness is not needed, nor is algebraic closedness.
  - Clopenness is needed: for a merely open `W`, take `𝔸¹ ⊂ P¹`.
- **(CI).**
  - Smooth over a field implies regular, hence normal.
  - A locally Noetherian normal scheme is a disjoint union of integral open subschemes, so its
    connected components are irreducible (Stacks, *Varieties* and *Properties*; Hartshorne II.8).
  - infra-smooth-dim proved that the stalks at closed points are regular of dimension 1. What
    Mathlib v4.35 lacks for a Lean proof is "regular local ⇒ domain" and "locally integral ⇒
    components disjoint".
- **(AD).**
  - The component `W` is an integral curve. Its function field has transcendence degree
    `dim W = 1` (Hartshorne I.1.8A, I.6), so `σ` and `ρ` satisfy a nonzero relation in `K(W)`.
  - The regular function `P(σ, ρ)` is therefore zero on the reduced open set where both are
    finite.
  - True in every characteristic. If `σ` is constant with finite value `c`, `P = x − c` works; if
    `σ ≡ ∞` on `W`, `P = 1` works.
- **(IC).**
  - `W → Spec K` is proper and `P¹ × P¹` is separated, so the image `D` of `W` is closed.
  - Hence `D ∩ 𝔸² = V(I)` is closed in `𝔸²`.
  - The `K`-points of `D ∩ 𝔸²` are exactly the images of `K`-points of `W`: a fibre over a closed
    point is nonempty, closed and of finite type over `K`, so it contains a closed point, which is
    a `K`-point.
- **T5.** Mumford, *Abelian Varieties*, §4 (existing leaf).

**Independent checks (model, not human).** Two fresh agents were given only the Lean files, not
the arguments above, and asked for counterexamples.

- The first judged (L) `GlobalFunctionsConst` and (G1) `ImagePlaneCurve` TRUE and not vacuous. It
  checked the cases `ρ ≡ ∞`, `ρ ≡ b`, `ρ` nonconstant and `σ = ∞`, and the variable order of
  `evalXY`.
- The second judged (L0) `FiniteGlobalSections` and (G1') `ImagePlaneCurveClosed` TRUE and not
  vacuous. It noted that `S = {P}` works and that `S = ∅` would make the image all of `K²`.
- (CI), (AD) and (IC) were introduced after these checks and were not reviewed independently. Each
  is one of the standard facts that the checked statements (G1) and (G1') were argued from.

## 7. Files and verification

All runs used `lake env lean`, one Lean process at a time. Every file has 0 errors and axioms
`[propext, Classical.choice, Quot.sound]` (VERIFIED, `run_*.txt`). The three composite files are
generated by `py/assemble.py`.

| file | content | warnings |
|---|---|---|
| `CMPoints.lean` | the CM-point gap (§3) | 0 |
| `C2K.lean` | C2K from (L) | 0 |
| `L0.lean` | (L) from (L0) | 0 |
| `C3K.lean` | C3K from (G1), (G1) from C2K and (G1'), the algebra | 0 |
| `ClauseC.lean.part`, `AlgDep.lean.part` | (G1') from (CI) and (G1''); (G1'') from C2K, (CI), (AD) and (IC) | compiled inside the composites |
| `CurveGlueAll.lean` | `CurveFacts.lean` verbatim, then `C2K`, `C3K` and the two parts; `curveFacts_of_glue`, `_glue'`, `_glue''`, `_glue_AD` | 0 |
| `MobiusEnd.lean` | imports the kernel's `QM.Pin`; contains mobius-glue §1-§5 and §7-§8, `CurveGlueAll` and `CMPoints`; proves `mobiusGlue_of_glue` | linter warnings, only in copied mobius-glue code |
| `MobiusFinal.lean` | `import Mathlib`; contains infra-smooth-dim's dimension theory (verbatim), `MobiusEnd` and `L0`; proves the theorems of §1 | linter warnings, only in copied code |

**The one changed line.** mobius-glue's `mobiusGlue_of_curveFacts` was written against qm-pin's
`R1fpPropsU`. In `MobiusEnd.lean`, one line destructures `h1' : R1fpProps Y' Φ'` in the kernel's
clause order instead. Everything else is verbatim, and `py/verbatim.py` checks this.

## 8. What remains

- **(L0)** is a textbook leaf, not in Mathlib v4.35. Only `H⁰(𝒪)` of a clopen piece of a proper
  scheme over a field is needed.
- **(CI), (AD) and (IC)** are standard glue, not in Mathlib v4.35.
  - (CI) is closest to Lean. It needs "regular local ring ⇒ domain" (dimension 1 suffices) on top
    of infra-smooth-dim's regularity of stalks, plus "locally integral ⇒ connected components are
    irreducible".
  - (AD) needs function fields of curves and their transcendence degree.
  - (IC) needs `P¹ × P¹` (or `P¹ ×_K P¹`) as a scheme with its points, and closedness of images
    under proper maps. Mathlib has `IsProper → UniversallyClosed`.
- **T5** is unchanged.
- **Integration.** `MobiusFinal.lean` is self-contained over the kernel and Mathlib. To integrate:
  - add kernel modules for the C2K/C3K/L0 sections, curve-facts, mobius-glue's mathematics and
    infra-smooth-dim's dimension theory;
  - replace the field `MobiusGlue` (pin-apply's `GluePiecesPin`) by (L0), (CI), (AD) and (IC);
  - T5 is already in `TextbookLeaves`.
