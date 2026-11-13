# curve-glue: C2K and C3K reduced, and the CM-point gap in `MobiusGlue` closed

Task curve-glue, 2026-11-13. Base f90cf864, merged with `origin/wip/infra-smooth-dim` (2b0e44f4).
Scratch: `scratch/curve-glue/` (results log `log.md`). No file under `ZInQKernel/`, `blueprint/` or
another task's directory was edited. This is model work only; no human has reviewed it.

Marks: **VERIFIED** means compiled, computed, or read in a file. **STANDARD** means published,
with a reference. **UNVERIFIED** means a theorem number recalled without a source (there is no
network here).

## 1. Result

**The kernel's `MobiusGlue` now rests on three named statements, and every step between them is
compiled Lean:**

- (L0) `FiniteGlobalSections`: a textbook leaf, the finiteness theorem for proper morphisms.
- (G1) `ImagePlaneCurve`: glue, a statement about plane curves.
- T5 `ObjBridge.TorsionStructure`: the existing textbook leaf.

The parallel task infra-smooth-dim proved the third curve-facts input, C1b `SmoothStalkDimOne`, so
it is no longer an assumption.

`scratch/curve-glue/MobiusFinal.lean` compiles with 0 errors and axioms
`[propext, Classical.choice, Quot.sound]` (VERIFIED, `run_MobiusFinal.txt`). It contains:

```lean
theorem LeafQM.AV.CurveGlue.mobiusGlue_of_L0_G1_T5 (hL0 : FiniteGlobalSections)
    (hG : ImagePlaneCurve) (hT : ObjBridge.TorsionStructure) : LeafQM.AV.Pin.MobiusGlue
theorem LeafQM.AV.CurveGlue.mobiusGlueNoCM_of_L0_G1_T5 (hL0 : FiniteGlobalSections)
    (hG : ImagePlaneCurve) (hT : ObjBridge.TorsionStructure) (h : R1R2fp) : MobiusGlueNoCM
theorem LeafQM.AV.Pin.curveFacts_of_L0_G1 (hL0 : FiniteGlobalSections) (hG : ImagePlaneCurve) :
    CurveRatFactor ∧ CurveSurj
```

`LeafQM.AV.Pin.MobiusGlue` here is the kernel's definition in `ZInQKernel/HDecomp/QM/Pin.lean`.
The file imports that module and does not redefine the name. `MobiusGlueNoCM` is `MobiusGlue`
with its CM-object premise removed.

The two assigned Props are reduced as follows:

| assigned Prop | result | Lean | file |
|---|---|---|---|
| C2K `ConstOrOntoAlgClosed` | **proved from (L)** `GlobalFunctionsConst`; (L) is proved from **(L0)** | `constOrOntoAlgClosed_of : GlobalFunctionsConst → ConstOrOntoAlgClosed`, `globalFunctionsConst_of : FiniteGlobalSections → GlobalFunctionsConst` | `C2K.lean`, `L0.lean` |
| C3K `RatFactorAlgClosed` | **proved from (G1)** plus Lean-proved algebra (resultants, Gauss's lemma, characteristic 0) | `ratFactorAlgClosed_of : ImagePlaneCurve → RatFactorAlgClosed` | `C3K.lean` |
| CM-point gap in `MobiusGlue` | **closed**: the CM points exist on every triple, derived from `CMExists`, `X6Surj` and the bijectivity of `Φ`; the CM premise of `MobiusGlue` is discharged by the leaf bundle | `cm_points_of_R1R2fp`, `cm_points_of_R1R2fpRep`, `mobiusGlue_noCM_of` | `CMPoints.lean` |

No statement was changed. Every copied declaration is textually identical to its source; the
check is `py/verbatim.py`, output `verbatim.txt` (VERIFIED). The only exception is one proof line
in the copied `mobiusGlue_of_curveFacts`, described in §7.

## 2. The named Props

| name | kind | content | status |
|---|---|---|---|
| **(L0) `FiniteGlobalSections`** | **textbook leaf** | `X → Spec K` proper over any field `K` and `W ⊆ X` open and closed ⇒ `Γ(W, 𝒪_X)` is a finite `K`-module (`(cstHom f W).Finite`) | STANDARD: EGA III₁ 3.2.1 (coherence of `f_*` for proper `f`); Hartshorne II.5.20 / III.8.8 for projective `X` (numbering UNVERIFIED); not in Mathlib v4.35 |
| (L) `GlobalFunctionsConst` | leaf form, now **proved from (L0)** | `K = K̄`, `X → Spec K` proper and smooth of relative dimension 1, `W` open, closed and preconnected, `s ∈ Γ(X, W)` ⇒ `s − c` is nilpotent for some `c ∈ K` | consequence of (L0) (`globalFunctionsConst_of`, VERIFIED). Also a consequence of "Γ = K for proper, connected, reduced schemes over `K̄`" (Hartshorne Ex. II.4.5(d) / I.3.4; Stacks, Varieties; UNVERIFIED numbering) |
| **(G1) `ImagePlaneCurve`** | **glue** | setting of C3K without characteristic 0: either `ρ ≡ ∞` on the `K`-points of the component `W`, or there is an irreducible `P ∈ K[x][y]` of `y`-degree ≥ 1 with (a) `P(σ(p), ρ(p)) = 0` at the `K`-points of `W` where both values are finite; (b) every `(t, u) ∈ K²` with `P(t, u) = 0` is `(σ(p), ρ(p))` for a `K`-point `p` of `W`; (c) `σ(p) = t` finite and `ρ(p) = ∞` ⇒ `lc_y(P)(t) = 0` | STANDARD (§6); not in Mathlib v4.35 (no `P¹ × P¹`, no plane curves) |
| T5 `ObjBridge.TorsionStructure` | textbook leaf (existing) | `A(K̄)[n] ≅ (ℤ/n)^{2g}` (Mumford §4) | already in `TextbookLeaves` |
| C1b `SmoothStalkDimOne` | glue, **proved** by infra-smooth-dim | stalks at closed points of a smooth curve over a field have dimension 1 | `smoothStalkDimOne`, copied verbatim into `MobiusFinal.lean` (VERIFIED) |

The following intermediate statements are all proved in Lean:

| name | content |
|---|---|
| `constOrOntoAlgClosed_of` | C2K from (L) |
| `ratFactorAlgClosed_of` | C3K from (G1) |
| `Alg.exists_two_roots` | `P ∈ K[x][y]` irreducible with `deg_y P ≥ 2`, `K` algebraically closed of characteristic 0 ⇒ some fibre `P(t, ·)` has two distinct roots |
| `Alg.isCoprime_coeff_of_irreducible` | `P = A y + B` irreducible ⇒ `A`, `B` coprime |
| `exists_nilpotent_sub_of_finite` | a finite algebra over `K = K̄` with only the trivial idempotents is `K` plus nilpotents |
| `idempotent_trivial_of_isPreconnected` | an idempotent section of `𝒪_X` over a preconnected open is `0` or `1` |
| `isUnit_of_ev_ne_zero` | a section that is nonzero at every `K`-point of its domain is a unit (Jacobson) |
| `ev_cst` | the value of the constant section `c` at a `K`-point is `c` |
| `cm_points_of_objects`, `cm_points_of_R1R2fp(Rep)` | the CM points over `0, ∞, −16/27` exist |

## 3. The CM-point gap

The review's concern was this. The proof of `MobiusGlue` (mobius-glue's `mobiusGlue_of_curveFacts`)
uses `ℚ̄`-points `y` of `Y'` whose objects have CM by `ℤ[i]`, `ℤ[ζ₃]` and `ℤ[√−6]`, and the values
`0, ∞, −16/27` there. `R2fpProps` only states the one-way implications "CM ⇒ value".

The concern is settled as follows, all compiled in `CMPoints.lean`:

1. **`MobiusGlue` already assumes the CM objects.** Its fifth premise in the kernel
   (`ZInQKernel/HDecomp/QM/Pin.lean`) is the existence of `QML3` objects over `ℚ̄` with each of the
   three CM types.
2. **CM points follow from CM objects.** Given the objects, the points exist on every triple
   satisfying `R2fpProps`, because `Φ Qbar` is a bijection onto `M3 Qbar`. The point is
   `y = (Φ Qbar).symm (M3.mk P)`, and the one-way clause gives its value. This is
   `cm_points_of_objects`; it uses only the one-way clauses. The converse clauses are never needed:
   the Möbius map is pinned by the three points where both `π'` and `π ∘ g` are known.
3. **The CM objects follow from the leaf bundle.** In `R1R2fp`, `CMExists` gives CM points on
   `X₆`. The second half of `X6Surj` says that every QM pair over `ℚ̄` has a level-3 structure,
   i.e. `Y₃ → X₆` is onto. The kernel's `cm_objects_of_R1R2fp` uses both. Hence
   `cm_points_of_R1R2fp`.
4. **The repaired bundle works too.** `R1R2fpRep` (leaf-adopt) has no `CMExists`; it has the
   biconditional `R2X6PropsIff`. There, `CMExists` follows from the biconditionals and the first
   half of `X6Surj`, which says `π₆` is onto (`cmExists_of_iff`, copied). Hence
   `cm_points_of_R1R2fpRep`.
5. **So the premise costs nothing.** `mobiusGlue_noCM_of : MobiusGlue → R1R2fp → MobiusGlueNoCM`.
   The consumers of `MobiusGlue` already supply the premise this way (pin-apply's
   `sameTripleMor_of_leaves`).

Nothing needs to be added to `MobiusGlue`'s hypotheses.

## 4. C2K from (L) (`C2K.lean`)

**Values at `K`-points.**

- `ev p : Γ(X, O) →+* K` is the value of a section at a `K`-point `p`. It is the residue map
  followed by the embedding `κ(x) → K` of `p`, which is exactly how `ToP1.val` evaluates.
- `cst f O c` is the constant `c`, the image of `c` under `K = Γ(Spec K) → Γ(X) → Γ(X, O)`.
- `ev_cst` says that constants evaluate to themselves at every section `p` of `f`. It is proved
  through Mathlib's `Scheme.germ_stalkClosedPointTo` and `p ≫ f = 𝟙`.

**Units.** In a Jacobson scheme of finite type over `K = K̄`, closed points are `K`-points
(Mathlib's `pointOfClosedPoint`). So a section that is nonzero at every `K`-point of its domain
has `D(s)` equal to the whole domain, and is a unit (`isUnit_of_ev_ne_zero`).

**Main argument** (`constant_of_missed`). Let `W` be the connected component of `p₀`. `W` is open
because `X` is Noetherian. Suppose `σ = [U, V, f, g]` misses a value `t` on the `K`-points of `W`.

- **`t = ∞`.** Every `K`-point of `W` lies in `U`. By the Jacobson property, `W ⊆ U`. By (L),
  `f|_W` is constant up to nilpotents, so `σ` is constant on `W`.
- **`t = a ∈ K`.**
  1. `f − a` is a unit on `W ∩ U`, and `1 − a g` is a unit on `W ∩ V`. Both are checked at
     `K`-points, using `fg = 1` on `U ∩ V` and `g = 0` off `U`.
  2. `1/(f − a)` and `g/(1 − a g)` agree on the overlap, so they glue to `h ∈ Γ(X, W)`. The gluing
     uses Mathlib's `objSupIsoProdEqLocus`.
  3. By (L), `h` takes a single value `c` at all `K`-points of `W`.
  4. If `W ∩ U` has a `K`-point, then `c ≠ 0`. This rules out `K`-points of `W` off `U`, where
     `h = g/(1 − ag) = 0`. Hence `σ = a + 1/c` on `W`.
  5. Otherwise `σ ≡ ∞` on `W`.

**Conclusion.** Either `σ` takes every value on `W`, or it misses one and is constant. This is C2K.

## 5. C3K from (G1) (`C3K.lean`)

**Algebra** (`Alg.exists_two_roots`, Lean-proved). Let `P ∈ K[x][y]` be irreducible with
`deg_y P = d ≥ 2`.

1. `P` is primitive and stays irreducible over `K(x)`
   (`IsPrimitive.irreducible_iff_irreducible_map_fraction_map`).
2. In characteristic 0 it is therefore separable, so `Res_y(P, ∂P/∂y) ≠ 0` in `K(x)`
   (`resultant_ne_zero`).
3. Hence `r = Res_y(P, ∂P/∂y) ∈ K[x]` is nonzero (`resultant_map_map`).
4. Choose `t` with `r(t) · lc(P)(t) ≠ 0`. Then `P(t, y)` has degree `d`, and its resultant with
   its derivative is `r(t) ≠ 0` (`resultant_map_map` again, with `derivative_map` and
   `leadingCoeff_derivative`).
5. So `P(t, y)` is coprime to its derivative (`resultant_eq_zero_iff`), hence separable.
6. Over `K = K̄` it therefore has `d ≥ 2` distinct roots (`nodup_roots`,
   `Splits.natDegree_eq_card_roots`).

**Reduction** (`ratFactorAlgClosed_of`).

- **If `ρ ≡ ∞` on `W`,** take `[F : G] = [1 : 0]`.
- **Otherwise, take `P` from (G1).** Then `deg_y P = 1`. Indeed, if `deg_y P ≥ 2`, then two roots
  `u ≠ u'` of some `P(t, ·)` are both hit by (b). This gives two `K`-points of `W` in the same
  `σ`-fibre with different `ρ`, which contradicts the fibre hypothesis.
- **Write `P = A y + B`,** with `A` and `B` coprime (`Alg.isCoprime_coeff_of_irreducible`). Take
  `[F : G] = [−B : A]`, and let `p` be a `K`-point of `W` with `σ(p) = t` finite.
  - `ρ(p) = ∞`: clause (c) gives `A(t) = 0`, so `[−B : A](t) = ∞`.
  - `ρ(p) = u` finite: clause (a) gives `A(t) u + B(t) = 0`. `A(t) = B(t) = 0` would contradict
    coprimality, so `A(t) ≠ 0` and `u = −B(t)/A(t)`.

**Where characteristic 0 enters.** C3K is false in characteristic `p`: take `σ = ρ^p` on `P¹`
(curve-facts §3). Characteristic 0 enters only through the separability step in the Lean algebra;
(G1) itself holds in every characteristic. For example, with `σ = ρ^p`, (G1) gives `P = y^p − x`,
and `Alg.exists_two_roots` correctly fails, since `P(t, y)` has a single root.

## 6. Why the new named Props are true

**(L0) `FiniteGlobalSections`.**

- `W` is open and closed in `X`, so it is a closed subscheme, and `W → Spec K` is proper.
- By the finiteness theorem, `Γ(W, 𝒪_W) = H⁰(W, 𝒪_W)` is a finite-dimensional `K`-vector space.
  The `K`-structure is the one through `f`, which is `cstHom f W`.
- Neither smoothness nor algebraic closedness is assumed. This is the published statement,
  specialized to `𝓕 = 𝒪_W` and `H⁰` (STANDARD; EGA III₁ 3.2.1, numbering UNVERIFIED).

**(L) from (L0)** (Lean-proved, `L0.lean`).

1. A finite `K`-algebra is Artinian.
2. If its only idempotents are 0 and 1, every element is a unit or nilpotent. Fitting's argument:
   `s^n = s^{n+1} y` makes `s^n y^n` idempotent.
3. For an eigenvalue `c` of multiplication by `s` (which exists since `K = K̄`), `s − c` is a zero
   divisor, so it is nilpotent.
4. An idempotent section over a preconnected `W` is 0 or 1, because its germs are 0 or 1 in the
   local rings.

**(G1) `ImagePlaneCurve`** (STANDARD; references UNVERIFIED).

- **The image curve.** `W` is a complete nonsingular irreducible curve: smooth implies normal, so
  connected components are irreducible. Its image `D` under `(σ, ρ) : W → P¹ × P¹` is closed
  (properness: `W → Spec K` is universally closed and `P¹ × P¹` is separated) and irreducible. It is not a point, because `σ` is nonconstant.
- **If `ρ ≢ ∞`, `D ∩ 𝔸²` is cut out by one irreducible `P`.** `D ∩ 𝔸²` is nonempty, open and
  dense in `D`. It is an irreducible curve in `𝔸²`, so it equals `V(P)` with `P` irreducible:
  `K[x, y]` is a UFD and height-one primes are principal (Hartshorne I.1.13, numbering UNVERIFIED).
- **`P` has `y`-degree ≥ 1.** Otherwise `σ` would be constant on a dense open subset of `W`.
- **(a)** is `D ∩ 𝔸² ⊆ V(P)`.
- **(b)** `V(P) ⊆ D`. The fibre of `W → D` over a closed point is a nonempty closed set of finite
  type over `K`, so it contains a closed point. That point is a `K`-point (Nullstellensatz).
- **(c)** A point `(t, ∞)` of `D` lies in the closure of `V(P)` in `𝔸¹ × P¹`. That closure lies in
  the zero set of the `y`-homogenization `Σ aᵢ(x) y₁ⁱ y₀^{d−i}`, which at `y₀ = 0` reads
  `a_d(t) = 0`.
- **Classification.** It is glue because it combines several textbook facts rather than restating
  one printed theorem.

**Independent check (model, not human).** A fresh agent was given only the Lean files, with no
proofs or arguments from this report, and asked for counterexamples.

- It judged `GlobalFunctionsConst` **TRUE and not vacuous**:
  - for empty `W`, `Γ = 0`;
  - for nonempty `W`, `Γ(W)` is a finite connected `K`-algebra;
  - `X = P¹_K` satisfies the hypotheses.
- It judged `ImagePlaneCurve` **TRUE without characteristic 0, and not vacuous**:
  - it checked the cases `ρ ≡ ∞`, `ρ ≡ b` (`P = y − b`) and `ρ` nonconstant;
  - it confirmed the variable order in `evalXY` and the `y`-leading coefficient;
  - its spot checks were `ρ = 1/σ` (`P = xy − 1`) and Frobenius (`P = y^p − x`);
  - `X = P¹`, `σ = ρ = id` satisfies the hypotheses.
- (L0) was added after this check. Its truth is argued above.

## 7. Files and verification

All runs used `lake env lean`, one process at a time. Every file reports 0 errors and axioms
`[propext, Classical.choice, Quot.sound]` (VERIFIED, the `run_*.txt` files).

| file | content | result |
|---|---|---|
| `CMPoints.lean` | the CM-point gap (§3) | compiled, 0 warnings |
| `C2K.lean` | C2K from (L) | compiled, 0 warnings |
| `C3K.lean` | C3K from (G1) and the algebra | compiled, 0 warnings |
| `L0.lean` | (L) from (L0) | compiled, 0 warnings |
| `CurveGlueAll.lean` | `CurveFacts.lean` verbatim + `C2K.lean` + `C3K.lean`; `curveFacts_of_glue : SmoothStalkDimOne → GlobalFunctionsConst → ImagePlaneCurve → CurveRatFactor ∧ CurveSurj` | compiled |
| `MobiusEnd.lean` | imports the kernel's `QM.Pin`; mobius-glue's §1-§5 and §7-§8 (from `scratch/mobius-glue/MobiusGlue.lean`) + `CurveGlueAll` + `CMPoints`; `mobiusGlue_of_glue : SmoothStalkDimOne → (L) → (G1) → T5 → MobiusGlue` | compiled; linter warnings only in copied mobius-glue code |
| `MobiusFinal.lean` | `import Mathlib` + infra-smooth-dim's dimension theory (verbatim) + `MobiusEnd` + `L0`; the theorems of §1 | compiled; linter warnings only in copied code |

**The one changed line.** mobius-glue's `mobiusGlue_of_curveFacts` was written against qm-pin's
`R1fpPropsU`. In `MobiusEnd.lean`, one line destructures `h1' : R1fpProps Y' Φ'` in the kernel's
clause order instead. Every other line is verbatim, and `py/verbatim.py` checks this.

## 8. What remains

- **(L0)**, the finiteness theorem for proper morphisms (here only `H⁰` of the structure sheaf of
  a clopen piece), is a textbook leaf and is not in Mathlib v4.35. It is the smallest statement of
  the three.
- **(G1)** is the remaining geometric glue. A finer cut, argued but not stated in Lean:
  - (G1-i) `σ` and `ρ` are algebraically dependent on `W`, because the function field of a curve
    has transcendence degree 1. This could build on infra-smooth-dim's
    `topologicalKrullDim_eq_of_smooth`.
  - (G1-ii) the image of a complete irreducible curve in `P¹ × P¹` is closed, and every closed
    point of it lifts to a `K`-point.
  - (G1-iii) irreducible plane curves are hypersurfaces `V(P)` (Hartshorne I.1.13), with the
    closure statement (c).
  - None of these is in Mathlib v4.35: there is no `P¹ × P¹` as a scheme with its points, and no
    function fields of curves with transcendence degree.
- **T5** is unchanged (an existing textbook leaf).
- **Integration.** `MobiusFinal.lean` is self-contained over the kernel and Mathlib. Integrating
  it means adding the C2K/C3K/L0 sections, curve-facts and mobius-glue's math and infra-smooth-dim's
  dimension theory as kernel modules, and replacing the `GluePieces` field `MobiusGlue` (pin-apply's
  `GluePiecesPin`) by the three named statements.
