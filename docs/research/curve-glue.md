# curve-glue: C2K and C3K reduced, and the CM-point gap in `MobiusGlue` closed

Task curve-glue, 2026-11-13. Base f90cf864, merged with `origin/wip/infra-smooth-dim` (2b0e44f4).
Scratch: `scratch/curve-glue/` (results log `log.md`). No file under `ZInQKernel/`, `blueprint/` or
another task's directory was edited. This is model work only; no human has reviewed it.

Marks: **VERIFIED** means compiled, computed, or read in a file. **STANDARD** means published,
with a reference. **UNVERIFIED** means a theorem number recalled without a source (there is no
network here).

## 1. Result

**The kernel's `MobiusGlue` now rests on three named statements, and everything between them is
compiled Lean:**

- **(L0) `FiniteGlobalSections`**, a textbook leaf: the finiteness theorem for proper morphisms,
  for `H⁰(𝒪)`.
- **(G1') `ImagePlaneCurveClosed`**, glue: the image of a component of the curve under `(σ, ρ)` is
  a plane curve.
- **T5 `ObjBridge.TorsionStructure`**, the existing textbook leaf.

The parallel task infra-smooth-dim proved the third curve-facts input, C1b `SmoothStalkDimOne`, so
it is no longer an assumption. Its proof is copied verbatim.

`scratch/curve-glue/MobiusFinal.lean` compiles with 0 errors and axioms
`[propext, Classical.choice, Quot.sound]` (VERIFIED, `run_MobiusFinal.txt`). It contains:

```lean
theorem LeafQM.AV.CurveGlue.mobiusGlue_of_L0_G1'_T5 (hL0 : FiniteGlobalSections)
    (hG : ImagePlaneCurveClosed) (hT : ObjBridge.TorsionStructure) : LeafQM.AV.Pin.MobiusGlue
theorem LeafQM.AV.CurveGlue.mobiusGlueNoCM_of_L0_G1'_T5 (hL0 : FiniteGlobalSections)
    (hG : ImagePlaneCurveClosed) (hT : ObjBridge.TorsionStructure) (h : R1R2fp) : MobiusGlueNoCM
theorem LeafQM.AV.Pin.curveFacts_of_L0_G1' (hL0 : FiniteGlobalSections)
    (hG : ImagePlaneCurveClosed) : CurveRatFactor ∧ CurveSurj
```

`LeafQM.AV.Pin.MobiusGlue` is the kernel's definition in `ZInQKernel/HDecomp/QM/Pin.lean`. The
file imports that module and does not redefine the name. `MobiusGlueNoCM` is `MobiusGlue` with
its CM-object premise removed.

The file also has variants with the intermediate statements as hypotheses:

- with (G1) `ImagePlaneCurve`: `mobiusGlue_of_L0_G1_T5`;
- with (L) `GlobalFunctionsConst`: `mobiusGlue_of_L_G1_T5`;
- with C1b as a hypothesis: `mobiusGlue_of_glue`, in the lighter file `MobiusEnd.lean`, which does
  not import all of Mathlib.

**The assigned Props:**

| assigned Prop | result | Lean | file |
|---|---|---|---|
| C2K `ConstOrOntoAlgClosed` | **proved from (L)** `GlobalFunctionsConst`; (L) is **proved from (L0)** | `constOrOntoAlgClosed_of : GlobalFunctionsConst → ConstOrOntoAlgClosed`; `globalFunctionsConst_of : FiniteGlobalSections → GlobalFunctionsConst` | `C2K.lean`, `L0.lean` |
| C3K `RatFactorAlgClosed` | **proved from (G1)**, and (G1) **from C2K and (G1')**; the rest is Lean-proved algebra (resultants, Gauss's lemma, separability in characteristic 0, Bezout-type finiteness) | `ratFactorAlgClosed_of : ImagePlaneCurve → RatFactorAlgClosed`; `imagePlaneCurve_of : ConstOrOntoAlgClosed → ImagePlaneCurveClosed → ImagePlaneCurve` | `C3K.lean` |
| CM-point gap in `MobiusGlue` | **closed** (§3) | `cm_points_of_R1R2fp`, `cm_points_of_R1R2fpRep`, `mobiusGlue_noCM_of` | `CMPoints.lean` |

For the CM-point gap: the CM points exist on every triple, derived from `CMExists`, `X6Surj` and
the bijectivity of `Φ`. The CM premise of `MobiusGlue` is discharged by the leaf bundle, so nothing
needs to be added to `MobiusGlue`'s hypotheses.

No statement was changed. Every copied declaration is textually identical to its source. The check
is `py/verbatim.py` (26 checks, all IDENTICAL; output `verbatim.txt`, VERIFIED). The one exception
is a single proof line in the copied `mobiusGlue_of_curveFacts`, described in §7.

## 2. The named Props

| name | kind | content | status |
|---|---|---|---|
| **(L0) `FiniteGlobalSections`** | **textbook leaf** | `X → Spec K` proper over any field `K`, `W ⊆ X` open and closed ⇒ `Γ(W, 𝒪_X)` is a finite `K`-module (`(cstHom f W).Finite`) | STANDARD: EGA III₁ 3.2.1 (coherence of `f_*` for proper `f`); Hartshorne II.5.20 / III.8.8 for projective `X` (numbering UNVERIFIED); not in Mathlib v4.35 |
| **(G1') `ImagePlaneCurveClosed`** | **glue** | setting of C3K without characteristic 0 (`W` the component of `p₀`, `σ` nonconstant on its `K`-points); see the list below | STANDARD (§6); not in Mathlib v4.35 (no `P¹ × P¹`, no plane curves) |
| T5 `ObjBridge.TorsionStructure` | textbook leaf (existing) | `A(K̄)[n] ≅ (ℤ/n)^{2g}` (Mumford §4) | already in `TextbookLeaves` |
| (L) `GlobalFunctionsConst` | intermediate, **proved from (L0)** | `K = K̄`, `X → Spec K` proper and smooth of relative dimension 1, `W` open, closed and preconnected, `s ∈ Γ(X, W)` ⇒ `s − c` is nilpotent for some `c ∈ K` | `globalFunctionsConst_of` (VERIFIED). Also a consequence of "Γ = K for proper, connected, reduced schemes over `K̄`" (Hartshorne Ex. II.4.5(d) / I.3.4, UNVERIFIED) |
| (G1) `ImagePlaneCurve` | intermediate, **proved from C2K and (G1')** | as (G1'), with (b'') replaced by (b) below | `imagePlaneCurve_of` (VERIFIED) |
| C1b `SmoothStalkDimOne` | glue, **proved** by infra-smooth-dim | stalks at closed points of a smooth curve over a field have dimension 1 | `smoothStalkDimOne`, copied verbatim into `MobiusFinal.lean` (VERIFIED) |

**The content of (G1').** Either `ρ ≡ ∞` on the `K`-points of `W`, or there is an irreducible
`P ∈ K[x][y]` of `y`-degree ≥ 1 with:

- (a) `P(σ(p), ρ(p)) = 0` at the `K`-points of `W` where both values are finite;
- (c) `σ(p) = t` finite and `ρ(p) = ∞` ⇒ `lc_y(P)(t) = 0`;
- (b'') the affine image `{(σ(p), ρ(p))}` is Zariski closed: it is the common zero set in `K²` of
  some `S ⊆ K[x][y]`.

**The clause (b) of (G1).** Every `(t, u) ∈ K²` with `P(t, u) = 0` equals `(σ(p), ρ(p))` for some
`K`-point `p` of `W`.

**Lean-proved intermediate results:**

| name | content |
|---|---|
| `constOrOntoAlgClosed_of` | C2K from (L) |
| `globalFunctionsConst_of` | (L) from (L0) |
| `ratFactorAlgClosed_of` | C3K from (G1) |
| `imagePlaneCurve_of` | (G1) from C2K and (G1') |
| `Alg.exists_two_roots` | `P ∈ K[x][y]` irreducible with `deg_y P ≥ 2`, `K` algebraically closed of characteristic 0 ⇒ some fibre `P(t, ·)` has two distinct roots |
| `Alg.finite_common_zeros` | `P` irreducible with `deg_y P ≥ 1` and `P ∤ Q` ⇒ `{P = Q = 0} ⊆ K²` is finite |
| `Alg.isCoprime_coeff_of_irreducible` | `P = A y + B` irreducible ⇒ `A`, `B` coprime |
| `exists_nilpotent_sub_of_finite` | a finite algebra over `K = K̄` with only the trivial idempotents is `K` plus nilpotents |
| `idempotent_trivial_of_isPreconnected` | an idempotent section of `𝒪_X` over a preconnected open is `0` or `1` |
| `isUnit_of_ev_ne_zero` | a section that is nonzero at every `K`-point of its domain is a unit (Jacobson) |
| `ev_cst` | the value of the constant section `c` at a `K`-point is `c` |
| `cm_points_of_objects`, `cm_points_of_R1R2fp(Rep)` | the CM points over `0, ∞, −16/27` exist |

## 3. The CM-point gap

**The review's concern.** The proof of `MobiusGlue` (mobius-glue's `mobiusGlue_of_curveFacts`)
uses `ℚ̄`-points `y` of `Y'` whose objects have CM by `ℤ[i]`, `ℤ[ζ₃]` and `ℤ[√−6]`, together with
the values `0, ∞, −16/27` at those points. But `R2fpProps` only states the one-way implications
"CM ⇒ value".

**How it is settled** (all compiled in `CMPoints.lean`):

1. **`MobiusGlue` already assumes the CM objects.** Its fifth premise in the kernel
   (`ZInQKernel/HDecomp/QM/Pin.lean`) is the existence of `QML3` objects over `ℚ̄` with each of the
   three CM types.
2. **CM points follow from the objects.** Given the objects, the points exist on every triple
   satisfying `R2fpProps`, because `Φ Qbar` is a bijection onto `M3 Qbar`. Take
   `y = (Φ Qbar).symm (M3.mk P)`; the one-way clause then gives the value at `y`
   (`cm_points_of_objects`).
   - Only the one-way clauses are used.
   - The converse clauses are never needed: the Möbius map is pinned by the three points where
     both `π'` and `π ∘ g` are known.
3. **The objects follow from the leaf bundle.** In `R1R2fp`, `CMExists` gives CM points on `X₆`.
   The second half of `X6Surj` says every QM pair over `ℚ̄` has a level-3 structure. The kernel's
   `cm_objects_of_R1R2fp` combines the two. Hence `cm_points_of_R1R2fp`.
4. **The repaired bundle works too.** `R1R2fpRep` (leaf-adopt) has no `CMExists`, only the
   biconditional `R2X6PropsIff`. There, `CMExists` follows from the biconditionals together with
   the first half of `X6Surj` (`π₆` is onto) (`cmExists_of_iff`, copied). Hence
   `cm_points_of_R1R2fpRep`.
5. **The premise costs nothing.** `mobiusGlue_noCM_of : MobiusGlue → R1R2fp → MobiusGlueNoCM`.
   The consumers of `MobiusGlue` already supply the premise this way (pin-apply's
   `sameTripleMor_of_leaves`).

So nothing needs to be added to `MobiusGlue`'s hypotheses.

## 4. C2K from (L) (`C2K.lean`), and (L) from (L0) (`L0.lean`)

**Values at `K`-points.**

- `ev p : Γ(X, O) →+* K` is the value of a section at a `K`-point `p`: the residue map, then the
  embedding `κ(x) → K` of `p`. This is exactly how `ToP1.val` evaluates.
- `cst f O c` is the constant `c`: the image of `c` under `K = Γ(Spec K) → Γ(X) → Γ(X, O)`.
- `ev_cst`: constants evaluate to themselves at every section `p` of `f`. Proof: Mathlib's
  `Scheme.germ_stalkClosedPointTo` and `p ≫ f = 𝟙`.

**Units.** In a Jacobson scheme of finite type over `K = K̄`, closed points are `K`-points
(Mathlib's `pointOfClosedPoint`). So a section that is nonzero at every `K`-point of its domain
has `D(s)` equal to the whole domain, and is a unit (`isUnit_of_ev_ne_zero`).

**C2K** (`constant_of_missed`). Let `W` be the connected component of `p₀`; it is open because `X`
is Noetherian. Suppose `σ = [U, V, f, g]` misses a value `t` on the `K`-points of `W`.

- **Case `t = ∞`.** Every `K`-point of `W` lies in `U`, so `W ⊆ U` (Jacobson). By (L), `f|_W` is
  constant up to nilpotents, so `σ` is constant on `W`.
- **Case `t = a ∈ K`.**
  1. `f − a` is a unit on `W ∩ U`, and `1 − a g` is a unit on `W ∩ V`. Both are checked at
     `K`-points, using `fg = 1` on `U ∩ V` and `g = 0` off `U`.
  2. `1/(f − a)` and `g/(1 − a g)` agree on the overlap, so they glue to `h ∈ Γ(X, W)` (Mathlib's
     `objSupIsoProdEqLocus`).
  3. By (L), `h` takes a single value `c` at every `K`-point of `W`.
  4. If `W ∩ U` has a `K`-point, then `c ≠ 0`. This excludes `K`-points of `W` off `U`, where
     `h = g/(1 − a g) = 0`. So `σ = a + 1/c` on `W`.
  5. Otherwise `σ ≡ ∞` on `W`.

**(L) from (L0)** (`globalFunctionsConst_of`). `Γ(X, W)` is a finite `K`-algebra by (L0).

- **Idempotents are trivial.** At each point, the germ of an idempotent is 0 or 1 in the local
  ring, so `W` is the disjoint union of the opens `D(e)` and `D(1 − e)`. Since `W` is preconnected,
  one of them is empty (`idempotent_trivial_of_isPreconnected`).
- **Every element is a unit or nilpotent.** The algebra is Artinian. Fitting's argument:
  `s^n = s^{n+1} y` makes `s^n y^n` idempotent, so it is 0 or 1.
- **Conclusion.** For an eigenvalue `c` of multiplication by `s` (which exists since `K = K̄`),
  `s − c` is a zero divisor. So `s − c` is not a unit, hence nilpotent
  (`exists_nilpotent_sub_of_finite`).

## 5. C3K from C2K and (G1') (`C3K.lean`)

**Two roots in a fibre** (`Alg.exists_two_roots`). Let `P ∈ K[x][y]` be irreducible with
`deg_y P = d ≥ 2`.

1. `P` is primitive and stays irreducible over `K(x)` (Gauss's lemma). In characteristic 0 it is
   then separable, so `r = Res_y(P, ∂P/∂y) ∈ K[x]` is nonzero (`resultant_ne_zero`,
   `resultant_map_map`).
2. Choose `t` with `r(t) · lc(P)(t) ≠ 0`. Then `P(t, y)` has degree `d`, and its resultant with
   its derivative is `r(t) ≠ 0`, so it is separable (`resultant_eq_zero_iff`).
3. Over `K = K̄`, a separable polynomial of degree `d` has `d ≥ 2` distinct roots (`nodup_roots`,
   `Splits.natDegree_eq_card_roots`).

**Bezout-type finiteness** (`Alg.finite_common_zeros`). Let `P` be irreducible with `deg_y P ≥ 1`,
and suppose `P ∤ Q`.

1. `P` and `Q` are coprime over `K(x)` (Gauss's lemma), so `Res_y(P, Q) ∈ K[x]` is nonzero.
2. `Res_y(P, Q) = AP + BQ` (`exists_mul_add_mul_eq_C_resultant`), so every common zero has its
   `x`-coordinate among the roots of the resultant.
3. Each fibre `P(t, ·)` is a nonzero polynomial. If `P(t, ·) ≡ 0`, then `x − t` divides the
   content of `P`, and a primitive `P` has unit content.

**(G1) from C2K and (G1')** (`imagePlaneCurve_of`). Only (b) needs proof.

1. By C2K, `σ` is onto `P¹(K)` on `W`, because it is nonconstant there. By (c), points over the
   cofinitely many `t` with `lc(P)(t) ≠ 0` have `ρ` finite. So the affine image `Im` is infinite.
2. `Im = V(S)` by (b''), and `Im ⊆ V(P)` by (a).
3. Take `Q ∈ S`. If `P ∤ Q`, then `V(P) ∩ V(Q) ⊇ Im` would be finite, which is impossible. So
   `P ∣ Q`.
4. Hence `V(P) ⊆ V(S) = Im`.

**C3K from (G1)** (`ratFactorAlgClosed_of`).

- If `ρ ≡ ∞` on `W`, take `[F : G] = [1 : 0]`.
- Otherwise `deg_y P = 1`. If `deg_y P ≥ 2`, two roots `u ≠ u'` of some `P(t, ·)` are hit by (b).
  That gives two `K`-points of `W` in one `σ`-fibre with different `ρ`, contradicting the fibre
  hypothesis.
- So `P = A y + B`, with `A, B` coprime. Take `[F : G] = [−B : A]` and let `σ(p) = t` be finite.
  - If `ρ(p) = ∞`, clause (c) gives `A(t) = 0`.
  - If `ρ(p) = u` is finite, clause (a) gives `A(t) u + B(t) = 0`. `A(t) = 0` would force
    `B(t) = 0`, contradicting coprimality.

**Characteristic 0.** C3K is false in characteristic `p`: take `σ = ρ^p` (curve-facts §3).
Characteristic 0 enters only through the separability step of `Alg.exists_two_roots`; (G1') holds
in every characteristic. For `σ = ρ^p` it gives `P = y^p − x`, whose fibres have a single root.

## 6. Why the named Props are true

**(L0) `FiniteGlobalSections`.**

- `W` is open and closed, hence a closed subscheme, and `W → Spec K` is proper.
- By the finiteness theorem for proper morphisms, `Γ(W, 𝒪_W) = H⁰(W, 𝒪_W)` is a finite
  `K`-vector space. The `K`-structure is the one through `f`, i.e. `cstHom f W`.
- Neither smoothness nor algebraic closedness is assumed.
- This is the published statement specialized to `𝓕 = 𝒪_W` and `H⁰` (STANDARD; EGA III₁ 3.2.1,
  numbering UNVERIFIED).

**(G1') `ImagePlaneCurveClosed`** (STANDARD; references UNVERIFIED).

- **Setting.** `W` is a complete nonsingular irreducible curve: smooth implies normal, so connected
  components are irreducible.
- **The image `D`.** Its image `D` under `(σ, ρ) : W → P¹ × P¹` is closed (`W → Spec K` is proper
  and `P¹ × P¹` is separated) and irreducible. It is not a point, since `σ` is nonconstant.
- **The polynomial `P`.** If `ρ ≢ ∞`, then `D ∩ 𝔸²` is nonempty, open and dense in `D`, and it is
  an irreducible curve in `𝔸²`.
  - So `D ∩ 𝔸² = V(P)` with `P` irreducible: `K[x, y]` is a UFD and height-one primes are principal
    (Hartshorne I.1.13).
  - `P ∉ K[x]`, since otherwise `σ` would be constant on a dense open subset of `W`.
- **(a)** is `D ∩ 𝔸² ⊆ V(P)`.
- **(b'')** `D ∩ 𝔸²` is closed in `𝔸²`, and its points are exactly the images of `K`-points of
  `W`. A fibre over a closed point is a nonempty closed set of finite type over `K`, so it contains
  a closed point, which is a `K`-point.
- **(c)** A point `(t, ∞)` of `D` lies in the closure of `V(P)` in `𝔸¹ × P¹`. That closure lies in
  the zero set of the `y`-homogenization `Σ aᵢ(x) y₁ⁱ y₀^{d−i}`, which at `y₀ = 0` reads
  `a_d(t) = 0`.
- **Classification.** It is glue: it combines several textbook facts and is not one printed
  theorem.

**Independent check (model, not human).** A fresh agent was given only the Lean files, not this
report's arguments, and asked for counterexamples.

- **`GlobalFunctionsConst`:** it judged it TRUE and not vacuous.
  - Empty `W`: `Γ = 0`.
  - Nonempty `W`: `Γ(W)` is a finite connected `K`-algebra.
  - `X = P¹_K` satisfies the hypotheses.
- **`ImagePlaneCurve`:** it judged it TRUE without characteristic 0, and not vacuous.
  - It checked the cases `ρ ≡ ∞`, `ρ ≡ b` (`P = y − b`) and `ρ` nonconstant.
  - It checked the variable order in `evalXY` and the `y`-leading coefficient.
  - Spot checks: `ρ = 1/σ` gives `P = xy − 1`; Frobenius gives `P = y^p − x`.
- **A second fresh agent** (same instructions) checked (L0) and (G1').
  - `FiniteGlobalSections`: TRUE, not vacuous. `RingHom.Finite` is `Module.Finite` for the
    `K`-structure through `f`; empty `W` is fine; properness alone suffices. Clopenness is needed:
    for a merely open `W`, `𝔸¹ ⊂ P¹` fails.
  - `ImagePlaneCurveClosed`: TRUE, not vacuous. `S = {P}` works. `S = ∅` would force the image to
    be all of `K²`, so (b'') is a real constraint.

## 7. Files and verification

All runs used `lake env lean`, one process at a time. Every file has 0 errors and axioms
`[propext, Classical.choice, Quot.sound]` (VERIFIED, the `run_*.txt` files). The composite files
are generated by `py/assemble.py`.

| file | content | result |
|---|---|---|
| `CMPoints.lean` | the CM-point gap (§3) | 0 warnings |
| `C2K.lean` | C2K from (L) | 0 warnings |
| `L0.lean` | (L) from (L0) | 0 warnings |
| `C3K.lean` | C3K from (G1); (G1) from C2K and (G1'); the algebra | 0 warnings |
| `CurveGlueAll.lean` | `CurveFacts.lean` verbatim, `C2K.lean`, `C3K.lean`; `curveFacts_of_glue`, `curveFacts_of_glue'` | 0 warnings |
| `MobiusEnd.lean` | imports the kernel's `QM.Pin`; mobius-glue's §1-§5 and §7-§8 (from `scratch/mobius-glue/MobiusGlue.lean`), `CurveGlueAll`, `CMPoints`; `mobiusGlue_of_glue : SmoothStalkDimOne → (L) → (G1) → T5 → MobiusGlue` | linter warnings only, in copied mobius-glue code |
| `MobiusFinal.lean` | `import Mathlib`, infra-smooth-dim's dimension theory (verbatim), `MobiusEnd`, `L0`; the theorems of §1 | linter warnings only, in copied code |

**The one changed line.** mobius-glue's `mobiusGlue_of_curveFacts` was written against qm-pin's
`R1fpPropsU`. In `MobiusEnd.lean`, one line destructures `h1' : R1fpProps Y' Φ'` in the kernel's
clause order instead. Every other line is verbatim, and `py/verbatim.py` checks this.

## 8. What remains

- **(L0)** is a textbook leaf, not in Mathlib v4.35. It is the finiteness theorem, needed here only
  for `H⁰` of the structure sheaf of a clopen piece of a proper scheme over a field.
- **(G1')** is the remaining geometric glue. A finer cut, argued but not stated in Lean:
  - (G1-i) `σ` and `ρ` are algebraically dependent on `W` (the function field of a curve has
    transcendence degree 1). This could build on infra-smooth-dim's
    `topologicalKrullDim_eq_of_smooth`.
  - (G1-ii) the image of `W` in `P¹ × P¹` is closed and irreducible. This gives (b'') and the
    choice of an irreducible `P`.
  - (G1-iii) irreducible plane curves are hypersurfaces (Hartshorne I.1.13), with the closure
    statement (c).
  - Mathlib v4.35 has none of `P¹ × P¹` as a scheme with its points, function fields of curves
    with their transcendence degree, or plane curves.
- **T5** is unchanged.
- **Integration.** `MobiusFinal.lean` is self-contained over the kernel and Mathlib. Integrating it
  means adding kernel modules for:
  - the C2K, C3K and L0 sections;
  - curve-facts, and mobius-glue's mathematics;
  - infra-smooth-dim's dimension theory.

  Then replace the field `MobiusGlue` (pin-apply's `GluePiecesPin`) by (L0) and (G1'). T5 is
  already in `TextbookLeaves`.
