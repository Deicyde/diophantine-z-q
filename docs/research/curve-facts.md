# curve-facts: `CurveRatFactor` and `CurveSurj` reduced to three per-component curve facts

Task curve-facts, 2026-11-13. Base 2dd83306, merged with `origin/wip/mobius-glue`. Scratch:
`scratch/curve-facts/` (results log `log.md`). No file under `ZInQKernel/`, `blueprint/` or
another task's directory was edited. Model work only; no human has reviewed it.

## 1. Result

**Both curve facts of mobius-glue are proved in Lean from three smaller named facts, each stated
over an arbitrary field (algebraically closed for the two curve leaves), as in Hartshorne.** One
is a textbook leaf and two are glue. Source: `scratch/curve-facts/CurveFacts.lean`. It compiles
with 0 errors, 0 warnings and axioms `[propext, Classical.choice, Quot.sound]` (VERIFIED, `run8.txt`):

```lean
theorem curveFacts_of_leaves (h1 : SmoothStalkDimOne) (h2 : ConstOrOntoAlgClosed)
    (h3 : RatFactorAlgClosed) : CurveRatFactor ∧ CurveSurj
```

- `CurveSurj` uses only C1b and C2K.
- `CurveRatFactor` uses only C2K and C3K.

| name | kind | content | status |
|---|---|---|---|
| `SmoothStalkDimOne` (C1b) | glue (dimension theory) | if `X → Spec K` is smooth of relative dimension 1 over any field `K` and `x` is a closed point, then `ringKrullDim 𝒪_{X,x} = 1` | STANDARD; true (§3); not in Mathlib |
| `ConstOrOntoAlgClosed` (C2K) | **textbook leaf** | `X` proper and smooth of relative dimension 1 over an algebraically closed `K`, and `σ : X → P¹`: on the `K`-points of each connected component of `X`, `σ` is constant or takes every value in `P¹(K)` | Hartshorne II.6.8 (UNVERIFIED numbering); not in Mathlib |
| `RatFactorAlgClosed` (C3K) | glue (textbook consequence) | the same setting with `char K = 0`: on a connected component where `σ` is nonconstant, a map `ρ` constant on the `σ`-fibres is `[F : G] ∘ σ` with `F, G ∈ K[X]` coprime | STANDARD (§3); not in Mathlib |

The proof also uses the following intermediate statements, all proved in Lean:

| name | content | proof |
|---|---|---|
| `SmoothCurveNoIsolatedPoint` (C1a) | for `X → Spec K` smooth of relative dimension 1, no point of `X` is open | from C1b (`smoothCurveNoIsolatedPoint_of`, §8): an open point is closed (Jacobson) and maximal for specialization, so `dim 𝒪_{X,x} = coheight x = 0` by Mathlib's `ringKrullDim_stalk_eq_coheight` |
| `GeomCompInfinite` (C1) | each geometric component of a proper smooth curve `S/ℚ` has infinitely many `ℚ̄`-points | from C1a (`geomCompInfinite_of`) |
| `GeomCompConstOrOnto` (C2) | C2K for `S/ℚ`, with `ℚ̄`-points and geometric components | from C2K by base change to `ℚ̄` (`geomCompConstOrOnto_of`) |
| `GeomCompRatFactor` (C3) | C3K for `S/ℚ` | from C3K by base change (`geomCompRatFactor_of`) |
| `GeomCompFinite` (C4) | `S_ℚ̄` has finitely many connected components meeting `ℚ̄`-points | from Mathlib (`geomCompFinite`) |
| `Mob.exists_interp` | any assignment of `P¹(K)`-values at finitely many nodes is realised by a coprime pair `[F : G]` | Lagrange interpolation |

The chain is:

- `curveSurj_of_comp : C1 → C2 → CurveSurj`;
- `curveRatFactor_of_comp : C2 → C3 → CurveRatFactor` (with C4 and interpolation);
- `curveFacts_of_named : C1a → C2 → C3 → …`;
- `curveFacts_of_algClosed : C1a → C2K → C3K → …`;
- `curveFacts_of_leaves : C1b → C2K → C3K → …`.

Combined with mobius-glue's `mobiusGlue_of_curves (hRF : CurveRatFactor) (hSu : CurveSurj)
(hT : ObjBridge.TorsionStructure)`, qm-pin's `MobiusGlue` therefore rests on C1b, C2K, C3K and
the existing textbook leaf T5.

**Verbatim copies.** `CurveRatFactor`, `CurveSurj` and `Mob.ratEval` were copied into
`CurveFacts.lean` §0. The script `scratch/curve-facts/py/verbatim.py` compares each declaration
with its source in `scratch/mobius-glue/MobiusGlue.lean`, docstring included: IDENTICAL
(VERIFIED). Their other dependencies (`ToP1`, `ToP1.val`, `fieldPt`, `Qbar`) are imported
unchanged from `ZInQKernel/HDecomp/QM/Pairs.lean`. No statement was changed.

## 2. Definitions (all genuine; `CurveFacts.lean` §1)

```lean
abbrev bcQbar (S : Over (Spec (CommRingCat.of ℚ))) : Scheme.{0} :=
  pullback S.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))       -- S_ℚ̄
def bcPt (y : fieldPt Qbar ⟶ S) : Spec (CommRingCat.of Qbar) ⟶ bcQbar S :=
  pullback.lift y.left (𝟙 _) _                                            -- the induced section
def geomComp (y : fieldPt Qbar ⟶ S) : Set (bcQbar S) :=
  connectedComponent (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1
```

`geomComp y` is the connected component of `S_ℚ̄` containing the closed point that `y` defines.
For `S` smooth over `ℚ`, connected components of `S_ℚ̄` are irreducible: smooth implies normal,
hence locally irreducible. Every ingredient is Mathlib's: `pullback`, `pullback.lift`,
`Scheme.SpecToEquivOfField` and `connectedComponent`. No structure was invented.

## 3. The named facts and why they are true

The ℚ̄-forms C2 and C3 below take the hypotheses of the original facts: `S : Over (Spec ℚ)`,
`IsProper S.hom` and `SmoothOfRelativeDimension 1 S.hom`. The leaves actually assumed are their
field-level forms C2K and C3K (end of this section). The truth arguments are the same, with `C` a
connected component of `X` instead of `S_ℚ̄`.

- **C1a `SmoothCurveNoIsolatedPoint`**: `∀ K [Field K] (X : Scheme) (f : X ⟶ Spec K),
  SmoothOfRelativeDimension 1 f → ∀ x, ¬ IsOpen {x}`.
  - Why true (STANDARD): every point has an open neighbourhood étale over `𝔸¹_K`. So every
    nonempty open set of `X` is infinite: an étale map is open and quasi-finite, and a nonempty
    open subset of `𝔸¹_K` contains infinitely many closed points for every field `K`. An open
    point would be a nonempty finite open set. The generic point of a component is not open
    either.
  - What Mathlib lacks: dimension theory for smooth morphisms, i.e. that relative dimension `n`
    means `n`-dimensional fibres. `Algebra.IsStandardSmoothOfRelativeDimension` exists, but
    nothing connects it to Krull dimension.
- **C2 `GeomCompConstOrOnto`**: for `σ : ToP1 S.left` and `y₀`, either `σ(y) = σ(y₀)` for every
  `ℚ̄`-point `y` with `geomComp y = geomComp y₀`, or every `t ∈ P¹(ℚ̄)` is `σ(y)` for some such `y`.
  - Source: Hartshorne, *Algebraic Geometry*, Prop. II.6.8 (UNVERIFIED numbering, recalled from
    memory and as cited by mobius-glue). A morphism from a complete nonsingular curve to a curve
    is constant or surjective. Here it is applied to a connected component of `S_ℚ̄`, which is a
    complete nonsingular irreducible curve over `ℚ̄`.
  - Dictionary: `ℚ̄`-points `y` of `S` over `ℚ` correspond to sections of `S_ℚ̄ → Spec ℚ̄`, which
    correspond to closed points of `S_ℚ̄`. The first step is the pullback's universal property;
    the second is Mathlib's `pointEquivClosedPoint`, and both are used in §6 of the Lean file.
    Also `σ(y) = (σ ∘ pr₁)(bcPt y)` (kernel `ToP1.val_comp_right`).
  - Kind: a leaf in the sense of the task, since the Lean statement is a consequence of the
    printed proposition through this dictionary.
  - What Mathlib lacks: `P¹` as a scheme with `P¹(K) = K ∪ {∞}`, and curves. Mathlib does have
    `IsProper → UniversallyClosed`, the valuative criteria and `Proj` proper.
- **C3 `GeomCompRatFactor`**: if `σ` is nonconstant on the component of `y₀`, and `ρ` is constant
  on the `σ`-fibres within that component, then `ρ = Mob.ratEval F G ∘ σ` on its `ℚ̄`-points with
  finite `σ`-value, for some coprime `F, G ∈ ℚ̄[X]`. Why true (STANDARD; references UNVERIFIED):
  - Let `C` be the component. Then `σ|_C : C → P¹` is finite (II.6.8) and
    `ℚ̄(σ) ⊆ M := ℚ̄(σ, ρ) ⊆ ℚ̄(C)`.
  - Let `D` be the smooth complete curve with function field `M` (II.6.7 / I.6.12). Then
    `C → D → P¹`, and `C → D` is onto (II.6.8).
  - `D → P¹` has degree `[M : ℚ̄(σ)]` and is separable (characteristic 0). So all but finitely
    many fibres have exactly that many points (II.6.9 and IV.2.2).
  - Points of `D` in one fibre that are not over the finitely many singular points of the image
    of `(σ, ρ)` have different `ρ`. So the fibre condition forces `M = ℚ̄(σ)`, i.e. `ρ = R(σ)` in
    `ℚ̄(C)`.
  - The two morphisms `ρ` and `R ∘ σ` agree on a dense open set of the reduced `C` and `P¹` is
    separated, so they agree everywhere. Write `R = [F : G]` in lowest terms.
  - Properness of `C` is used through II.6.8. Without it, `CurveRatFactor` fails, by
    mobius-glue's `(𝔸¹ ∖ 0) ⊔ pt` example; C3 itself only uses it through `σ|_C` being finite.
  - Classified as glue: it is a consequence of several textbook results, not one printed theorem.

**Not vacuous or inert.** Each named fact quantifies over all proper smooth curves `S/ℚ` (C1a
over all `X` smooth of relative dimension 1 over a field), with genuine `ToP1` maps. None
quantifies over an invented structure, and none is a disguised form of its consequence:

- C2 and C3 are per-component statements.
- The glue that combines components (the fibre condition across components, finiteness of
  components, interpolation when every component is constant) and the passage from points of
  `S_ℚ̄` to `ℚ̄`-points of `S` are proved in Lean.

**Field-level forms (§7 of the Lean file).**

- C2K and C3K quantify over every algebraically closed field `K : Type`, every scheme
  `X : Scheme.{0}` and every proper `f : X ⟶ Spec K` smooth of relative dimension 1.
- `K`-points are sections `p` with `p ≫ f = 𝟙`; components are
  `connectedComponent (ptOf p)`, where `ptOf p` is the point of `p`.
- C3K adds `[CharZero K]`. It is false in characteristic `p`: take `X = P¹`, `σ = ρ^p`. Frobenius
  is bijective on `K`-points, so `ρ` is constant on the `σ`-fibres, but `ρ` is not a rational
  function of `σ`.
- The ℚ̄-versions C2 and C3 follow by base change to `ℚ̄`, through these steps (all proved):
  - `y ↦ bcPt y`, with inverse `ptOfSection`;
  - `bcPt_ptOfSection`;
  - `σ(y) = (σ ∘ pr₁)(bcPt y)` (`val_bcPt`, from the kernel's `ToP1.val_comp_right`);
  - Mathlib's instances that properness and `SmoothOfRelativeDimension` are stable under base
    change.


**Independent check (model, not human).** A fresh agent was given only the Lean statements of
C1a, C2K and C3K and the kernel's `ToP1`/`ToP1.val`, and asked for counterexamples. It was not
given C1b, which was added afterwards. Its findings:

- All three are TRUE and none is vacuous: `X = P¹_K` satisfies every hypothesis.
- C1a holds over every field, and properness is not needed.
- C2K needs properness (`𝔸¹ ⊂ P¹` misses `∞`) and algebraic closedness (over `ℝ`, `t²` misses
  negative values). Smoothness and dimension 1 are not needed: a closed irreducible image in
  `P¹` is a point or everything, closed points are `K`-points, and the components are handled
  through `connectedComponent`.
- C3K needs characteristic 0 (`σ = t^p`) and algebraic closedness (over `ℝ`, `σ = t³`, `ρ = t`).
  The case "`ρ ≡ ∞` on the component" is covered by `F = 1, G = 0`.
- C1b (stalk dimension 1 at closed points of a smooth curve over a field) is standard. It is
  stronger than C1a and was not part of the review.

## 4. What the Lean proofs do (`CurveFacts.lean`)

- **§3 `geomCompFinite`** (C4).
  - `S_ℚ̄` is a Noetherian scheme. `IsLocallyNoetherian` comes from Mathlib's instance for a
    pullback of a locally finite type morphism; `CompactSpace` comes from quasi-compactness of
    `S.hom`.
  - So it has finitely many irreducible components (`NoetherianSpace.finite_irreducibleComponents`).
  - Each point's irreducible component lies in its connected component
    (`irreducibleComponent_subset_connectedComponent`), so `range geomComp` is the image of a
    finite set.
- **§4 `Mob.exists_interp`**. Let `G = ∏_{r(t) = ∞} (X - t)`, and let `F` be the Lagrange
  interpolant (`Lagrange.interpolate`) with `F(t) = v·G(t)` where `r(t) = v` and `F(t) = 1` where
  `r(t) = ∞`. `F` and `G` are coprime through `F = (X - a)·q + 1` at each root `a` of `G`.
- **§5 `curveSurj_of_comp`**: by C2 on the component of the given point. The constant branch
  makes a fibre contain the whole component, which is infinite by C1.
- **§5 `curveRatFactor_of_comp`**. Two cases:
  - Some component is nonconstant. C3 gives `R` there. C2 makes that component onto `P¹(ℚ̄)`, so
    every `ℚ̄`-point `y` with `σ(y) = t` shares its `σ`-value with a point `y'` of that component.
    The global fibre condition gives `ρ(y) = ρ(y') = R(t)`.
  - Every component is constant. Then `σ` takes finitely many values (C4), and `R` comes from
    `Mob.exists_interp` at those values.
- **§6 `geomCompInfinite_of`** (C1 from C1a).
  - `S_ℚ̄` is Noetherian, so connected components are open (`isOpen_connectedComponent_of_noetherian`,
    proved: the complement is a finite union of irreducible components).
  - `S_ℚ̄` is Jacobson (`LocallyOfFiniteType.jacobsonSpace`). In a Jacobson space a nonempty open
    set with finitely many closed points contains an open point
    (`exists_isOpen_singleton_of_finite_closedPoints`, proved), which C1a excludes.
  - Every closed point `x` of the component is `bcPt y` for a `ℚ̄`-point `y` of `S`: take
    `y = pointOfClosedPoint f x ≫ pr₁` (Mathlib's `AlgClosed/Basic.lean`) and use
    `pullback.hom_ext`.

## 5. Mathlib v4.35 survey (VERIFIED by grep in `.lake/packages/mathlib`)

- **Present and used:**
  - `IsProper`, which extends `IsSeparated`, `UniversallyClosed` and `LocallyOfFiniteType`.
  - `IsNoetherian`, with `LocallyOfFiniteType.isLocallyNoetherian` and pullback instances.
  - `NoetherianSpace.finite_irreducibleComponents`.
  - `JacobsonSpace`, `LocallyOfFiniteType.jacobsonSpace` and `nonempty_inter_closedPoints`.
  - `pointOfClosedPoint` and `pointEquivClosedPoint`: closed points are `K`-points over an
    algebraically closed `K`.
  - `SmoothOfRelativeDimension`, stable under base change.
  - `Lagrange.interpolate`.
- **Present, not needed here:**
  - `ValuativeCriterion` (`IsProper.eq_valuativeCriterion`).
  - `Scheme.functionField`.
  - `Scheme.ordHom`, the order of vanishing at codimension-1 points (`OrderOfVanishing.lean`).
  - `AffineSpace`, and `Proj` proper (`ProjectiveSpectrum/Proper.lean`).
  - `GeometricallyConnected` and `ZariskisMainTheorem.lean`.
- **Absent**, and needed by C1a, C2 and C3:
  - `P¹` as a scheme with its point bijection (the kernel's `ToP1` works around this with
    charts);
  - dimension theory of smooth morphisms, and smooth ⇒ reduced/normal (`Smooth.lean` has no
    `IsReduced` conclusion);
  - curves as a notion, with function fields of transcendence degree 1;
  - the degree of a finite morphism of curves and fibre counts;
  - Hartshorne II.6.8;
  - finiteness of `Γ(X, 𝒪_X)` for proper `X`.

## 6. What remains

- **C1b** is the smallest piece. It needs a dimension theory of smooth morphisms in Mathlib:
  a standard smooth algebra of relative dimension 1 over a field has Krull dimension 1 at every
  maximal ideal. Mathlib's `Algebra.IsStandardSmoothOfRelativeDimension` gives a presentation
  with invertible Jacobian, but nothing in Mathlib computes its dimension.
- **C2** could be reduced further, argued but not compiled, to a "Liouville" fact: on a proper,
  connected, smooth scheme over an algebraically closed field, global functions are constant
  (Hartshorne Ex. II.4.5 / Stacks "proper + geometrically connected + geometrically reduced
  ⇒ `Γ = k`", UNVERIFIED tags). The argument:
  - Suppose `σ` misses a finite `t` on the component `C`. Then `f - t` has no zero at a closed
    point of `C ∩ U`. Since `S_ℚ̄` is Jacobson, `f - t` is a unit on `C ∩ U`.
  - `1/(f - t)` on `C ∩ U` and `g/(1 - t g)` near `C ∖ U` glue to a global function on `C`, which
    is a constant `c`.
  - So `f = t + 1/c` on `C ∩ U`. A clopen argument (`C` connected) makes `σ` constant on `C`.
  - The Lean glue would need two-open sheaf gluing, restriction to the clopen `C`, and
    smooth ⇒ reduced; it was not attempted.
- **C3** is the deepest of the three. A finer cut would separate an algebraic lemma from a
  geometric one:
  - the algebraic lemma: an irreducible `P ∈ ℚ̄[X][Y]` such that `P(t, ·)` has at most one root
    for all but finitely many `t` has `deg_Y P = 1` (char. 0, discriminant);
  - the geometric statement: the image of `(σ, ρ)` on the component is the curve `P = 0`.
  Neither was formalized.
