# model-glue: the glue Props `ModelCoordinate` and `ModelComparison`

Task model-glue (2026-11-13). Base: `wip/integrate-w49` (998b4f79). Targets: the two glue Props
of task vert-witness, `VertWitness.ModelCoordinate` and `VertWitness.ModelComparison`
(`scratch/vert-witness/VertWitness.lean`; docs/research/vert-witness.md §4.3).

## 1. Main result

Both targets are reduced to two named statements, `ModelCoordinateResidue` (glue) and
`CurveBijIso` (a textbook leaf), plus the existing textbook leaf T5. All the glue in between is
proved. VERIFIED: `lake env lean scratch/model-glue/ModelGlue6.lean` exits 0. The file has no
`sorry` and no `axiom`.

```lean
-- ModelCoordinate (verbatim owner statement) from the smaller glue ModelCoordinateResidue
theorem ModelGlue.modelCoordinate_of_residue (h : ModelCoordinateResidue) : ModelCoordinate

-- ModelComparison (verbatim owner statement) from T5 and the textbook leaf CurveBijIso
theorem ModelGlue.modelComparison_of_curveBijIso (hT : ObjBridge.TorsionStructure)
    (hC : CurveBijIso) : ModelComparison

theorem ModelGlue.modelCoordinate_and_modelComparison (hT : ObjBridge.TorsionStructure)
    (hD : ModelCoordinateResidue) (hC : CurveBijIso) : ModelCoordinate ∧ ModelComparison

-- downstream composite: vert-witness's HeckeVertWitness
-- (SmoothFibreReduced is now proved, so it no longer appears as an input)
theorem ModelGlue.heckeVertWitness_of_curveBijIso (hL : ShimuraGoodReduction) (hRR : R1R2fp)
    (hT : ObjBridge.TorsionStructure) (hD : ModelCoordinateResidue) (hC : CurveBijIso) :
    HeckeVertWitness
```

Every `#print axioms` in `scratch/model-glue/compile6_out.txt` reads
`[propext, Classical.choice, Quot.sound]`. That covers the four theorems above and every
intermediate theorem (34 `ModelGlue.*` lines).

Glue Props of earlier steps, now proved outright with exactly their stated types:

| Prop (namespace `ModelGlue`) | Proof | Status |
|---|---|---|
| `ModelGenericFibre` | `modelGenericFibre` (the base change `𝒴 ×_{ℤ_(p)} Spec ℚ`) | proved |
| `GermOfQbarValues` | `germOfQbarValues` (Jacobson density on the generic fibre) | proved |
| `ModelIntegral` | `modelIntegral_of (hT : TwistClassFinite) (hC : CurveBijIso)` | from `CurveBijIso` + T5 |
| `ModelFunctionField` | `modelFunctionField_of_curveBijIso (hT : TwistClassFinite) (hC : CurveBijIso)` | from `CurveBijIso` + T5 |
| `SmoothFibreReduced` (vert-witness) | `smoothFibreReduced'` (copied from task smooth-fibre) | proved |

`TwistClassFinite` is `twistClassFinite hT`, proved from T5 in `Contrib/Mobius/Glue.lean`.

## 2. The remaining named statements

**`ModelGlue.CurveBijIso`** (textbook leaf; STANDARD; locators UNVERIFIED):

```lean
def CurveBijIso : Prop :=
  ∀ (S Y : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → ∀ g : S ⟶ Y,
    Function.Bijective (fun s : fieldPt Qbar ⟶ S => s ≫ g) → IsIso g
```

In words: a morphism of proper smooth curves over `ℚ` that is bijective on `ℚ̄`-points is an
isomorphism. The standard proof:

1. `g` is quasi-finite: a positive-dimensional fibre would have infinitely many `ℚ̄`-points.
2. `g` is proper, hence finite (EGA III 4.4.2; Mathlib has
   `IsFinite.of_isProper_of_locallyQuasiFinite`).
3. In characteristic 0, `g` is generically étale. So over each component of `Y_ℚ̄`, the number of
   `ℚ̄`-points in a general fibre equals the degree (Hartshorne II.6.9, III.10.7). Each degree is
   therefore 1.
4. So `g` is finite and birational onto the normal `Y`, hence an isomorphism.

Steps 1 and 2 are partly in Mathlib. Step 3 needs generic smoothness and degree counting, which
Mathlib 4.35 does not have.

**`ModelGlue.ModelCoordinateResidue`** (glue; `scratch/model-glue/ModelGlue.lean.part`). It is
`ModelCoordinate` with the Gauss criterion replaced by its source. There is `ρ : 𝒴 → P¹` over
`ℤ_(p)` with `CoordFibres`, defined at every point `ξ` whose stalk is a DVR with maximal ideal
`(p)`, such that the residue `ρ̄(ξ) ∈ κ(ξ)` is transcendental over the prime field. Its content
is the tame quotient `𝒴/Γ' ≅ P¹_{ℤ_(p)}` (vert-witness §4.3 (d)). That is:

- SGA 1 Exp. V for the quotient and its compatibility with base change, since `p ∤ |Γ'|`;
- the three CM sections stay pairwise disjoint mod `p`.

Neither quotient schemes nor `P¹_{ℤ_(p)}` exist in Mathlib 4.35, and no part of this was proved.

**T5** (`ObjBridge.TorsionStructure`, the existing leaf H-25 of frontier.md, Mumford §4, §6). It
is used only through `TwistClassFinite`: twist classes over `ℚ̄` are finite.

## 3. How the proof goes (all compiled)

**`ModelCoordinate` ⇐ `ModelCoordinateResidue`** (step 1). This is the Gauss criterion
`mem_maximalIdeal_iff_of_transcendental`. Take a local ring with `p ∈ 𝔪`, and suppose the residue
of `r` is transcendental over the prime field. Then for `f ∈ ℤ[X]`,
`f(r) ∈ 𝔪 ⟺ f ∈ pℤ[X]`.

**`ModelComparison` ⇐ `ModelIntegral` + `ModelFunctionField`** (step 1,
`modelComparison_of`). For integral `𝒴`, a surjection `κ : ℚ(𝒴) → E` restricts to an embedding of
every stalk with fraction field `E` (`stalk_embedding_of_functionField`).

**The comparison morphism** (step 4, `exists_genFib_to_Y`).

- Let `S := 𝒴_ℚ = genFib 𝒴`. The family `𝒜` pulls back to `S` (`famBC`, `isFibreOf_baseChange`).
- `R1univProps` then gives `g : S → Y` over `ℚ` with `Φ(s ≫ g) = [fibre of 𝒜 at s]`.
- `g` is bijective on `ℚ̄`-points by the leaf's clauses 4 and 5 and by `genFib_pt`/`genFib_pt_inj`.
- `CurveBijIso` makes `g` an isomorphism.

**`ModelIntegral`** (step 4).

- *`Y` is irreducible* (`irreducible_of_chart`). The closure of the chart `Spec B` is irreducible,
  since `B ⊆ E` is a domain. If it were not all of `Y`, its open complement would have infinitely
  many closed points. This uses Jacobson and the absence of isolated points, which comes from the
  proved `smoothCurveNoIsolatedPoint_of smoothStalkDimOne`. Each of these closed points is the
  point of a `ℚ̄`-point with `π = ∞`. But `π⁻¹(∞)` is one twist class, which is finite.
- *`S` is irreducible*, because `S ≅ Y`.
- *`𝒴` is reduced* (`isReduced_of_smooth_zloc`): a smooth algebra over a domain is reduced. The
  proof is smooth-fibre's, with a domain in place of a field.
- *`𝒴` is irreducible* (`irreducibleSpace_of_genFib`). The image of `S` contains `D(p)`. `D(p)` is
  dense: on an open set missing `D(p)`, `p` would vanish because `𝒴` is reduced, yet `p` is a
  non-zero-divisor in every stalk by flatness (`natCast_mem_nonZeroDivisors_stalk`).

**`ModelFunctionField`** (step 5, `modelFunctionField_of_curveBijIso`).

- `ℚ = ℤ_(p)[1/p]` (`zloc_away`), so `j : S → 𝒴` is an open immersion.
- So `κ = e_B ∘ θ ∘ ψ⁻¹ ∘ φ` is bijective, where:
  - `φ : ℚ(𝒴) ≅ ℚ(S)` comes from `j`;
  - `ψ : ℚ(Y) ≅ ℚ(S)` comes from `g`;
  - `θ : ℚ(Y) ≅ ℚ(Spec B)` comes from the chart;
  - `e_B : ℚ(Spec B) ≅ E` holds because both are fraction fields of `B` (`ffMap`,
    `ffMap_bijective`).
- The germ of `ρ` goes to the germ of `σ = ρ ∘ j`.
- `σ` and `τ = π ∘ g` have the same fibre relation on `ℚ̄`-points (`CoordFibres`, `R2fpProps`).
  They also take the values `0, ∞, −16/27` at the CM points, and have finite fibres. So they agree
  (`val_eq_of_same_fibres`, the Möbius argument from the proved `curveFacts`).
- Hence they have the same germ (`germ_eq_of_val_eq`, Jacobson). So `ψ⁻¹(φ(ρ)) = π`.
- On the chart, the germ of `π ∘ h` is `X` (`germ_chart_eq`, Jacobson on `Spec B` with the chart's
  value clause), and `e_B(X) = X`.

**`ModelGenericFibre`, `GermOfQbarValues`** (step 3). `Hom(ℤ_(p), T)` is a singleton
(`zloc_ringHom_ext`), so `ℚ̄`-points lift uniquely to the base change. A prime of `ℤ_(p)` that
does not contain `p` is `0` (`zloc_prime_eq_bot`). So the generic point of an integral flat `𝒴`
lies over `Spec ℚ`.

## 4. Files and checks

`scratch/model-glue/`:

- `assemble.sh` builds `ModelGlue.lean`, `ModelGlue2.lean`, …, `ModelGlue6.lean`.
- `ModelGlue6.lean` is the final single-file check. It is
  `import ZInQKernel.Contrib.Mobius.Main` + `scratch/vert-witness/VertWitness.lean` (whole file,
  verbatim) + `ModelGlue.lean.part` … `ModelGlue6.lean.part`.
- `py/verbatim_check.py` checks the assembly mechanically: the prefix is verbatim, the two target
  `def`s occur exactly once and only in the prefix, and the copied smooth-fibre proofs equal their
  source. Output (VERIFIED): `ALL OK`.

On this host, `lake build ZInQKernel.Contrib.Mobius.Main` must run first (about 2 min). After
that, the check takes about 25 s.

Code copied from other tasks:

- `exists_qbarPt` and `eval_res` from period-glue (`scratch/period-glue/PiTwist.lean`);
- `isReduced_of_etale_of_isDomain'` and the proof of `smoothFibreReduced'` from smooth-fibre
  (`ZInQKernel/Contrib/SmoothFibre/Basic.lean`).

No Tau Ceti code was vendored, and no existing file was edited.

## 5. Findings (Lean pitfalls, VERIFIED by compilation)

- `set B := integralClosure ℚ[X] E` re-created the chart morphism `h` and lost its
  `IsOpenImmersion` instance. Write the term out instead.
- The Mathlib instance `Algebra R (Spec R).functionField` is not found for
  `R = CommRingCat.of B`, because the CommRing instance comes through `forget`. Use
  `@instAlgebraCarrierFunctionFieldSpec (CommRingCat.of B) _`, and pass from `CommRingCat.of B` to
  `B` with `IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl _)`.
- `germ ⊤ η (ΓSpecIso.inv b) = algebraMap (CommRingCat.of B) ℚ(Spec B) b` holds by `rfl`.
- The `IsOpenImmersion (pullback.fst _ g)` instance is stated for a specific `HasPullback`
  instance. Use `MorphismProperty.pullback_fst (P := @IsOpenImmersion)`.
- A field point of a fibre factor, `(Additive.toMul (P.e.eta a)).left`, has domain
  `(ptObj K).left`, not `Spec K`. Use `dsimp only [famBC, PkgI3.AbVar.ptObj, Over.mk_left]`
  before rewriting, and close `(ptObj K).hom ≫ y = y` through
  `Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id`.
- `irreducibleSpace_def` produces `IsIrreducible ⊤`. Restate it with
  `show IsIrreducible (Set.univ : Set _)`.

## 6. Statement changes

None proposed. Both targets are used with their owner's exact text.
