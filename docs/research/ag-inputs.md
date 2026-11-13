# ag-inputs: review of pi0-x6's `π₀(X₆) = 1` argument, and `AGInputs` from standard leaves

Task ag-inputs, 2026-11-13. Base `wip/integrate-w35c` (883c4ddf). Lean files in
`scratch/ag-inputs/`; results log `scratch/ag-inputs/log.md`. No file under `ZInQKernel/`,
`blueprint/`, or another task's notes or scratch directory was edited.

Marks: **VERIFIED** means compiled, computed, or read in a source. **STANDARD** means a published
theorem with a reference. **SPECULATIVE** means an assessment. Theorem numbers given from memory
are UNVERIFIED (no network).

## Verdict

1. **pi0-x6's Galois-component argument is correct** (VERIFIED as an argument, §1; its deduction
   is compiled). The adversarial review found no gap in the deduction itself. Two caveats:
   - **(c) is a real extra input.** The exact-CM clause `R2X6CMExact` (`π₆ = 0 ⇒ com ≅ ℤ[i]`,
     `π₆ = ∞ ⇒ com ≅ ℤ[ζ₃]`) is not a clause of the bundle. It is a consequence of Baba–Granath,
     read in its printed meaning, as pi0-x6 says. It also follows from the bundle's
     `R2X6PropsIff` together with the QM dichotomy and the maximality of `ℤ[i]` and `ℤ[ζ₃]`
     (§1.3). Neither derivation is in Lean.
   - **`AGInputs` was not pure algebraic geometry.** Its fields `over0` and `overInf` need the
     fibres of `π₆` to be finite. That is a fact about the quaternion order: `Aut(𝒪)` is finite
     modulo inner automorphisms by units. pi0-x6 filed it under "standard algebraic geometry";
     here it is the glue `AutModInnFinite` (proved from SN and AL).
2. **All three fields of `AGInputs` are proved in Lean from standard leaves** (VERIFIED: compiled,
   standard axioms only; `scratch/ag-inputs/AGInputs.lean`):

   `agInputs_of_leaves : ConnectedGeomConnected → CurveComponentDichotomy → AutModInnFinite →
   IsProper X.hom → SmoothOfRelativeDimension 1 X.hom → R2X6Props X Ψ π₆ → AGInputs π₆`

   `AutModInnFinite` is itself proved from Skolem–Noether and the finiteness of the
   Atkin–Lehner group (`autModInnFinite_of`). Skolem–Noether is proved by t-skolem-kw and has the
   same statement as `GlueDescent.LeafSkolemNoether`. The final forms are:

   `AGInO.r1pi0Props_of_leaves' : X6Props → R2X6Props → R5ptProps → R5fpCount → R2X6CMExact →
   ConnectedGeomConnected → CurveComponentDichotomy → LeafSkolemNoether → AtkinLehnerFinite →
   GeometricallyConnected X.hom`

   `AGInLA.r1R2fpRep_of_noPi0 : R1R2fpRepNoPi0 → R5fpCount → ConnectedGeomConnected →
   CurveComponentDichotomy → LeafSkolemNoether → AtkinLehnerFinite → R1R2fpRep`

   `R1R2fpRep` is a verbatim copy of the repaired bundle `LeafAdopt.R1R2fpRep`.
   `R1R2fpRepNoPi0` is the same bundle with its clause `R1pi0Props X` replaced by (c). So the
   bundle clause `R1pi0Props` is glue from:
   - the rest of the bundle;
   - the leaf `R5fpCount`;
   - the clause (c);
   - four standard results, none from the Shimura-curve literature, listed below.

   | Leaf | Lean | Content | Source | Status |
   | --- | --- | --- | --- | --- |
   | AG-GC | `AGIn.ConnectedGeomConnected` | `k` algebraically closed, `Y → Spec k` proper, `Y` connected ⇒ geometrically connected | EGA IV₂ (4.5.1), (4.5.8); Stacks, Varieties, §"Geometrically connected schemes" (UNVERIFIED numbers) | STANDARD; a consequence of the published statement, which needs neither "proper" nor more than separable closedness |
   | AG-CD | `AGIn.CurveComponentDichotomy` (proved from AG-CD1 `ComponentInfinite` and AG-CD2 `ConstOrSurj`, `curveComponentDichotomy_of`) | `X` proper smooth of relative dimension 1 over `ℚ`, `π : X → P¹`: on each connected component of `X_ℚ̄`, `π` hits every value of `P¹(ℚ̄)` at a `ℚ̄`-point, or some value is hit at infinitely many | Hartshorne II.6.8 (constant or surjective); normal Noetherian ⇒ components irreducible (Stacks); Nullstellensatz (UNVERIFIED numbers) | STANDARD (consequence of the listed theorems) |
   | SN | `GlueDescent.LeafSkolemNoether` | automorphisms of a finite-dimensional central simple algebra are inner | Skolem–Noether | **proved** (t-skolem-kw, `TSkolemKW.leafSkolemNoether`; identical statement, VERIFIED by reading both) |
   | AL | `AGInO.AtkinLehnerFinite` | `N_{B^×}(𝒪)/ℚ^×𝒪^×` finite: finite `T ⊆ B^×` with every normalizing `b = r·t·u` | Vignéras LNM 800 Ch. II–III; Voight GTM 288 Ch. 18, §28.9 (UNVERIFIED locators): an elementary abelian 2-group of rank `≤ #{p ∣ D}` | STANDARD (consequence) |

   Proved glue:
   - `descend` from AG-GC;
   - `over0` and `overInf` from AG-CD and finite fibres;
   - finite fibres from R2's fibre clause and `AutModInnFinite`, including the isomorphism of
     inner twists (`qmIsoOfConj`);
   - `AutModInnFinite` from SN and AL, including the extension of a ring automorphism of `𝒪` to
     a `ℚ`-algebra automorphism of `B` (`extAut`) and conjugation by normalizing units
     (`conjAut`).

3. **Mathlib v4.35 cannot prove AG-GC, AG-CD or AL** (SPECULATIVE assessment, from reading
   `Mathlib/AlgebraicGeometry/Geometrically/*`). It has `GeometricallyConnected`, base change of
   properness and surjectivity, and pullback pasting; all three are used in `descend_of_leaf`.
   What it lacks:
   - for AG-GC, connectedness under extension of an algebraically closed base field;
   - for AG-CD, dimension theory of curves and "normal ⇒ connected components irreducible" for
     schemes;
   - for AL, the normalizer of a quaternion order (two-sided ideals of a maximal order).
4. **Recommendation.** The clause `R1pi0Props` can leave the R1 bundle. It would be replaced by:
   - the three textbook leaves AG-GC, AG-CD and AL (SN is proved), which are crowdsourcable and
     independent of the Shimura-curve literature;
   - the clause (c), a restatement of Baba–Granath's CM clause.

   That removes the dependence on Deligne 1971 §2, whose locator is UNVERIFIED. If the owner
   prefers fewer hypotheses, keep `R1pi0Props` as a clause of R1, with this file as the record
   that it is glue modulo textbook facts. The choice is the owner's.

## 1. Adversarial review of the Galois-component argument

The argument (pi0-x6 §2) has five steps:
1. Every component of `X̄ = X₆ ×_ℚ ℚ̄` contains a `ℚ̄`-point over `0` and one over `∞`.
2. There are at most two points over `0`. Their residue fields are `ℚ(i)`, and those of the
   points over `∞` are `ℚ(√−3)`.
3. Choose `σ ∈ Aut(ℚ̄/ℚ)` that fixes `√−3` and moves `i`. Then `σ` fixes a point `y` over `∞` in
   the component of `x₁`, and sends `x₁` to the other point `x₂` over `0`.
4. Components are Galois-compatible.
5. So the two components coincide.

Checked:

### 1.1 The deduction (VERIFIED, compiled)

`subsingleton_of_galois` is pi0-x6's Lean proof, recompiled here unchanged. It uses `hcount` on
`x₁, x₂, σx₁`, and each case closes:
- `x₁ = x₂`: the components are equal;
- `σx₁ = x₁`: contradicts `σ(i) ≠ i` through `galPt_eq_self_iff` (the stabilizer of a `ℚ̄`-point
  is the fixing group of its residue field, proved);
- `x₂ = σx₁`: Galois compatibility of components (`compOf_galois`, proved), applied to `y` and
  `x₁`, gives `comp(x₂) = comp(σy) = comp(y) = comp(x₁)`.

That `σx₁` lies over `0` uses only `π(σx) = σ(π x)` (`ToP1.val_comp`, proved).

### 1.2 The residue fields (VERIFIED as an argument; the leaf R5pt as stated in the bundle)

From `R5ptProps` with `b = 1` and `h = 1`, the residue field has degree 2 and contains `k`
(`residue_eq_adjoin_of_R5pt`, proved). The closed facts `inertCount6 = 1`, `#Pic = 1` and
conductor 1 are proved for both fields.

Independent sanity check (SPECULATIVE; references UNVERIFIED):
- Shimura reciprocity gives `k·ℚ(P) = H_R`, the ring class field, which is `k` here since
  `h = 1`. So `ℚ(P) ⊆ k`.
- `X^D(ℝ) = ∅` for `D > 1` (Shimura 1975) gives `ℚ(P) ≠ ℚ`.
- Hence `ℚ(P) = ℚ(i)` over `0` and `ℚ(P) = ℚ(√−3)` over `∞`, independently of the exact form of
  González–Rotger Thm 5.12.

The conic model `x² + y² + 3z² = 0` with `W` acting by sign changes (from memory) agrees with
this:
- the fixed points of `z ↦ −z` are `(±i : 1 : 0)`, with field `ℚ(i)`;
- the fixed points of the two other involutions are `(0 : ±√−3 : 1)` and `(±√−3 : 0 : 1)`, both
  with field `ℚ(√−3)`, matching `CM(−3)` and `CM(−24)`. For the latter, `b = 0` and `h = 2`, and
  the degree-2 field is not real.

The argument would fail if the points over `0` and over `∞` had the same residue field. They do
not.

### 1.3 Input (c), `R2X6CMExact` (not in the bundle)

The bundle's `R2X6PropsIff` gives `π₆ = 0 ↔ HasCM4` (some `φ ∈ com` with `φ² = −1`). `R5ptProps`
and `R5fpCount` are keyed on `com ≅ R`. So the core needs `com ≅ ℤ[i]` over `0`, and likewise
`com ≅ ℤ[ζ₃]` over `∞`.

Derivation (c2), not in Lean:
- by the QM dichotomy (`PkgI3.QMDichotomyYu`) and the double centralizer theorem, `com` is `ℤ`
  or an order in an imaginary quadratic field;
- `φ` gives `ℤ[i] ⊆ com`, so `com` is an order of `ℚ(i)` containing the maximal order `ℤ[i]`,
  hence equal to it.

Option (c1) adopts it as a restatement of Baba–Granath's clause ("CM point by `R`" means
`End_𝒪(A) ≅ R`, an optimal embedding). Either is acceptable. (c1) is what the Lean uses.

### 1.4 The geometric input (d)

The input "every component meets the fibres over `0` and `∞`" is true for the genuine `X₆`.
Each connected component of `X̄` is a proper smooth irreducible curve over `ℚ̄`, and `π₆`
restricted to it is either surjective or constant.

Constancy is excluded because the fibres of `π₆` on `ℚ̄`-points are finite. That finiteness is
not algebraic geometry:
- by R2's fibre clause, the fibre through `x` is `{[P.twist α]}`;
- that set is finite only because `Aut(𝒪)/Inn(𝒪^×)` is finite. This holds by Skolem–Noether
  together with the finiteness of `N(𝒪)/ℚ^×𝒪^×`.

pi0-x6 listed this inside (d) as standard algebraic geometry; it is a quaternion-order fact
(`AutModInnFinite`, proved here from SN and AL).

### 1.5 pi0-x6's finding F1 on the rv-blueprints sketch (VERIFIED as an argument)

pi0-x6's finding F1 is confirmed. With two degree-2 components, each one is ramified over `0`,
`∞` and `−16/27`, because each has one point in each of these fibres. Riemann–Hurwitz gives
`B = 2g + 2`. A fourth branch value, with `g = 1`, is not excluded by any clause of the bundle.

### 1.6 Non-vacuity

Each leaf in the table holds for every scheme it quantifies over (published theorems), so none
assumes the conclusion. AG-GC and AG-CD quantify over all proper (smooth) `ℚ`-schemes, not over
`X₆`. AL is a statement about the explicit order `LeafQM.O`; SN quantifies over all central
simple algebras.

The only `X₆`-specific inputs are the bundle clauses and (c).

## 2. Lean (`scratch/ag-inputs/AGInputs.lean`)

All of the following is VERIFIED:
- `lake env lean scratch/ag-inputs/AGInputs.lean` exits 0, with no errors and no warnings.
- 20 `#print axioms` lines all show `[propext, Classical.choice, Quot.sound]`
  (`compile_out.txt`).
- The file contains no `sorry` and no `axiom`.
- It imports `ZInQKernel.HDecomp.QM.Leaves` and `ZInQKernel.HDecomp.Descent.B1Quat` (built
  with `lake build`).

§1-§7 are pi0-x6's `Pi0X6.lean`, copied with the namespace renamed `AGIn`. §8-§11 are new:

| § | Declaration | Statement | Status |
| --- | --- | --- | --- |
| 8 | `AGIn.ConnectedGeomConnected` | leaf AG-GC (above) | leaf (def) |
| 8 | `AGIn.spec_rat_ext` | any two `Spec L → Spec ℚ` agree | proved |
| 8 | `AGIn.descend_of_leaf` | AG-GC, `IsProper X.hom`, `X_ℚ̄` connected ⇒ `GeometricallyConnected X.hom` | proved |
| 9 | `AGIn.CurveComponentDichotomy` | leaf AG-CD (above), over `Xbar`, `compOf`, `ToP1.val` | leaf (def) |
| 9 | `AGIn.ComponentInfinite`, `AGIn.ConstOrSurj` | AG-CD1: each component of `X_ℚ̄` has infinitely many `ℚ̄`-points; AG-CD2: `π` on a component is constant or surjective (Hartshorne II.6.8) | leaves (def) |
| 9 | `AGIn.curveComponentDichotomy_of` | AG-CD1 + AG-CD2 ⇒ AG-CD | proved |
| 9 | `AGIn.meets_fibre_of_finite` | AG-CD + finite fibres ⇒ every component of `X_ℚ̄` meets every fibre | proved |
| 9 | `AGIn.qmIsoOfConj` | `q₁(a) = q₂(u a u⁻¹)` ⇒ `q₂(u⁻¹) : (A, q₁) ≅ (A, q₂)` | proved |
| 9 | `AGIn.AutModInnFinite` | finite `S ⊆ Aut(𝒪)`, every `α = s ∘ Ad(u)` | def (glue target, proved in §10) |
| 9 | `AGIn.twistClasses_finite` | `AutModInnFinite` ⇒ `{[P.twist α]}` finite | proved |
| 9 | `AGIn.fibres_finite` | `R2X6Props` + `AutModInnFinite` ⇒ every `π₆`-fibre on `ℚ̄`-points finite | proved |
| 9 | `AGIn.agInputs_of_leaves` | AG-GC, AG-CD, `AutModInnFinite`, proper, smooth, `R2X6Props` ⇒ `AGInputs π₆` | proved |
| 9 | `AGIn.r1pi0Props_of_leaves` | bundle clauses + `R5fpCount` + (c) + the above ⇒ `GeometricallyConnected X.hom` | proved |
| 10 | `AGInO.exists_nat_smul_mem`, `nOf` | every `b ∈ B` has `n > 0` with `n·b ∈ 𝒪` | proved |
| 10 | `AGInO.extAut`, `extAut_coe` | `α ∈ Aut(𝒪)` extends to `B ≃ₐ[ℚ] B` agreeing with `α` on `𝒪` | proved |
| 10 | `AGInO.AtkinLehnerFinite` | leaf AL (above) | leaf (def) |
| 10 | `AGInO.conjAut`, `autSet` | conjugation by a normalizing unit as an element of `Aut(𝒪)` | defs |
| 10 | `AGInO.autModInnFinite_of` | SN + AL ⇒ `AutModInnFinite` | proved |
| 10 | `AGInO.r1pi0Props_of_leaves'` | as `r1pi0Props_of_leaves`, with SN + AL for `AutModInnFinite` | proved |
| 11 | `AGInLA.R1pi0Props`, `R2X6PropsIff`, `R1R2fpRep` | verbatim copies from `scratch/h-decomposition/Leaves.lean` (checked by script) | defs |
| 11 | `AGInLA.R1R2fpRepNoPi0` | `R1R2fpRep` with `R1pi0Props X` replaced by (c) | def |
| 11 | `AGInLA.r1R2fpRep_of_noPi0` | `R1R2fpRepNoPi0` + `R5fpCount` + AG-GC + AG-CD + SN + AL ⇒ `R1R2fpRep` | proved |

`scratch/ag-inputs/T1.lean` (`descend` over Mathlib alone) and `T2.lean` (§10 alone) are the
development files; both compile (VERIFIED).

Proof of `autModInnFinite_of`:
1. Extend `α` to `φ = extAut α ∈ Aut_ℚ(B)`.
2. SN at `B` (`GlueDescent.B6_inner`; `B` central simple by `B6_isCentral` and
   `B6_isSimpleRing`) gives `φ = Ad(b)`.
3. `b` normalizes `𝒪`, using `α` and `α⁻¹`.
4. AL gives `b = r·t·u`. Then `t` normalizes `𝒪`, and `α(a) = t(u a u⁻¹)t⁻¹ = (conjAut t)(u a u⁻¹)`.

Proof of `descend_of_leaf`:
1. Take a field `K` with `y : Spec K → Spec ℚ`, and let `L = K̄`. `K` has characteristic 0
   because of `y`.
2. Choose `ℚ̄ →ₐ[ℚ] L` (`IsAlgClosed.lift`).
3. `X_K ×_K L` is a pullback of `X_ℚ̄ → Spec ℚ̄` along `Spec L → Spec ℚ̄`. This is
   `IsPullback.paste_horiz` and `IsPullback.of_right`, using that morphisms to `Spec ℚ` are
   unique. So it is connected by AG-GC applied to `X_ℚ̄ → Spec ℚ̄`, which is proper as a base
   change.
4. `X_K ×_K L → X_K` is surjective, as a base change of `Spec L → Spec K`. So `X_K` is
   connected.

`scratch/ag-inputs/T1.lean` is the same proof over Mathlib alone (VERIFIED, compiled).

## 3. What remains

1. The three leaves AG-GC, AG-CD and AL. Each is textbook, and none is in Mathlib v4.35. Any of
   them could be formalized independently of this project.
2. Input (c): adopt `R2X6CMExact` (c1), or derive it from `QMDichotomyYu` (c2). (c2) needs, in
   Lean:
   - the centralizer of `B` in `M₂(F)` (via the simplicity of `F ⊗ B`, available in
     t-skolem-kw);
   - `HomFreeFinite`, to make `com` an order;
   - the maximality of `ℤ[i]` and `ℤ[ζ₃]`, proved in §5-§6.

   Not done.
3. Locators: all theorem numbers above are from memory (UNVERIFIED). A human check of EGA IV₂
   §4.5, Hartshorne II.6.8, and the Atkin–Lehner group in Vignéras or Voight is needed before
   announcing.
4. Integration: `AGInLA.r1R2fpRep_of_noPi0` is the drop-in form. If adopted, it goes into
   `ZInQKernel/HDecomp/` next to the bundle, with `R1R2fpRepNoPi0` replacing `R1R2fpRep` in
   `ResearchLeaves`, and AG-GC, AG-CD and AL added as named leaves.
