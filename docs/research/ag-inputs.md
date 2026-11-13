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
     here it is a separate leaf, `AutModInnFinite`.
2. **All three fields of `AGInputs` are proved in Lean from three standard leaves**
   (VERIFIED: compiled, standard axioms only; `scratch/ag-inputs/AGInputs.lean`):

   `agInputs_of_leaves : ConnectedGeomConnected → CurveComponentDichotomy → AutModInnFinite →
   IsProper X.hom → SmoothOfRelativeDimension 1 X.hom → R2X6Props X Ψ π₆ → AGInputs π₆`

   `r1pi0Props_of_leaves : X6Props Y Φ X Ψ fY → R2X6Props X Ψ π₆ → R5ptProps X Ψ → R5fpCount →
   R2X6CMExact Ψ π₆ → ConnectedGeomConnected → CurveComponentDichotomy → AutModInnFinite →
   GeometricallyConnected X.hom`

   The conclusion is exactly the bundle clause `LeafAdopt.R1pi0Props X`. The hypotheses are:
   - bundle clauses (`X6Props`, `R5ptProps`, and `R2X6Props`, which `R2X6PropsIff` implies);
   - the leaf `R5fpCount`;
   - (c), `R2X6CMExact`;
   - three standard leaves, none from the Shimura-curve literature:

   | Leaf | Lean | Content | Source | Status |
   | --- | --- | --- | --- | --- |
   | AG-GC | `ConnectedGeomConnected` | `k` algebraically closed, `Y → Spec k` proper, `Y` connected ⇒ geometrically connected | EGA IV₂ (4.5.1), (4.5.8); Stacks, Varieties, §"Geometrically connected schemes" (UNVERIFIED numbers) | STANDARD; the published statement drops "proper" and only needs `k` separably closed, so this is a consequence |
   | AG-CD | `CurveComponentDichotomy` | `X` proper smooth of relative dimension 1 over `ℚ`, `π : X → P¹`: on each connected component of `X_ℚ̄`, `π` hits every value of `P¹(ℚ̄)` at a `ℚ̄`-point, or some value is hit at infinitely many | Hartshorne II.6.8 (constant or surjective); normal Noetherian ⇒ components irreducible (Stacks); Nullstellensatz (UNVERIFIED numbers) | STANDARD (consequence of the listed theorems) |
   | AutO | `AutModInnFinite` | finite `S ⊆ Aut(𝒪)` with every `α = s ∘ Ad(u)`, `s ∈ S`, `u ∈ 𝒪^×` | Skolem–Noether (T13, **proved** by t-skolem-kw) and the finiteness of the Atkin–Lehner group `N(𝒪)/ℚ^×𝒪^× ≅ (ℤ/2)²` (Vignéras LNM 800; Voight GTM 288; UNVERIFIED locators) | STANDARD (consequence of the two) |

   What is now proved glue:
   - `descend` from AG-GC;
   - `over0` and `overInf` from AG-CD and finite fibres;
   - finite fibres from R2's fibre clause and AutO, including the isomorphism of inner twists
     (`qmIsoOfConj`).
3. **Mathlib v4.35 cannot prove the three leaves** (SPECULATIVE assessment, from reading
   `Mathlib/AlgebraicGeometry/Geometrically/*`). It has `GeometricallyConnected`, base change of
   properness and surjectivity, and pullback pasting; all three are used in `descend_of_leaf`.
   What it lacks:
   - for AG-GC, connectedness under extension of an algebraically closed base field;
   - for AG-CD, dimension theory of curves and "normal ⇒ connected components irreducible" for
     schemes;
   - for AutO, the normalizer of a quaternion order.
4. **Recommendation.** The clause `R1pi0Props` can leave the R1 bundle. It would be replaced by:
   - the three textbook leaves above, which are crowdsourcable and independent of the
     Shimura-curve literature;
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
(leaf AutO).

### 1.5 pi0-x6's finding F1 on the rv-blueprints sketch (VERIFIED as an argument)

pi0-x6's finding F1 is confirmed. With two degree-2 components, each one is ramified over `0`,
`∞` and `−16/27`, because each has one point in each of these fibres. Riemann–Hurwitz gives
`B = 2g + 2`. A fourth branch value, with `g = 1`, is not excluded by any clause of the bundle.

### 1.6 Non-vacuity

Each leaf in the table holds for every scheme it quantifies over (published theorems), so none
assumes the conclusion. AG-GC and AG-CD quantify over all proper (smooth) `ℚ`-schemes, not over
`X₆`. AutO is a statement about the explicit order `LeafQM.O`.

The only `X₆`-specific inputs are the bundle clauses and (c).

## 2. Lean (`scratch/ag-inputs/AGInputs.lean`)

All of the following is VERIFIED:
- `lake env lean scratch/ag-inputs/AGInputs.lean` exits 0, with no errors and no warnings;
- 15 `#print axioms` lines all show `[propext, Classical.choice, Quot.sound]`
  (`compile_out.txt`);
- the file contains no `sorry` and no `axiom`;
- it imports `ZInQKernel.HDecomp.QM.Leaves` (built with
  `lake build ZInQKernel.HDecomp.QM.Leaves`).

§1-§7 are pi0-x6's `Pi0X6.lean`, copied with the namespace renamed `AGIn`. §8-§9 are new:

| Declaration | Statement | Status |
| --- | --- | --- |
| `ConnectedGeomConnected` | leaf AG-GC (above) | leaf (def) |
| `spec_rat_ext` | any two `Spec L → Spec ℚ` agree | proved |
| `descend_of_leaf` | AG-GC, `IsProper X.hom`, `X_ℚ̄` connected ⇒ `GeometricallyConnected X.hom` | proved |
| `CurveComponentDichotomy` | leaf AG-CD (above), over `Xbar`, `compOf`, `ToP1.val` | leaf (def) |
| `meets_fibre_of_finite` | AG-CD + finite fibres ⇒ every component of `X_ℚ̄` meets every fibre | proved |
| `qmIsoOfConj` | `q₁(a) = q₂(u a u⁻¹)` ⇒ `q₂(u⁻¹) : (A, q₁) ≅ (A, q₂)` | proved |
| `AutModInnFinite` | leaf AutO (above) | leaf (def) |
| `twistClasses_finite` | AutO ⇒ `{[P.twist α]}` finite | proved |
| `fibres_finite` | `R2X6Props` + AutO ⇒ every `π₆`-fibre on `ℚ̄`-points finite | proved |
| `agInputs_of_leaves` | the three leaves + proper + smooth + `R2X6Props` ⇒ `AGInputs π₆` | proved |
| `r1pi0Props_of_leaves` | bundle clauses + `R5fpCount` + (c) + three leaves ⇒ `GeometricallyConnected X.hom` | proved |

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

1. The three leaves AG-GC, AG-CD and AutO. Each is textbook, and none is in Mathlib v4.35. Any
   of them could be formalized independently of this project.
   - AutO splits further into Skolem–Noether, which is proved (t-skolem-kw; needs `B` central
     simple over `ℚ` as instances), and the finiteness of `N(𝒪)/ℚ^×𝒪^×`. The split is not done
     in Lean.
2. Input (c): adopt `R2X6CMExact` (c1), or derive it from `QMDichotomyYu` (c2, needs the double
   centralizer theorem).
3. Locators: all theorem numbers above are from memory (UNVERIFIED). A human check of EGA IV₂
   §4.5 and of Hartshorne II.6.8 is needed before announcing.
