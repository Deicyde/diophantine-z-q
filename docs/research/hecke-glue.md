# hecke-glue: two of the three open inputs of the Hecke dictionary are proved

Task hecke-glue, 2026-11-17. Lean: `ZInQKernel/Contrib/OneProof/HeckeGlue.lean` (namespace
`AfTateLam.HeckeGlue`). Scratch: `scratch/hecke-glue/` (log, verbatim target copy, `#discharges`
output, autofold spec).

## 1. Verdict

hecke-pin (`ZInQKernel/Contrib/OneProof/HeckePin.lean`) reduced the dictionary gap of the r16 rows
`HeckeJ1DS`, `AfShimura` and `AfCharpolyDS965` to three named Props. Their status now:

| Prop (hecke-pin) | hecke-pin's rating | now |
|---|---|---|
| `ConstOnTauPoints` | GLUE, open | **proved** (`constOnTauPoints`) |
| `X1TauPoints` | LEAF candidate, not printed form | **proved**: it is glue, not a leaf (`x1TauPoints`) |
| `AbelJacobiX1` | LEAF candidate, not printed form | open; still not printed form (§5) |

All of this is VERIFIED: it compiles with no `sorry`, and every theorem uses only `propext`,
`Classical.choice`, `Quot.sound` (`scratch/hecke-glue/Discharges-output.txt`).

**Per row:**
* `HeckeJ1DS`: the dictionary gap is **closed with no hypothesis**. `isHeckeT_unique'` and
  `isDiamond_unique'` show that `IsHeckeT` / `IsDiamond` determine `T_p` and `⟨d⟩`.
* `AfShimura`, `AfCharpolyDS965`: the gap is closed except for one input.
  * The pinning of `T_p`, `⟨d⟩`, `A_f` and `θ` needs no hypothesis (here and in hecke-pin).
  * `KillsIf` = DS's `I_f` needs only `AbelJacobiX1`
    (`killsIf_iff_IfDS_of_abelJacobi`, `evF_eq_zero_of_heckeJ_eq_zero_of_abelJacobi`).

**Against the target.** The target was the gap closed modulo printed-form leaves only. That is met for
`HeckeJ1DS`. It is not met for `AfShimura` and `AfCharpolyDS965`. There the one remaining input,
`AbelJacobiX1`, is a composite consequence of printed theorems (DS Thm 6.1.2 with DS §3.3 and the
algebraic Jacobian), and no printed form of it can be stated in Lean today (§5).

## 2. `X1TauPoints` is glue: the place at `τ` and its center

`X1TauPoints` says: for every model `X` of DS's `X₁(N)_alg` with generators `(j_X, t_X)` (`IsX1Gen`) and every
`τ ∈ ℍ`, some complex point `x` satisfies `AtTau` at `τ`. Proof in two steps, both compiled.

**Step 1, the place (`tauPlace : TauPlace`; GLUE, analytic).** Fix `τ ∈ ℍ`.
* Every `a ∈ K(X)` is `P(j_X, t_X)/Q(j_X, t_X)` with `Q(j_X, t_X) ≠ 0` (`exists_rep`, from `K(X) = ℚ(j_X, t_X)`).
* `a` has a meromorphic function near `τ`: `mf a = hol P / hol Q`. Here `hol F (z) = F(j(z), f₁(z))` on
  Weber's generic branch, which is holomorphic on `ℍ` (the tree's `WeberField.diffOn_ez`).
* The function does not depend on the representation, up to equality on a punctured neighbourhood
  (`rep_eventuallyEq`). By `IsX1Gen`, `F(j_X, t_X) = 0` iff `F(j, f₁)` vanishes at the good `τ`. That holds
  iff `hol F ≡ 0` on `ℍ`, by the identity theorem (`hol_eq_zero_of_ev2`, `ev2_eq_zero_of_hol`). Also the bad
  points `g₂g₃ = 0` and the zeros of `hol Q` are isolated (`eventually_ne_of_diffOn`).
* `O = {a : mf a has a finite limit at τ}` is a valuation subring of `K(X)` (`placeO`). If the order
  satisfies `meromorphicOrderAt ≥ 0`, there is a limit. If it is `< 0`, then `mf a → ∞` and `mf a⁻¹ → 0`
  (Mathlib `tendsto_nhds_of_meromorphicOrderAt_nonneg`, `tendsto_cobounded_of_meromorphicOrderAt_neg`).
* The limit `ev : O → ℂ` is a ring homomorphism (`placeEv`). It is local (`placeEv_local`): if
  `ev a ≠ 0` then `a⁻¹ ∈ O`.
* `tendsto_hol` moves `AtTau`'s limit over `ℍ` to the generic branch near `τ` in `ℂ`. On a punctured
  neighbourhood, `evAn = hol` (`WeberField.evAn_eq`).

**Step 2, the center (`exists_cpt_of_place`; GLUE, algebraic).** Let `O ⊂ K(X)` be a valuation subring with a
local `ev : O → ℂ`. Then some complex point `x` has every `a ∈ O` regular at `x` with value `ev a`.
* *Valuative criterion.* `X → Spec ℚ` is proper, so `Spec O → X` lifts `Spec K(X) → X` (Mathlib
  `UniversallyClosed.eq_valuativeCriterion`). For this, `ℚ ⊂ O` because `ev(n) = n ≠ 0` (`rat_mem`).
* *The center.* Let `p` be the center and `φ : 𝒪_{X,p} → O` the local map (`stalkClosedPointTo`). Then `φ` is
  compatible with `𝒪_{X,p} → K(X)`, since `fromSpecStalk p` is a monomorphism
  (`SpecMap_stalkSpecializes_fromSpecStalk`).
* *`O` equals the local ring.* `𝒪_{X,p}` is a valuation ring (CloudW07 `valuationRing_stalk`, smooth curve)
  and `O` dominates it, so every `a ∈ O` lies in `𝒪_{X,p}`.
* *The point.* `x = Spec(ev) ≫ (Spec O → X)` lies over `p` (`Spec_closedPoint`, since `ev` is local). Its
  values are `ev ∘ φ` (`germ_stalkClosedPointTo_Spec_fromSpecStalk`).

`x1TauPoints_of_tauPlace` combines the two steps.

**Consequence: `X1TauPoints` is not a leaf.** Its only inputs are the definition of `IsX1Gen` (the integer
relations of `(j_X, t_X)` are those of `(j, f₁)`), Mathlib and the tree's Weber analysis. hecke-pin read it as
the DS §7.7 identification `X₁(N) = X₁(N)_alg,ℂ`. That identification is not needed here, because `IsX1Gen`
already contains the dictionary at the level of function fields.

## 3. `ConstOnTauPoints`, over `ℚ`

`constOnTauPoints_of_x1TauPoints : X1TauPoints → ConstOnTauPoints` (compiled). Then `constOnTauPoints` uses
`x1TauPoints`.

**`ConstOnTauPoints` is not provable without the points.** With no `x_τ` its constancy hypothesis is vacuous.
So the proof consumes `X1TauPoints`, which is now proved.

The proof runs over `ℚ`. It does not need hecke-pin's route through `X_ℂ`, which needed geometric
irreducibility, a gap in the tree. Steps (`g : X → J` with `g(P₀) = 0`, constant on the `x_τ`):
1. **`x_ρ` lies over a closed point.**
   * `j_X` is regular at `x_ρ` with value `j(ρ) = 0` (`regAt_jX`, `jfun_ρ`), and `j_X ≠ 0` (`jX_ne_zero`, from
     `IsX1Gen` and a good point with `g₂g₃ ≠ 0`).
   * At the generic point a nonzero function has a nonzero value (`regAt_ne_zero_of_generic`), so `x_ρ` does
     not lie over the generic point.
   * The curve has dimension ≤ 1 (CloudW07 `topologicalKrullDim_le_of_smoothOfRelativeDimension`), so a
     non-generic point is closed (CloudW07 `eq_genericPoint_of_not_isClosed`).
2. **`q = g(p_ρ)` is a closed point of `J`** (Mathlib `closedPoints_subset_preimage_closedPoints`, Jacobson).
   Every `x_τ` maps to `q`.
3. **The generic point maps to `q`.** Otherwise `F = g⁻¹(q)` is a closed set without the generic point. Then:
   * `F` is finite (CloudW07 `IsOpen.finite_compl_of_topologicalKrullDim_le_one`).
   * Finitely many complex points lie over finitely many closed points (`finite_cpts`: `κ(p)` is finite over
     `ℚ`, by Zariski's lemma, with `AlgHom.fintype` and `SpecToEquivOfField`).
   * The value of a function at a point is unique (`regAt_unique`).
   * So `j(τ)` takes finitely many values on `ℍ`. But `j` is continuous with `j(i) = 1728 ≠ 0 = j(ρ)`
     (`HeckePin.const_of_countable`). Contradiction.
4. **`q = g(P₀) = 0`.** The generic point specializes to `P₀`, and `q` is closed.
5. **`g = 1`.**
   * `κ(0)` maps to `ℚ`, so any two homomorphisms out of it agree (`ringHom_ext_of_toRat`).
   * So `g` and `1` agree on `Spec κ(η)` (`SpecToEquivOfField_eq_iff`).
   * Mathlib `ext_of_fromSpecResidueField_eq` (`X` reduced, `J` separated, `{η}` dense) gives `g = 1`.

## 4. Wiring into HeckePin

| HeckePin theorem | hypotheses there | wrapper here | hypotheses now |
|---|---|---|---|
| `isHeckeT_unique` | `X1TauPoints`, `ConstOnTauPoints` | `isHeckeT_unique'` | none |
| `isDiamond_unique` | `X1TauPoints`, `ConstOnTauPoints` | `isDiamond_unique'` | none |
| `evF_eq_zero_of_heckeJ_eq_zero_of_leaves` | `X1TauPoints`, `AbelJacobiX1` | `evF_eq_zero_of_heckeJ_eq_zero_of_abelJacobi` | `AbelJacobiX1` |
| `killsIf_iff_IfDS_of_leaves` | `X1TauPoints`, `AbelJacobiX1` | `killsIf_iff_IfDS_of_abelJacobi` | `AbelJacobiX1` |

HeckePin.lean is not edited: the wrappers are new theorems in HeckeGlue.lean.

**`#discharges`** (VERIFIED, `scratch/hecke-glue/Discharges-output.txt`): `r16CoreY` is still discharged by
`AfTateLam.r16CoreY_of_ds965`, assuming the same five leaves. The new theorems discharge no open field, as
expected. They are audit theorems about the dictionary hypotheses of those leaves, not new routes.

**Verbatim copy** (VERIFIED, `scratch/hecke-glue/Target.lean`):
* the three Props are copied from HeckePin.lean;
* `copies_eq` checks that the copies are the originals (`Iff.rfl`);
* `x1TauPoints_copy` and `constOnTauPoints_copy` prove the copies.

## 5. `AbelJacobiX1`: the printed statements and the bridge

`AbelJacobiX1`: for `f ∈ S₂(Γ₁(N))` with a primitive `F` on `ℍ`, some countable `Λ ⊂ ℂ` has the following
property. Every degree-0 divisor `Σ n_τ [x_τ]` whose class `Σ n_τ aj(x_τ)` in `J(ℂ)` is trivial has
`Σ n_τ F(τ) ∈ Λ`.

**The printed statements it composes:**
* (P1) **Diamond–Shurman Thm 6.1.2 (Abel's theorem)**, 2005 printing pp. 214–215 (VERIFIED by pdftotext of the
  local copy). For a compact Riemann surface `X`, the map `Div⁰(X) → Jac(X) = Ω¹_hol(X)^∧/H₁(X, ℤ)` given by
  `Σ n_x x ↦ Σ n_x ∫_{x₀}^{x}` descends to an isomorphism `Pic⁰(X) ≅ Jac(X)`. Only "descends" is used:
  principal divisors integrate to periods.
* (P2) **DS §3.3**: a weight-2 cusp form `f` for `Γ` gives the holomorphic differential `f(τ)dτ` on `X(Γ)`
  (number UNVERIFIED; STANDARD).
* (P3) **Algebraic Jacobian** (Weil; Milne, *Jacobian varieties*, 1986, Thm 1.1 and Prop. 6.1, numbers
  UNVERIFIED). For the Albanese `(J, aj)` of a pointed smooth projective curve over `k` and `K ⊇ k`
  algebraically closed, a degree-0 divisor on `X_K` has `Σ n aj(P) = 0` iff it is principal.
* (P4) **GAGA for curves** (DS §7.2 for `X₁(N)`): rational functions on `X_ℂ` are the meromorphic functions on
  the compact Riemann surface.

**The bridge (P1–P4 ⟹ `AbelJacobiX1`), step by step. None of it is proved in Lean.**
1. Class trivial in `J(ℂ)` ⟹ `Σ n_τ [x_τ]` is principal on `X_ℂ`. This is (P3) at `K = ℂ`, applied to the
   `ℂ`-points `x_τ`. It needs `X_ℂ` integral (geometric irreducibility, missing in the tree) and the
   comparison of the Albanese `J` of `IsJacobian` with Milne's `J` (uniqueness of Albanese, a short glue).
2. The rational function `g ∈ ℂ(X)` becomes a `Γ₁(N)`-invariant meromorphic function `G(τ) = g(j(τ), f₁(τ))`
   on `ℍ`, and `ord_{x_τ} g = ord_τ G / e_τ`, where `e_τ` is the ramification at elliptic points. This is
   glue: the analytic place of §2 identifies `𝒪_{X,x_τ}` with the functions finite at `τ`, so the
   valuations agree up to `e_τ`.
3. The compact Riemann surface `X₁(N) = Γ₁(N)\ℍ*` and the identification of `X(ℂ)` with it (P4, DS §7.7).
   This is the dictionary that §2 avoided for the points. Here it cannot be avoided, because (P1) is a
   statement about the Riemann surface.
4. `∫_{x_{τ'}}^{x_τ} f(τ)dτ ≡ F(τ) − F(τ')` modulo periods (P2, and the definition of the path integral on
   `X₁(N)`).
5. `Λ` = the period group `{∫_γ f(τ)dτ : γ ∈ H₁}` is countable (`H₁` is finitely generated), and
   `F(γτ) − F(τ)` is a period for `γ ∈ Γ₁(N)`.

**Why no printed form can be stated in Lean today.** (P1) needs compact Riemann surfaces, `H₁`, and path
integrals of holomorphic 1-forms. Mathlib v4.35 has complex manifolds but none of these, and the tree's
`CloudB3W17*` modules do not provide them for `X₁(N)`. (P3) is statable over genuine definitions: Mathlib
`Scheme.ord` on an integral `X_ℂ`, with the CloudW07 Picard/Albanese layer. But it is only one of the five
steps. So `AbelJacobiX1` stays a composite leaf candidate.

**An honest alternative.** One could cite (P1)–(P4) as a single composite leaf, as hecke-pin's audit row
does now.

**Proposed kinds row** (an audit Prop, not a hypothesis of the fold): kind `consequence`, strictest
`GLUE` (the dictionary ruling of 11-16). Flag: "composite of DS Thm 6.1.2 (Abel, pp. 214–215), DS §3.3,
Milne JV 1.1/6.1, GAGA (DS §7.2); not printed form".

## 6. New Props and their ratings

| Prop | kind | rating | status |
|---|---|---|---|
| `TauPlace` (new) | GLUE (analytic) | not a leaf | proved (`tauPlace`) |
| `X1TauPoints` (hecke-pin) | GLUE (was: LEAF candidate) | not a leaf: follows from `IsX1Gen`, Mathlib and `WeberField` | proved (`x1TauPoints`) |
| `ConstOnTauPoints` (hecke-pin) | GLUE | not a leaf | proved (`constOnTauPoints`) |
| `AbelJacobiX1` (hecke-pin) | LEAF candidate, composite | not printed form (§5) | open |

No new leaf is introduced.

The autofold spec (`scratch/hecke-glue/autofold.json`) is hecke-pin's spec with the same discharge
(`r16CoreY` by `AfTateLam.r16CoreY_of_ds965`; the fold's leaf set is unchanged). It adds three things:
* the import of HeckeGlue;
* updated audit notes in the three leaves' docs;
* an `audit_props` list in which `X1TauPoints` and `ConstOnTauPoints` are marked `glue (proved,
  AfTateLam.HeckeGlue)` and `AbelJacobiX1` keeps its row.

## 7. Files and checks

* `ZInQKernel/Contrib/OneProof/HeckeGlue.lean`: new, about 800 lines; imports `HeckePin` and CloudW07's
  `Curve.Dimension`. `lake build ZInQKernel.Contrib.OneProof.HeckeGlue` succeeds (VERIFIED).
* `scratch/hecke-glue/HeckeGlue.lean`: the same file (scratch copy).
* `scratch/hecke-glue/Target.lean`: verbatim copies and `Iff.rfl` checks (VERIFIED).
* `scratch/hecke-glue/Discharges.lean` and `-output.txt`: `#discharges` and axioms (VERIFIED).
* `scratch/hecke-glue/autofold.json`: the spec.
* `scratch/hecke-glue/log.md`: the results log.
