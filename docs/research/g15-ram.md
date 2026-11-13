# g15-ram: G15's open Prop `G15RamG`, conductor exponents (clauses (i) and (ii))

Task g15-ram, 2026-11-13. Lean: `scratch/g15-ram/G15Ram.lean` (standalone, imports seven kernel
modules). Log: `scratch/g15-ram/log.md`. Compiler output: `scratch/g15-ram/compile.out`.

Markers: **VERIFIED** = compiled or read here. **STANDARD** = published, with a reference.
**SPECULATIVE** = my judgement. Theorem numbers from memory are **UNVERIFIED** (no network).

## 1. Result

**Verdict.** `G15RamG D u` (copied verbatim from `scratch/g0-mod-newform/`) is a *predicate on
the data* `D : ModData L A`, whose fields are bare representations `r₅`, `r₃`. It is false for
arbitrary `D`. For example, twisting `r₅` by a Dirichlet character of conductor `2^k` with
`k > U₀ + 1` breaks clause (i) at `p = 2`, because the character's last upper break at 2 is
`k − 1` (STANDARD; this counterexample is not formalized). So `G15RamG` cannot be proved as a
closed statement. It is a claim about the `r_ℓ` that G8
builds. What this task proves is that **`G15RamG D u` follows from closed local-field Props and
smaller Props on the same `D`**. All of the local-field side except one transport is now proved:

```
theorem G15Ram.g15RamG_of_dvrModel
    (hM : ∀ (p : ℕ) [Fact p.Prime], LadicDVRModel p)          -- glue: transport (DVR model)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)  -- glue on G7/G8's D
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)  -- G11's output
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u
```

and, plugged into g0-mod-newform's tail (`scratch/g15-ram/Tail.lean`, a verbatim copy of
`NewForm.lean` plus this file):

```
theorem G0ModNewform.modularConstituent_tail_R (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists) (hSw : …) (hL8 : LadicCond.SwanIntegral) (hAd : …)
    (hM : ∀ (p : ℕ) [Fact p.Prime], G15Ram.LadicDVRModel p)
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧
      (∀ p (hp : p.Prime), p ≠ 5 → @G15Ram.LocalData p ⟨hp⟩ 5 _ D.r5) ∧
      G15Ram.LocalData 5 D.r3 ∧ G0Galois.G11Out T D.r5 ∧ G0Galois.G11Out T D.r3) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧ (N : ℝ) ≤ Q_D · M² ∧ CommonConstituent A (J_L)
```

VERIFIED: `lake env lean scratch/g15-ram/G15Ram.lean` exits 0 with no errors and no `sorry`;
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every printed declaration
(see §4). The same holds for `Tail.lean` (`modularConstituent_tail_R`, about 40 s).

T20 and T21 enter through the kernel's proved theorems `PkgI6.hilbertDifferentFormula` and
`PkgI6.differentBound` (t-different, `ZInQKernel/HDecomp/Textbook/Different.lean`). T22
(Herbrand) is not needed: the absolute upper filtration `LadicCond.upperAbs` is defined as the
intersection over all finite Galois levels, so `upperAbs p t ⊆ upperSet F t` holds by definition,
and the break bound is proved directly at the level `F` (§2). (Herbrand's theorem is what makes
that definition agree with Serre's `G^v = lim G^v(F/ℚ_p)`; def-ladic-cond chose the
intersection form, so nothing here depends on it.) R6 (Raynaud) and T16 (local
reciprocity with upper numbering) enter only through the Props on `D` (`TwistShape`,
`TwistUpper`), because the objects they speak about (`A` over Glazer's `L`, `μ_σ`, `β`) are not
yet Lean objects; see §3.

## 2. What is proved (all VERIFIED by compilation)

| Lean | statement | from |
|---|---|---|
| `upperBreakFix_of_hilbertSerre` | `UpperBreakFix p`: for `F ⊆ ℚ̄_p` finite Galois with `e(F/ℚ_p) ≤ a!` and `t > 4a²`, `G_{ℚ_p}^t ⊆ G_F` (Glazer N5 L796-812, L824-827) | `HilbertSerreLadic p`, kernel `GlueConductor.upper_break_le` |
| `upperWild` | `UpperWild p`: for `t > 0`, `G_{ℚ_p}^t ⊆ P_p` (`‖σx − x‖ < ‖x‖` for all `x ≠ 0`) | nothing (Mathlib) |
| `wildFixTame` | `WildFixTame p`: if `F` is finite Galois and `p ∤ e(F/ℚ_p)`, `P_p` fixes `F` | nothing (Mathlib) |
| `hilbertSerre_of_model` | `HilbertSerreLadic p` | `LadicDVRModel p`, T20 `PkgI6.hilbertDifferentFormula`, T21 `PkgI6.differentBound` |
| `localRamG_of` | `LocalRamG u p r` | `UpperBreakFix`, `UpperWild`, `WildFixTame`, `LocalData p r`, `G11Out T r` (`p ≠ ℓ`) |
| `g15RamG_of_pieces`, `g15RamG_of_hilbertSerre`, `g15RamG_of_model`, `g15RamG_of_dvrModel` | `G15RamG D u` | as above, at every prime (`r₅` at `p ≠ 5`, `r₃` at `p = 5`) |
| `modularConstituent_tail_R` (`Tail.lean`) | G13-G16's conclusion | `modularConstituent_tail_G` (g0-mod-newform) and `g15RamG_of_dvrModel` |

Proof notes.

* **Break bound at the level of `upperAbs`.** `LadicCond.phiAt F` is Herbrand's integral of the
  step function `t ↦ g_t/g_0` (`g_t = ramCardR F t`). This function is antitone, hence interval
  integrable (`Antitone.intervalIntegrable`); `φ` is monotone, has slope `≤ 1` on `[0, ∞)`,
  satisfies `φ(u) ≥ u/g_0`, and `φ(m) = ∑_{k<m} g_{k+1}/g_0` at integers (`phi_nat`, via
  `sum_integral_adjacent_intervals`). Let `n` be minimal with `G_n` fixing `F`, and put
  `w = n − 1`. Then `φ(w) ≤ 4a² < t`, by the kernel's D1 arithmetic `upper_break_le` applied to
  the last break `w` (`G_w ≠ 1` by minimality) and to the bound `∑_{i<n}(g_i − 1) ≤ e − 1 + e·v_p(e)`.
  So every `u` with `t ≤ φ(u)` satisfies `u ≥ w + (t − φ(w)) > w`, hence `ψ(t) > w` and
  `⌈ψ(t)⌉ ≥ n`, so `σ ∈ G_{ψ(t)} ⊆ G_n ⊆ G_F`.
* **Positive upper groups are wild.** For `x ≠ 0`, take `F` = Mathlib's
  `FiniteGaloisIntermediateField.adjoin ℚ_p {x}`. The same `ψ` estimate gives `σ ∈ G_1(F)`.
  Every `x ∈ F^×` is `ϖ^k z` with `‖z‖ = 1`: `|F^×| = |ϖ|^ℤ` follows from `IsUnif` and
  `exists_mem_Ioc_zpow`. The set of `y` with `‖σy − y‖ < ‖y‖` contains `ϖ` and the units of `F`,
  and is closed under products (the norm is ultrametric, `PadicAlgCl.isUltrametricDist`, and
  Galois-isometric) and under inverses.
* **Wild inertia fixes tame extensions** (Serre's "`G_1` is the `p`-Sylow subgroup of `G_0`"
  is avoided). Write `s` for the restriction of a wild `σ` to `F`. It lies in the inertia
  subgroup `(inertiaSub F).map restrictNormalHom` of `Gal(F/ℚ_p)`, whose order is
  `ramCard F 0 = e` (`ramCard_zero_eq`, using `IsUnif` to identify `ramSet F 0` with
  `{‖σx − x‖ < 1}`). So `m = orderOf s` divides `e` and `p ∤ m`. Every `σ^k` is wild, because
  wildness is closed under products. Put `y = m⁻¹ ∑_{k<m} σ^k x`; then `σy = y`, since
  `σ^m x = x`. For `z = x − y` we get `m z = ∑_{k<m}(z − σ^k z)`. If `z ≠ 0`, each term has norm
  `< ‖z‖`, and `‖m‖ = 1`, so `‖z‖ < ‖z‖`. Hence `x = y` is fixed.
* **From T20 + T21.** `𝔇_{B/A} = 𝔪^{∑_{i<N}(|G_i|−1)}` (T20), `𝔇 ∣ 𝔪^{e−1}(e)` (T21), and
  `(e) = 𝔪^{e·v_p(e)}` in `B` (write `e = p^v u`, `p ∤ u`). Then `pow_dvd_pow_iff` in the
  cancellative monoid of ideals of the DVR `B` gives `∑_{i<N}(g_i − 1) ≤ e − 1 + e·v_p(e)`.

## 3. What remains: the smaller named Props

Each is a `def … : Prop` in `scratch/g15-ram/G15Ram.lean` with a docstring naming its glue step
and source. **None of them is a leaf**: all are glue. Their published inputs are leaves that are
already in the bundles (R6 `PkgI2.RaynaudCriterion`, T16 `PkgI6.LocalReciprocityUpper`,
Néron–Ogg–Shafarevich) or proved textbook results (T20, T21).

**Closed local-field glue (no `D`):**

1. `LadicDVRModel p` (transport). For `F ⊆ ℚ̄_p` finite Galois there are a complete DVR `A`
   with perfect residue field and a DVR `B` finite, torsion-free, separable and Galois over it
   (`ℤ_p` and `𝓞_F`), whose `PkgI6.lowerRam A B i` have orders `ramCard F i` and are trivial only
   when `ramSet F i` fixes `F`, with `e(B/A) = ramCard F 0`, `(p) = 𝔪_B^e`, and every integer
   prime to `p` a unit of `B`. Truth: STANDARD (Serre, *Corps locaux* II §2, IV §1; UNVERIFIED
   numbering). In Mathlib this needs the valuation ring of `F` as a DVR, and the identification
   `Gal(F/ℚ_p) ≅ Aut_{ℤ_p}(𝓞_F)` compatible with the two filtrations. glue-sqrt-local
   (docs/research/glue-sqrt-local.md) already proved `y ∈ F` integral over `ℤ_p` iff its
   spectral norm is `≤ 1` (`isIntegral_iff_spectralNorm_le_one`) and the locality of the integral
   closure; neither is copied here. Size: SPECULATIVE, medium (0.5-1.5k lines).
2. ~~`WildFixTame p`~~: **proved** (`wildFixTame`, §2).

**Glue on G7/G8's construction (Props on `D`), `LocalData p r`:**

3. `SmallPrimeData p r` (`p ≤ D`): there are a finite Galois `F ⊆ ℚ̄_p` with
   `e(F/ℚ_p) ≤ (DG₀)!` and a local twist `β` such that
   - `TwistShape p r F β`: on `G_F ∩ P_p`, `r` is the scalar `β(σ)`. This is G8's formula
     `ρ_ℓ(σ) = β(σ)⁻¹a_σμ_σσ` with `a_σμ_σ = 1` on `G_L`, together with R6 (Raynaud: `A`
     semistable over `L_v(A[3])`, or `L_v(A[5])` at `p = 3`) and D2 (wild inertia trivial on
     `V_ℓ`, `PkgI2.D2_fixed_of_raynaud`). `F` is the Galois closure of `L_v(A[3])`, of degree
     `≤ (DG₀)!` (N5 L819-823).
   - `TwistUpper p F β U₀`: `β = 1` on `G_{ℚ_p}^t ∩ G_F` for `t > U₀`. At odd `p` this holds
     because `β²` is tame (`GlueConductor.char_trivial_of_odd_pgroup`). At `p = 2` it comes from
     T16 with D3 (`GlueConductor.fourth_pow_mem`) and `ψ ≥ id`, and
     `max(4D², 3e) ≤ U₀` (`GlueConductor.max_le_U0`) (N5 L823-844).
4. `LargePrimeData p r` (`p > D`): a tame finite Galois `F` (`p ∤ e(F)`, the Galois closure of
   `L_v`, since `[L_v:ℚ_p] ≤ D < p`) with `TwistShape` (by good reduction (G3) and
   Néron–Ogg–Shafarevich) and `TwistTame` (`β = 1` on `G_F ∩ P_p`, odd `p`) (N5 L848-851).

**G11's output:** `G0Galois.G11Out T r` for `T = S_mul ∪ supp M_{S_mul}(u)`
(`GlueDescent.ramSet`), for `r₅` and `r₃`. This is clause (iii), which g0-mod-galois proves as
`g11` for its construction.

**Honest scope of the `D`-side Props (VERIFIED as logical points).**
- `LargePrimeData p r` follows from clause (ii) itself (take `F = ⊥`, `β = 1`). So at `p > D` the
  reduction only separates out the local-field fact `WildFixTame`, now proved. The
  abelian-variety content of clause (ii) is still in `LargePrimeData`.
- At `p ≤ D`, `SmallPrimeData` is not implied by clause (i) in that trivial way. It is a
  finite-level statement (a scalar on `G_F ∩ P_p` with `e(F) ≤ (DG₀)!`) plus a bound for one
  *character* `β`. The ramification theory that turns this into clause (i) (the break bound, and
  "upper groups are wild") is proved here.
- `LocalData p r` is satisfiable (trivial `r`, `F = ⊥`, `β = 1`), so the hypotheses are
  consistent.
- Truth on Glazer's construction (SPECULATIVE but direct from N5 L719-851). `TwistShape` holds
  because `r_ℓ ⊕ r_ℓ ≅ ρ_ℓ` and `ρ_ℓ` is scalar on `G_F ∩ P_p`. `TwistUpper` at `p = 2` uses
  Glazer's argument over the Galois closure of `L_v` (degree `≤ D!`), whose fixer contains
  `G_F`, so the stated form (over the bigger field `F`) is weaker than what Glazer proves.
- Why the `D`-side Props cannot be split further now: R6 and T16 speak about `A` over Glazer's
  field `L` and about the cochain `β` of G7. `ModData` contains only the model over `L'` and the
  two representations. The construction of `r_ℓ` from `(μ_σ, a_σ, β)` (G8) is not a Lean object
  anywhere in the repository, so "`r = β⁻¹·(Tate action)` on `G_L`" cannot yet be stated.

## 4. Compile record

`lake env lean scratch/g15-ram/G15Ram.lean` (VERIFIED, 2026-11-13; see the log for timings):
exit 0, 0 errors, no `sorry`. `#print axioms` = `[propext, Classical.choice, Quot.sound]` for
`upperBreakFix_of_hilbertSerre`, `g15RamG_of_pieces`, `g15RamG_of_hilbertSerre`, `upperWild`,
`hilbertSerre_of_model`, `g15RamG_of_model`, `wildFixTame`, `g15RamG_of_dvrModel`; and for
`modularConstituent_tail_R` in `Tail.lean` (`scratch/g15-ram/tail_compile.out`).

Verbatim copies (checked by a python string comparison against the sources, log step 3): `ModData`, `U0`,
`LocalRamG`, `G15RamG` (from `scratch/g0-mod-newform/NewForm.lean`) and `G0Galois.G11Out` (from
`scratch/g0-mod-galois/part_galois.lean`).

## 5. Integration

- `modularConstituent_tail_R` (compiled in `Tail.lean`) replaces the tail's hypothesis
  `∃ D, G12Spec D ∧ G14TraceCompat D ∧ G15RamG D u` by
  `∃ D, G12Spec D ∧ G14TraceCompat D ∧ (∀ p ≠ 5, LocalData p D.r5) ∧ LocalData 5 D.r3 ∧
  G11Out T D.r5 ∧ G11Out T D.r3`, and adds the closed hypothesis `LadicDVRModel`.
  `T = GlueDescent.ramSet S_mul u` is a set for which g0-mod-galois's `g11` applies (its
  hypotheses `G2Out K T`, `G3Out A ℓ T` are for an arbitrary `T`).
- The new local-field lemmas (`ramSet_anti`, `ramCardR_anti`, `phi_nat`, `phi_sub_le`,
  `wild_of_ramSet_one`, …) concern only `LadicCond`'s objects. They belong next to
  `ZInQKernel/HDecomp/Conductor/LadicCond.lean`.
