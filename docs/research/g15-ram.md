# g15-ram: G15's open Prop `G15RamG`, conductor exponents (clauses (i) and (ii))

Task g15-ram, 2026-11-13. Lean: `scratch/g15-ram/G15Ram.lean` (standalone, importing seven kernel
modules) and `scratch/g15-ram/Tail.lean` (assembled by `scratch/g15-ram/build_tail.sh`). Log:
`scratch/g15-ram/log.md`. Compiler output: `scratch/g15-ram/compile.out`,
`scratch/g15-ram/tail_compile.out`.

Markers: **VERIFIED** = compiled or read here. **STANDARD** = published, with a reference.
**SPECULATIVE** = my judgement. Theorem numbers from memory are **UNVERIFIED** (no network).

## 1. Result

**Verdict.** `G15RamG D u`, copied verbatim from `scratch/g0-mod-newform/`, is a *predicate on
the data* `D : ModData L A`. The fields of `D` are bare representations `r₅`, `r₃`, and the
predicate is false for arbitrary `D`. For example, twisting `r₅` by a Dirichlet character of
conductor `2^k` with `k > U₀ + 1` breaks clause (i) at `p = 2`, because the character's last upper
break at 2 is `k − 1` (STANDARD; this counterexample is not formalized). So `G15RamG` cannot be
proved as a closed statement: it is a claim about the `r_ℓ` that G8 builds.

**Main result (VERIFIED, compiled).** All the local-field ramification theory in G15 is now proved
in Lean. This includes T20 and T21, through t-different's kernel theorems and their transport to
`LadicCond`'s filtrations. `G15RamG D u` follows from G11's output and a strictly smaller Prop on
the same `D`:

```
theorem G15Ram.g15RamG_of_localData
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)  -- glue on G7/G8's D
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)  -- G11's output
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u
```

`Tail.lean` (a verbatim copy of `NewForm.lean` plus this file) plugs this into g0-mod-newform's
tail:

```
theorem G0ModNewform.modularConstituent_tail_R (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists) (hSw : …) (hL8 : LadicCond.SwanIntegral) (hAd : …)
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧
      (∀ p (hp : p.Prime), p ≠ 5 → @G15Ram.LocalData p ⟨hp⟩ 5 _ D.r5) ∧
      G15Ram.LocalData 5 D.r3 ∧ G0Galois.G11Out T D.r5 ∧ G0Galois.G11Out T D.r3) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧ (N : ℝ) ≤ Q_D · M² ∧ CommonConstituent A (J_L)
```

VERIFIED: `lake env lean scratch/g15-ram/G15Ram.lean` exits 0 with no errors and no `sorry`
(about 15 s), and `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all twelve
printed declarations (§4). `Tail.lean` also exits 0 with no errors (about 40 s), and its
`modularConstituent_tail_R` has the same three axioms.

**How the named inputs enter.**
- T20 and T21 enter through the kernel's proved `PkgI6.hilbertDifferentFormula` and
  `PkgI6.differentBound` (t-different, `ZInQKernel/HDecomp/Textbook/Different.lean`), applied to
  `ℤ_p → 𝓞_F`.
- Herbrand's theorem (T22) is not needed. The absolute filtration `LadicCond.upperAbs` is
  defined as the intersection over all finite Galois levels, so `upperAbs p t ⊆ upperSet F t`
  holds by definition. Herbrand is what makes this definition agree with Serre's
  `G^v = lim G^v(F/ℚ_p)`; def-ladic-cond chose the intersection form, so nothing here depends on
  it.
- From t-different, `TDifferent.card_lowerRam_zero` (`|G_0| = e`) is used.
- R6 (Raynaud) and T16 (local reciprocity with the upper numbering theorem) enter only through
  the Props on `D` (`TwistShape`, `TwistUpper`). The objects they speak about (`A` over Glazer's
  `L`, `μ_σ`, `β`) are not yet Lean objects; see §3.

## 2. What is proved

All rows are VERIFIED by compilation. No hypotheses are used beyond those listed.

| Lean | statement | from |
|---|---|---|
| `upperBreakFix_of_hilbertSerre` | `UpperBreakFix p`: for `F ⊆ ℚ̄_p` finite Galois with `e(F/ℚ_p) ≤ a!` and `t > 4a²`, `G_{ℚ_p}^t ⊆ G_F` (Glazer N5 L796-812, L824-827) | `HilbertSerreLadic p`; kernel `GlueConductor.upper_break_le` (D1 arithmetic) |
| `hilbertSerre_of_model` | `HilbertSerreLadic p`: some `G_n` fixes `F`, and `∑_{i<n}(g_i − 1) ≤ e − 1 + e·v_p(e)` | `LadicDVRModel p`; T20 `PkgI6.hilbertDifferentFormula`, T21 `PkgI6.differentBound` |
| `ladicDVRModel_of_Zp` | `LadicDVRModel p` | `LadicDVRModelZp p`; `TDifferent.card_lowerRam_zero`, `TDifferent.map_maximalIdeal_eq_pow` |
| `ladicDVRModelZp` | `LadicDVRModelZp p`: `B = 𝓞_F = integralClosure ℤ_p F` is a DVR, finite, torsion-free, separable and Galois over `ℤ_p`, and `PkgI6.lowerRam ℤ_p B i` matches `ramSet F i` | Mathlib |
| `upperWild` | `UpperWild p`: for `t > 0`, `G_{ℚ_p}^t ⊆ P_p` | Mathlib |
| `wildFixTame` | `WildFixTame p`: if `p ∤ e(F/ℚ_p)`, then `P_p` fixes `F` | Mathlib |
| `localRamG_of` | `LocalRamG u p r` | `UpperBreakFix`, `UpperWild`, `WildFixTame`, `LocalData p r`, `G11Out T r` (`p ≠ ℓ`) |
| `g15RamG_of_localData` (and the intermediate forms `g15RamG_of_pieces`, `…_of_hilbertSerre`, `…_of_model`, `…_of_dvrModel`, `…_of_zpModel`) | `G15RamG D u` | `LocalData`, `G11Out` |
| `modularConstituent_tail_R` (`Tail.lean`) | G13-G16's conclusion | `modularConstituent_tail_G` (g0-mod-newform) and `g15RamG_of_localData` |

### Proof notes

**Break bound at the level of `upperAbs`.**
- `LadicCond.phiAt F` is Herbrand's integral of the step function `t ↦ g_t/g_0`, where
  `g_t = ramCardR F t`. This function is antitone, hence interval integrable
  (`Antitone.intervalIntegrable`).
- Consequently `φ` is monotone, has slope `≤ 1` on `[0, ∞)`, satisfies `φ(u) ≥ u/g_0`, and at
  integers `m` equals `∑_{k<m} g_{k+1}/g_0` (`phi_nat`, via `sum_integral_adjacent_intervals`).
- Let `n` be minimal with `G_n` fixing `F`, and put `w = n − 1`. The kernel's `upper_break_le`
  gives `φ(w) ≤ 4a² < t`. It applies to the last break `w` (`G_w ≠ 1` by minimality) with
  `∑_{i<n}(g_i − 1) ≤ e − 1 + e·v_p(e)`.
- So every `u` with `t ≤ φ(u)` satisfies `u ≥ w + (t − φ(w)) > w`. Hence `ψ(t) > w`,
  `⌈ψ(t)⌉ ≥ n`, and `σ ∈ G_{ψ(t)} ⊆ G_n ⊆ G_F`.

**From T20 + T21.** T20 gives `𝔇_{B/A} = 𝔪^{∑_{i<N}(|G_i|−1)}` and T21 gives `𝔇 ∣ 𝔪^{e−1}(e)`.
Also `(e) = 𝔪^{e·v_p(e)}` in `B` (write `e = p^v u` with `p ∤ u`). Then `pow_dvd_pow_iff`, in the
cancellative monoid of ideals of the DVR `B`, gives `∑_{i<N}(g_i − 1) ≤ e − 1 + e·v_p(e)`.

**The DVR model.**
- `y ∈ F` is integral over `ℤ_p` iff `‖y‖ ≤ 1`. The proof is glue-sqrt-local's spectral-norm
  argument, copied, with `spectralNorm.eq_of_tower` and `PadicAlgCl.spectralNorm_eq` to pass to
  the norm of `ℚ̄_p`.
- `𝓞_F` is local (the norm is ultrametric), Dedekind (`IsIntegralClosure.isDedekindDomain`),
  Noetherian and not a field, so it is a DVR by `IsDiscreteValuationRing.TFAE`. It is finite
  over `ℤ_p` (`IsIntegralClosure.finite`) and torsion-free.
- `Frac(𝓞_F) ≅ F` is Galois and separable over `Frac(ℤ_p) ≅ ℚ_p`. The proof transports along
  `FractionRing.algEquiv` with `IsGalois.of_equiv_equiv`, and checks compatibility on `ℤ_p` with
  `IsLocalization.ringHom_ext`.
- `𝔪^k = (ϖ^k) = {b : ‖b‖ ≤ ‖ϖ‖^k}`.
- `galRestrict ℤ_p ℚ_p F 𝓞_F` and `restrictNormalHom` identify `PkgI6.lowerRam ℤ_p 𝓞_F i` with
  the restrictions to `F` of `ramSet F i`. This gives both the orders and the triviality
  statement.

**Positive upper groups are wild.**
- Given `x ≠ 0`, take `F` to be Mathlib's `FiniteGaloisIntermediateField.adjoin ℚ_p {x}`. The
  `ψ` estimate gives `σ ∈ G_1(F)`.
- Every element of `F^×` is `ϖ^k z` with `‖z‖ = 1`.
- The set of `y` with `‖σy − y‖ < ‖y‖` contains `ϖ` and the units of `F`. It is closed under
  products (the norm is ultrametric and Galois-isometric) and under inverses, so it contains `x`.

**Wild inertia fixes tame extensions.** This argument avoids Serre's "`G_1` is the `p`-Sylow
subgroup of `G_0`".
- The restriction `s` of a wild `σ` lies in the inertia subgroup of `Gal(F/ℚ_p)`, whose order
  is `ramCard F 0 = e`. So `m = orderOf s` divides `e`, and `p ∤ m`.
- Every `σ^k` is wild. Put `y = m⁻¹ ∑_{k<m} σ^k x`; then `σy = y`.
- For `z = x − y`, `m z = ∑_{k<m}(z − σ^k z)`. If `z ≠ 0`, each term has norm `< ‖z‖`, and
  `‖m‖ = 1`, so `‖z‖ < ‖z‖`. Hence `z = 0`, and `x = y` is fixed by `σ`.

## 3. What remains: the Props on `D`

The only remaining hypotheses are glue on G7/G8's construction, plus G11's output. Each is a
`def … : Prop` in `G15Ram.lean` whose docstring names its glue step and source. **None is a
leaf.** Their published inputs are leaves already in the bundles: R6 `PkgI2.RaynaudCriterion`,
T16 `PkgI6.LocalReciprocityUpper`, and Néron–Ogg–Shafarevich.

`LocalData p r` is split by the size of `p`.

1. **`SmallPrimeData p r` (`p ≤ D`).** There are a finite Galois `F ⊆ ℚ̄_p` with
   `e(F/ℚ_p) ≤ (DG₀)!` and a local twist `β` such that:
   - `TwistShape p r F β`: on `G_F ∩ P_p`, `r` is the scalar `β(σ)`. This combines three inputs.
     First, G8's formula `ρ_ℓ(σ) = β(σ)⁻¹a_σμ_σσ`, with `a_σμ_σ = 1` on `G_L`. Second, R6: `A` is
     semistable over `L_v(A[3])` (over `L_v(A[5])` at `p = 3`). Third, D2: wild inertia acts
     trivially on `V_ℓ` (`PkgI2.D2_fixed_of_raynaud`). Here `F` is the Galois closure of
     `L_v(A[3])`, of degree `≤ (DG₀)!` (N5 L819-823).
   - `TwistUpper p F β U₀`: `β = 1` on `G_{ℚ_p}^t ∩ G_F` for `t > U₀`. At odd `p` this holds
     because `β²` is tame (`GlueConductor.char_trivial_of_odd_pgroup`). At `p = 2` it comes from
     T16 together with D3 (`GlueConductor.fourth_pow_mem`), `ψ ≥ id`, and `max(4D², 3e) ≤ U₀`
     (`GlueConductor.max_le_U0`) (N5 L823-844).
2. **`LargePrimeData p r` (`p > D`).** There are a tame finite Galois `F` (`p ∤ e(F)`) and a local
   twist `β` such that:
   - `TwistShape` holds, by good reduction (G3) and Néron–Ogg–Shafarevich;
   - `TwistTame` holds: `β = 1` on `G_F ∩ P_p` (for odd `p`) (N5 L848-851).

   Here `F` is the Galois closure of `L_v`, which is tame since `[L_v:ℚ_p] ≤ D < p`.

**G11's output.** The hypothesis is `G0Galois.G11Out T r` for `T = S_mul ∪ supp M_{S_mul}(u)`
(`GlueDescent.ramSet`), for both `r₅` and `r₃`. This is clause (iii). g0-mod-galois proves it as
`g11` for its construction, and `g11` applies to any `T` satisfying `G2Out K T` and
`G3Out A ℓ T`.

### Honest scope of the `D`-side Props

The following are VERIFIED as logical points, except where marked.
- `LargePrimeData p r` follows from clause (ii) itself (take `F = ⊥`, `β = 1`). So at `p > D` the
  reduction only isolates the local-field fact `WildFixTame`, which is now proved. The
  abelian-variety content of clause (ii) remains inside `LargePrimeData`.
- At `p ≤ D`, `SmallPrimeData` is not implied by clause (i) in that trivial way. It is a
  finite-level statement (a scalar on `G_F ∩ P_p`, with `e(F) ≤ (DG₀)!`) plus a bound for one
  *character* `β`. The ramification theory that turns it into clause (i) (the break bound, and
  "upper groups are wild") is proved here.
- `LocalData p r` is satisfiable (trivial `r`, `F = ⊥`, `β = 1`), so the hypotheses are
  consistent.
- Truth on Glazer's construction is SPECULATIVE but direct from N5 L719-851. `TwistShape` holds
  because `r_ℓ ⊕ r_ℓ ≅ ρ_ℓ` and `ρ_ℓ` is scalar on `G_F ∩ P_p`. For `TwistUpper` at `p = 2`,
  Glazer argues over the Galois closure of `L_v` (degree `≤ D!`). That field's fixer contains
  `G_F`, so the stated form, over the bigger field `F`, is weaker than what Glazer proves.
- These Props cannot be split further yet. R6 and T16 speak about `A` over Glazer's field `L`
  and about G7's cochain `β`, but `ModData` holds only the model over `L'` and the two
  representations. G8's construction of `r_ℓ` from `(μ_σ, a_σ, β)` is not a Lean object anywhere
  in the repository, so "`r = β⁻¹·(Tate action)` on `G_L`" cannot yet be stated.

## 4. Compile record

`lake env lean scratch/g15-ram/G15Ram.lean` (VERIFIED, 2026-11-13) exits 0 with 0 errors and no
`sorry`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each of:
`upperBreakFix_of_hilbertSerre`, `g15RamG_of_pieces`, `g15RamG_of_hilbertSerre`, `upperWild`,
`hilbertSerre_of_model`, `g15RamG_of_model`, `wildFixTame`, `g15RamG_of_dvrModel`,
`ladicDVRModel_of_Zp`, `g15RamG_of_zpModel`, `ladicDVRModelZp`, `g15RamG_of_localData`.

`lake env lean scratch/g15-ram/Tail.lean` exits 0 with 0 errors, and `modularConstituent_tail_R`
has the same three axioms (`scratch/g15-ram/tail_compile.out`).

The verbatim copies were checked by a python string comparison against their sources (log step
3): `ModData`, `U0`, `LocalRamG` and `G15RamG` against `scratch/g0-mod-newform/NewForm.lean`, and
`G0Galois.G11Out` against `scratch/g0-mod-galois/part_galois.lean`.

## 5. Integration

- `modularConstituent_tail_R`, compiled in `Tail.lean`, replaces the tail's hypothesis
  `∃ D, G12Spec D ∧ G14TraceCompat D ∧ G15RamG D u` by
  `∃ D, G12Spec D ∧ G14TraceCompat D ∧ (∀ p ≠ 5, LocalData p D.r5) ∧ LocalData 5 D.r3 ∧
  G11Out T D.r5 ∧ G11Out T D.r3`. It adds no other hypothesis.
- The local-field results (`upperBreakFix_of_hilbertSerre`, `upperWild`, `wildFixTame`,
  `ladicDVRModelZp` and their lemmas) involve only `LadicCond`'s objects and Mathlib. They
  belong next to `ZInQKernel/HDecomp/Conductor/LadicCond.lean`.
- The kernel's open glue `LadicCond.SwanIndependent`, `SwanIntegral` and `AdaptedExists` could
  reuse the same `φ` lemmas (`phi_mono`, `phi_sub_le`, `phi_nat`). `ladicDVRModelZp` also gives
  the kernel a ring-theoretic model of every finite Galois `F ⊆ ℚ̄_p` that is compatible with
  `ramSet`. Together with T22 (t-different), this should bring `SwanIndependent` within reach
  (SPECULATIVE).
