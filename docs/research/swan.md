# swan: the glue Props `SwanIndependent`, `SwanIntegral`, `AdaptedExists`

Task swan, 2026-11-13. Lean: `scratch/swan/Swan.lean`, `scratch/swan/Bridge.lean`, and their
assembly `scratch/swan/All.lean` (`build.sh`). Log: `scratch/swan/log.md`. Compiler output:
`scratch/swan/compile.out`, `scratch/swan/all_compile.out`.

Markers: **VERIFIED** = compiled or read here. **STANDARD** = published, with a reference.
**SPECULATIVE** = my judgement. Theorem numbers from memory are **UNVERIFIED** (no network).

## 1. Result

**All three Props are proved in Lean, unconditionally:** `SwanIndependent` (every `p`),
`SwanIntegral` (L8) and `AdaptedExists` (every `p`). The proofs use Mathlib and the kernel modules
`LadicCond` and `I6Base`. They also use task t-different's proof of the kernel's Herbrand leaf
I6.8 (`PkgI6.herbrandQuotient`), copied in. There are no hypotheses, and no statement was changed.

```
theorem Swan.swanIndependent_proved (p : ℕ) [Fact p.Prime] : LadicCond.SwanIndependent (p := p)
theorem Swan.swanIntegral_proved : LadicCond.SwanIntegral
theorem Swan.adaptedExists_proved (p : ℕ) [Fact p.Prime] : LadicCond.AdaptedExists (p := p)
```

VERIFIED: `lake env lean scratch/swan/All.lean` exits 0, with 0 errors and no `sorry`, in about
35 s. The warnings are deprecations and unused-section-variable linters. `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for `PkgI6.herbrandQuotient`,
`SwanBridge.herbrandUpper_of_quotient`, `Swan.swan_main`, `Swan.swan_proved` and the three
theorems above. The output is in `scratch/swan/all_compile.out`.

### Files

| file | content | compile |
|---|---|---|
| `scratch/swan/Swan.lean` (1020 lines) | §0 verbatim copies (`rfl`-checked); §1-§4 `adaptedExists` (Mathlib only); §5-§8 `swan_main : HerbrandUpper → (all three)`, with H1-H3 proved | exit 0, ~40 s; `scratch/swan/compile.out` |
| `scratch/swan/Bridge.lean` (~470 lines) | `SwanBridge.herbrandUpper_of_quotient : PkgI6.HerbrandQuotient → HerbrandUpper` (the transport from DVRs to the subfields of `ℚ̄_p`) | exit 0 |
| `scratch/swan/All.lean` (2713 lines, made by `build.sh`) | kernel imports; `scratch/t-different/Herbrand.lean` lines 60-1248 (copy in `tdiff_herbrand_src.lean`) and its proof of `PkgI6.herbrandQuotient`; `Swan.lean`; `Bridge.lean`; `final_part.lean` | exit 0, ~35 s; `scratch/swan/all_compile.out` |

All.lean takes the definitions `PkgI6.lowerRam`, `lowerRamR`, `herbrandPhi`, `upperRam` and
`HerbrandQuotient` from the kernel's `I6Base`. A python comparison found them character for
character identical to t-different's copies (VERIFIED), so t-different's proof applies unchanged.

The conjunction `Swan.swan_proved` is exactly the three hypotheses `hSw`, `hL8`, `hAd` of
`G0ModNewform.modularConstituent_tail_G` and `g13_g16_ram` (scratch/g0-mod-newform). It also
discharges the glue hypotheses of the kernel's `LadicCond.carayolR17_of_R17'` and
`carayolR17'_of_R17`. So `CarayolR17` and `CarayolR17'` are now equivalent unconditionally.

### Structure of the proof

1. `AdaptedExists`: an elementary proof from Mathlib (§3 below).
2. `SwanIntegral`, `SwanIndependent` ⇐ `HerbrandUpper` (`Swan.swan_main`), through three
   smaller Props, all proved: H1 `SwanAtIntegral` (finite-level change of variables), H2
   `UpperAbsWild` (`G^u ⊆ P_p` for `u > 0`) and H3 `UpperAbsSurj` (`G^u → G^u(L/ℚ_p)` onto, from
   Herbrand plus compactness).
3. `HerbrandUpper` ⇐ `PkgI6.HerbrandQuotient` (`SwanBridge.herbrandUpper_of_quotient`, §4 below).
4. `PkgI6.HerbrandQuotient` is proved (t-different, `PkgI6.herbrandQuotient`; it is also
   `HSyn.t22a_proved` in `Leaves.lean`).

### The intermediate leaf `HerbrandUpper`

```
def Swan.HerbrandUpper : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L M : Fld p), IsFinGal L → IsFinGal M → L ≤ M → ∀ v : ℝ, 0 < v →
    restr L '' upperSet M v = restr L '' upperSet L v
```

This is Herbrand's theorem (Serre, *Corps locaux* IV §3, Prop. 14, numbering UNVERIFIED) over the
`LadicCond` definitions, restricted to `v > 0`. For finite Galois `L ⊆ M` inside `ℚ̄_p`, the image
of `G^v(M/ℚ_p)` in `Gal(L/ℚ_p)` is `G^v(L/ℚ_p)`. I checked by hand that these definitions are
Serre's: `ramSet L i` is the preimage of `G_i`; `ramSetR` is `G_t = G_{⌈t⌉}`;
`phiAt L u = ∫₀ᵘ g_t/g_0`; `upperSet L v = G_{ψ(v)}`. It is no longer needed as a hypothesis
(step 3), but `swan_main` keeps it as a clean interface.

## 2. Truth of the three statements (analysis, then Lean)

All three are **true as stated** (VERIFIED by the Lean proofs).
Two hypotheses turn out to be unnecessary, which is harmless: `SwanIntegral` never uses
continuity or `p ≠ ℓ`, and `SwanIndependent` holds for every field `k` and every homomorphism
`ρ`, continuous or not.

## 3. The proofs

### `AdaptedExists` (§1-§4 of `Swan.lean`; Mathlib only)

The claim: for continuous `ρ : G_{ℚ_p} → GL_n(ℚ̄_ℓ)` with `ℓ ≠ p`, there is a finite Galois `L`
with `ρ` trivial on `P_p ∩ G_L`. The classical proof (Serre–Tate §2, after Grothendieck: the
image lies in `GL_n(E)`, `E/ℚ_ℓ` finite, by Baire, then pro-`p` against pro-`ℓ`) is replaced by
an elementary argument that needs neither Baire nor `GL_n(𝓞_E)`:

1. `wild_pow_fix`: for `γ ∈ P_p` and finite Galois `L`, some `γ^{p^k}` fixes `L`. Write the order
   of `γ|_L` as `p^k m` with `p ∤ m`, and put `δ = γ^{p^k}`. The map `T x = Σ_{j<m} δ^j x` is
   `ℚ_p`-linear `L → L`. It satisfies `T x = m x + Σ (δ^j x − x)`, where `‖m‖ = 1` and each
   `‖δ^j x − x‖ < ‖x‖`, so `‖T x‖ = ‖x‖` and `T` is injective. Hence `T` is surjective, and its
   image is `δ`-fixed, so `δ` fixes `L`. (`wild_fix_of_coprime`; `P_p` is a subgroup,
   `mul_mem_wildSet`, `inv_mem_wildSet`.)
2. `Bd.pow_sub`, `norm_pow_sub_one_entry`: if every entry of `A` has norm `≤ a = ‖A_{ij}‖ < 1`
   and `ℓ ∤ m`, then `‖((1+A)^m − 1)_{ij}‖ = a`. The proof bounds the entries of
   `(1+A)^m − 1 − mA` by `a²` (by induction), then uses the ultrametric inequality.
3. `exists_level`: continuity and the Krull topology (`krullTopology_mem_nhds_one_iff_of_normal`)
   give, for each `r > 0`, a finite Galois `L` with `ρ(G_L) ⊆ {‖g_{ij} − δ_{ij}‖ < r}`.
4. `adaptedExists`: take `L` for `r = 1`. If `γ ∈ P_p ∩ G_L` had `ρ(γ) = 1 + A ≠ 1`, let
   `a = max ‖A_{ij}‖ ∈ (0,1)` and take `L'` for `r = a`. Some `γ^{p^k}` fixes `L'` (step 1), so
   `‖((1+A)^{p^k} − 1)_{ij}‖ < a`, which contradicts step 2 because `ℓ ∤ p^k`.

### `SwanIntegral` and `SwanIndependent` (§5-§8)

Key lemma `invariants_upperAbs`: for `L` adapted to `ρ` and `u > 0`,
`V^{G^u} = V^{G^u(L) ∩ P_p}`, where `G^u = upperAbs p u` is the absolute upper group. This needs:

- **H2 `UpperAbsWild`** (`G^u ⊆ P_p` for `u > 0`). **Proved**, `upperAbsWild`. The proof has
  three parts. `upperSet_subset_ramSet_one` shows `ψ_L(u) > 0`, using
  `t/g_0 ≤ φ_L(t) ≤ t·|Gal(L/ℚ_p)|/g_0` for `t ≥ 0` and `φ_L ≤ 0` on `[−1, 0]`; the integrand is
  antitone, hence interval integrable. `wildAt_of_ramSet_one` shows that `σ ∈ G_1(L)` gives
  `‖σx − x‖ < ‖x‖` on `L^×`, by writing `x = yϖ^a` with `‖y‖ = 1` (discreteness from `IsUnif`).
  `exists_finGal_mem` puts any `x` into a finite Galois `L` (the normal closure of `ℚ_p(x)`).
- **H3 `UpperAbsSurj`** (every element of `G^u(L) ∩ P_p` agrees on `L` with an element of
  `G^u`). **Proved from `HerbrandUpper`**, `upperAbsSurj_of_herbrand`. The closed sets
  `C_M = {τ : τ|_L = σ|_L, τ ∈ G^u(M)}` have the finite intersection property: apply Herbrand at
  a finite Galois `E` containing `L` and the `M`s (`exists_finGal_above`, compositum), then use
  the compactness of `G_{ℚ_p}` (Mathlib's `CompactSpace Gal(K/k)` for Galois `K/k`). Closedness
  is `isClosed_of_restr`: such a set is a union of cosets of an open fixing subgroup.

Then:

- **H1 `SwanAtIntegral`**: `Sw_L(ρ) = ∫₀^∞ codim V^{G^u(L) ∩ P} du` at an adapted level.
  **Proved**, `swanAtIntegral`. The steps are `phiAt_nat` (`φ_L(j) = Φ_j = Σ_{i=1}^{j} g_i/g_0`),
  `phiAt_piece` (`φ_L` is affine on `[j, j+1]`) and `upperSet_eq` (`G^u(L) = G_{j+1}(L)` for
  `Φ_j < u ≤ Φ_{j+1}`, i.e. `⌈ψ_L(u)⌉ = j+1`). With these, the integrand on `(0, ∞)` is
  `Σ_{j<N} c_{j+1} 1_{(Φ_j, Φ_{j+1}]}`, where `c_i = codim V^{G_i ∩ P}` vanishes for `i ≥ N`
  (`eventuallyTrivial`). Its integral is `Σ c_{j+1}(Φ_{j+1} − Φ_j) = Σ (g_{j+1}/g_0) c_{j+1}`.
- `swanAt_eq_integral_upperAbs`: at any adapted `L`, `Sw_L(ρ) = ∫₀^∞ codim V^{G^u} du`. This gives
  `SwanIntegral` directly (`swanIntegral_of`). It also gives `SwanIndependent` (`swanIndependent_of`):
  two adapted levels compute the same integral.

### The transport `HerbrandUpper ⇐ PkgI6.HerbrandQuotient` (`Bridge.lean`)

For finite Galois `E/ℚ_p` inside `ℚ̄_p`, take `𝓞_E = {x ∈ E : ‖x‖ ≤ 1}` as a
`Subalgebra ℤ_[p] ℚ̄_p` (`SwanBridge.OE`).

- `isIntegral_iff_norm_le_one`: `y ∈ ℚ̄_p` is integral over `ℤ_p` iff `‖y‖ ≤ 1`. The proof goes
  through the spectral norm and `spectralValue_le_one_iff`, adapting
  `scratch/glue-sqrt-local/Local.lean`. It gives `IsIntegralClosure (OE E) ℤ_[p] E`, hence
  `IsFractionRing` and `Module.Finite ℤ_[p] (OE E)` (`IsIntegralClosure.finite`).
- `dvr_OE`: `𝓞_E` is a DVR (`ofHasUnitMulPowIrreducibleFactorization`, with the uniformizer of
  `LadicCond.exists_isUnif`). Units are the elements of norm 1, divisibility is comparison of norms,
  and `𝔪^{i+1} = {‖x‖ ≤ ‖ϖ‖^{i+1}}` (`mem_maximalIdeal_pow`).
- `isGalois_frac`: `IsGalois (FractionRing ℤ_[p]) (FractionRing 𝓞_E)` under
  `FractionRing.liftAlgebra`, by `IsGalois.of_equiv_equiv`. The residue field of `ℤ_[p]` is
  perfect (finite, via `PadicInt.residueField`).
- `res E = galRestrict ∘ restrictNormalHom : G_{ℚ_p} → Gal(𝓞_E/ℤ_p)` is surjective, and
  `res E σ = res E τ ↔ σ|_E = τ|_E`. Under it, `PkgI6.lowerRam` corresponds to `ramSet`
  (`ramSet_iff`), `Nat.card (lowerRamR t)` equals `ramCardR E t` (`card_lowerRamR`),
  `herbrandPhi = phiAt` (`herbrandPhi_eq`) and `upperRam` corresponds to `upperSet`
  (`upperSet_iff`).
- `herbrandUpper_of_quotient`: apply the leaf at `A = ℤ_[p]`, `C = 𝓞_L`, `B = 𝓞_M`. The map `r`
  is the restriction `Gal(𝓞_M) → Gal(𝓞_L)`, built through `res M` (surjective) and `res L`; then
  translate both directions of `upperRam(𝓞_L) v = r(upperRam(𝓞_M) v)`.

## 4. Integration notes

1. `All.lean` imports only the kernel modules `ZInQKernel.HDecomp.Conductor.LadicCond` and
   `ZInQKernel.HDecomp.Conductor.I6Base`. As kernel modules, the natural split is: t-different's
   `TDifferent` part (if not already adopted), then `Swan.lean`, then `Bridge.lean`, then
   `final_part.lean`. The consumers in g0-mod-newform then drop `hSw`, `hL8` and `hAd`, using
   `Swan.swanIndependent_proved`, `Swan.swanIntegral_proved` and `Swan.adaptedExists_proved`.
2. Mathlib names that changed or are deprecated and appear here: `if_pos`/`if_neg` (deprecated in
   this Mathlib, still present), `integral_finsetSum` (renamed from `integral_finset_sum`).
3. `Bridge.lean` is reusable. It is the first concrete instantiation of the DVR-based leaves of
   pkg-I6 (I6.6-I6.9) at the rings of integers of the finite Galois subfields of `ℚ̄_p`, with the
   dictionary to `LadicCond`'s ramification groups. The same `OE`, `dvr_OE`, `isGalois_frac` and
   `res` should transport `HilbertDifferentFormula` and `DifferentBound` to `LadicCond`'s setting.

## 5. Leaves and glue, summary

| Prop | status | Lean |
|---|---|---|
| `LadicCond.AdaptedExists` | **proved** (Mathlib only) | `Swan.adaptedExists` |
| `LadicCond.SwanIntegral` (L8) | **proved** | `Swan.swanIntegral_proved` (All.lean) |
| `LadicCond.SwanIndependent` | **proved** | `Swan.swanIndependent_proved` (All.lean) |
| H1 `Swan.SwanAtIntegral` (glue) | **proved** | `Swan.swanAtIntegral` |
| H2 `Swan.UpperAbsWild` (glue) | **proved** | `Swan.upperAbsWild` |
| H3 `Swan.UpperAbsSurj` (glue) | **proved from `HerbrandUpper`** | `Swan.upperAbsSurj_of_herbrand` |
| `Swan.HerbrandUpper` (Herbrand over `LadicCond`) | **proved from I6.8** | `SwanBridge.herbrandUpper_of_quotient` |
| `PkgI6.HerbrandQuotient` (I6.8 = T22a) | **proved** (t-different) | `PkgI6.herbrandQuotient`, copied into All.lean |

No leaf remains for these three Props.
