# swan: the glue Props `SwanIndependent`, `SwanIntegral`, `AdaptedExists`

Task swan, 2026-11-13. Lean: `scratch/swan/Swan.lean` (imports only the kernel module
`ZInQKernel.HDecomp.Conductor.LadicCond` and Mathlib). Log: `scratch/swan/log.md`. Compiler
output: `scratch/swan/compile.out`.

Markers: **VERIFIED** = compiled or read here. **STANDARD** = published, with a reference.
**SPECULATIVE** = my judgement. Theorem numbers from memory are **UNVERIFIED** (no network).

## 1. Result

**`AdaptedExists` is proved outright. `SwanIndependent` and `SwanIntegral` are proved from a single
leaf, Herbrand's theorem (`Swan.HerbrandUpper`).** No other hypothesis is used. The two other
reduction steps, the finite-level change of variables (H1) and "the absolute upper groups lie in
wild inertia" (H2), are proved in Lean, and so is the passage from Herbrand's theorem to the
surjectivity `G^u → G^u(L/ℚ_p)` (H3).

VERIFIED: `lake env lean scratch/swan/Swan.lean` exits 0, with 0 errors and no `sorry`. The only
warnings are four deprecation notices for `if_pos`/`if_neg`. `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for all ten declarations printed: `adaptedExists`,
`swanIntegral_of`, `swanIndependent_of`, `swan_all`, `upperAbsSurj_of_herbrand`, `swan_all'`,
`upperAbsWild`, `swan_final`, `swanAtIntegral`, `swan_main`. A run takes about 40 s.

```
theorem Swan.adaptedExists {p : ℕ} [Fact p.Prime] : LadicCond.AdaptedExists (p := p)

theorem Swan.swan_main (hH : HerbrandUpper) :
    (∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) ∧ LadicCond.SwanIntegral ∧
      (∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
```

The conjunction is exactly the three hypotheses `hSw`, `hL8`, `hAd` of
`G0ModNewform.modularConstituent_tail_G` and `g13_g16_ram` (scratch/g0-mod-newform), and of the
kernel's `LadicCond.carayolR17_of_R17'` and `carayolR17'_of_R17`. The statements are the kernel's
own (`LadicCond.*`, used directly as the theorem types). §0 of `Swan.lean` also repeats them
verbatim and checks the copies equal by `rfl`.

### The leaf

```
/-- Leaf H3a: Herbrand's theorem (Serre, Corps locaux IV §3, Prop. 14, numbering UNVERIFIED). -/
def Swan.HerbrandUpper : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L M : Fld p), IsFinGal L → IsFinGal M → L ≤ M → ∀ v : ℝ, 0 < v →
    restr L '' upperSet M v = restr L '' upperSet L v
```

For finite Galois `L ⊆ M` inside `ℚ̄_p` and `v > 0`, the image of `G^v(M/ℚ_p)` in `Gal(L/ℚ_p)` is
`G^v(L/ℚ_p)`, i.e. `(G/H)^v = G^vH/H` with `G = Gal(M/ℚ_p)`, `H = Gal(M/L)`. It is stated over
the kernel's definitions of `LadicCond` (`ramSet`, `ramCardR`, `phiAt`, `upperSet`). I checked by
hand that these are Serre's definitions: `ramSet L i` is the preimage of `G_i` (`v_L(σx − x) ≥ i+1`
on `𝓞_L`); `ramSetR` is Serre's `G_t = G_{⌈t⌉}`; `phiAt L u = ∫₀ᵘ g_t/g_0 dt`; and
`upperSet L v = G_{ψ(v)}` with `ψ(v) = sInf {u ≥ −1 | v ≤ φ(u)}`. Under these definitions the
leaf is Serre's statement restricted to `v > 0` (the range used). It is **weaker** than the
published statement.

It is the same theorem as the kernel's leaf I6.8 `PkgI6.HerbrandQuotient`, stated there over
DVRs `A → C → B`. That leaf is **proved** (task t-different, `PkgI6.herbrandQuotient`,
`scratch/t-different/Herbrand.lean`; `HSyn.t22a_proved` in `Leaves.lean`). Deriving
`HerbrandUpper` from it needs the standard transport (§4): `𝓞_L ⊆ 𝓞_M` inside `ℚ̄_p` are DVRs
finite over `ℤ_p`, with `Gal(𝓞_M/ℤ_p) = Gal(M/ℚ_p)` carrying lower groups to `ramSet`. That
transport is not done here, so the leaf is not yet discharged.

## 2. Truth of the three statements (analysis, then Lean)

All three are **true as stated** (VERIFIED by the Lean proofs, modulo Herbrand for two of them).
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

## 4. What remains

1. **Discharge the leaf `HerbrandUpper` from the proved `PkgI6.herbrandQuotient`** (GLUE,
   standard transport, not done). It needs: `𝓞_E = {x ∈ E : ‖x‖ ≤ 1}` is a DVR, finite and
   torsion-free over `ℤ_p`, with fraction field `E` and `IsGalois` over `FractionRing ℤ_p`
   (through `FractionRing.liftAlgebra`); and `Gal(𝓞_M/ℤ_p) ≅ Gal(M/ℚ_p)` (Galois-invariance of
   the spectral norm) carries `PkgI6.lowerRam` to `LadicCond.ramSet`
   (`𝔪^{i+1} = {‖x‖ ≤ ‖ϖ‖^{i+1}}`), cardinalities to `ramCard`, `herbrandPhi` to `phiAt` and
   `upperRam` to `upperSet`. Then `HerbrandUpper` is `PkgI6.HerbrandQuotient` at
   `A = ℤ_p`, `C = 𝓞_L`, `B = 𝓞_M`. The t-different proof uses no completeness, so `A` may be
   any DVR model of `ℤ_p`. Rough size: 600-1000 lines (SPECULATIVE).
2. Integration: `Swan.lean` imports only the kernel's `LadicCond`, so it can become a kernel
   module as it stands. The consumers in g0-mod-newform then take `(swan_main hH).1`, `.2.1`
   and `.2.2` for `hSw`, `hL8` and `hAd`.

## 5. Leaves and glue, summary

| Prop | status | from |
|---|---|---|
| `LadicCond.AdaptedExists` | **proved** | Mathlib |
| `LadicCond.SwanIntegral` (L8) | **proved from one leaf** | `HerbrandUpper` |
| `LadicCond.SwanIndependent` | **proved from one leaf** | `HerbrandUpper` |
| H1 `Swan.SwanAtIntegral` (glue) | **proved** | Mathlib |
| H2 `Swan.UpperAbsWild` (glue) | **proved** | Mathlib |
| H3 `Swan.UpperAbsSurj` (glue) | **proved from one leaf** | `HerbrandUpper` + compactness |
| `Swan.HerbrandUpper` (leaf) | open here | Serre IV §3 Prop. 14 (UNVERIFIED numbering); same theorem as I6.8, which t-different proves over DVRs |
