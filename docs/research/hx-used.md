# hx-used: the top hypothesis `hX = T5Glue.X0ModuliGalois`, its used form, and its removal by the eta route

Task hx-used, 2026-11-15. Branch `wip/hx-used`, base `43513d87` (leaf-fold25). Lean: contributor file
`ZInQKernel/Contrib/OneProof/X0ModuliUsed.lean` with helper `ZInQKernel/Contrib/OneProof/X0ModuliUsed/EtaRoute.lean`.
Scratch: `scratch/hx-used/` (`log.md`, `Copy.lean`, `EtaRoute.lean`, `X0ModuliUsed.lean`, `Discharges.lean`,
`discharges.txt`, `num/*.py`). Marks used below:
- **VERIFIED**: compiled, computed, or read in a named file.
- **STANDARD**: published, with an exact reference.
- **SPECULATIVE**: not checked.
- **UNVERIFIED**: a theorem number given from memory (this host has no network).

Model work, no human review.

## 0. Result

1. **`hX` is used only at level 32, for x0-32's two coordinates, at Heegner points** (VERIFIED, read; §3). On the route
   to `ZInQ.OneProof.frozenTarget`, `hX` enters only through `T5Glue.shimuraReciprocityModFn_of_printed hCM hX`. Every
   consumer of the resulting `Shimura.ShimuraReciprocityModFn` evaluates it only at `N = 32` and `g ∈ {X0.xC, X0.yC}`.
2. **`hX` can be removed** (VERIFIED, compiled; standard axioms). Those two instances follow from
   - the printed main theorem of CM that is already a top hypothesis, `hCM : T5Glue.ShimuraMainCM`, and
   - one explicit identity between Jacobi's θ and Weierstrass ℘. This is the new glue `X0EtaRoute.ThetaWeierstrass8`,
     equivalent to `X0EtaRoute.XEtaWeierstrass` (x0-32's eta quotient `x` as a ℘-ratio).

   No canonical-model or moduli input is used. `X0ModuliUsed.frozenTarget_of_theta` is `frozenTarget` with `hX`
   replaced by `ThetaWeierstrass8`.
3. **Alternative (the used form).** `X0ModuliUsed.X0ModuliGaloisX0_32` is `X0ModuliGalois` restricted to `N = 32`,
   `g ∈ {x, y}` and Heegner points of level 32.
   - It is implied by `hX` (`x0ModuliGaloisX0_32_of`).
   - It suffices for the consumers (`frozenTarget_of_used`).
4. **Neither variant discharges `hX` as stated.** No theorem proves `T5Glue.X0ModuliGalois`, and `#discharges` lists
   nothing from this file. `hX` is a plain argument of `frozenTarget`, so the fold is manual (§2). The recommended fold
   is the theta route:
   - it replaces a statement that cannot be stated in printed form today (x0-moduli: coarse moduli schemes,
     q-expansion principle) by a concrete analytic identity;
   - that identity is statable over Mathlib's `jacobiTheta₂` and `PeriodPair.weierstrassP`, numerically verified to
     40 digits, and provable in principle (§5).
5. **No statement was changed.** `X0ModuliGalois` is not false, vacuous or inert.

### 0.1 Theorems (verbatim; `#print axioms` output VERIFIED in `scratch/hx-used/discharges.txt`)

The new glue (`X0ModuliUsed/EtaRoute.lean`, namespace `X0EtaRoute`, with `open T5Glue`). It is stated with:
- `pp w = ⟨1, w⟩` (`T5Glue.pp`);
- `ppM M hM τ` = the `PeriodPair` `⟨1/(M:ℂ), τ⟩`;
- `wpRatio P a b c = (P.weierstrassP a - P.weierstrassP c) / (P.weierstrassP b - P.weierstrassP c)`.

```lean
def ThetaWeierstrass8 : Prop :=
  ∀ w : UpperHalfPlane,
    jacobiTheta₂ 0 w / (cexp (Real.pi * I * w / 4) * jacobiTheta₂ ((w : ℂ) / 2) w) =
      1 - 2 * wpRatio (pp w) (1 / 2) (3 * (w : ℂ) / 8) (1 / 2 + (w : ℂ) / 8)

def XEtaWeierstrass : Prop :=
  ∀ τ : UpperHalfPlane,
    ZInQ.Contrib.TYZGenus.X0.xC τ = 2 - 4 * wpRatio (ppM 16 (by norm_num) τ) (1 / 32) (3 * τ / 8) (1 / 32 + τ / 8)
```

Main theorems. All have axioms `[propext, Classical.choice, Quot.sound]`.

```lean
theorem X0EtaRoute.xEtaWeierstrass_of_theta (h : ThetaWeierstrass8) : XEtaWeierstrass
theorem X0EtaRoute.srAt_x (hX : XEtaWeierstrass) (hCM : ShimuraMainCM) :
    X0ModuliUsed.ShimuraReciprocityModFnAt 32 (fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ)
theorem X0EtaRoute.srAt_y (hX : XEtaWeierstrass) (hCM : ShimuraMainCM) :
    X0ModuliUsed.ShimuraReciprocityModFnAt 32 (fun τ => ZInQ.Contrib.TYZGenus.X0.yC τ)

theorem X0ModuliUsed.tyzThm35ReadingA_of_theta (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : T5Glue.ShimuraMainCM) (hT : X0EtaRoute.ThetaWeierstrass8)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33) : ZInQ.Literature.TYZThm35ReadingA
theorem X0ModuliUsed.frozenTarget_of_theta
    (r : HDec.HSyn.OpenResearchLeaves22) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : ZInQ.Contrib.TYZDecomp.TYZThm11Integral) (h29 : ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hT : X0EtaRoute.ThetaWeierstrass8)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
-- the same with `XEtaWeierstrass` in place of `ThetaWeierstrass8`:
theorem X0ModuliUsed.tyzThm35ReadingA_of_eta ... (hXE : X0EtaRoute.XEtaWeierstrass) ...
theorem X0ModuliUsed.frozenTarget_of_eta ... (hXE : X0EtaRoute.XEtaWeierstrass) ...
```

`ShimuraReciprocityModFnAt N g` is the body of `Shimura.ShimuraReciprocityModFn`
(`TYZGenus/ShimuraModFn.lean:76`) with `N`, `g` fixed. `shimuraReciprocityModFn_iff` checks that
`ShimuraReciprocityModFn ↔ ∀ N g, IsRatModFn N g → ShimuraReciprocityModFnAt N g` holds by `Iff.rfl`.

The used-form alternative (`X0ModuliUsed.lean` §1–§4). Same axioms:

```lean
def X0ModuliGaloisHeegnerAt (N : ℕ) (g : UpperHalfPlane → ℂ) : Prop :=
  ∀ (σ : ℂ ≃+* ℂ) (D : ℤ) (Q Q' : HeegnerForm N D) (μ : ℂ),
    (∀ i < N, ∃ a : Qbar, ιC a = modCoord N Q.tauH i) →
    IsConjModel (σ : ℂ →+* ℂ) (pp Q.tauH) (pp Q'.tauH) μ →
    (2 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k < N ∧
      σ ((pp Q.tauH).weierstrassP (1 / N)) = μ ^ 2 * (pp Q'.tauH).weierstrassP (k / N) ∧
      σ ((pp Q.tauH).derivWeierstrassP (1 / N)) = μ ^ 3 * (pp Q'.tauH).derivWeierstrassP (k / N)) →
    σ (g Q.tauH) = g Q'.tauH

def X0ModuliGaloisX0_32 : Prop :=
  X0ModuliGaloisHeegnerAt 32 (fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ) ∧
    X0ModuliGaloisHeegnerAt 32 (fun τ => ZInQ.Contrib.TYZGenus.X0.yC τ)

theorem x0ModuliGaloisX0_32_of (h : T5Glue.X0ModuliGalois) : X0ModuliGaloisX0_32
theorem tyzThm35ReadingA_of_used (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : T5Glue.ShimuraMainCM) (hXU : X0ModuliGaloisX0_32)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33) : ZInQ.Literature.TYZThm35ReadingA
theorem frozenTarget_of_used ... (hCM : _root_.T5Glue.ShimuraMainCM) (hXU : X0ModuliGaloisX0_32) ... : ZInQ.FrozenTarget
```

### 0.2 `#discharges` (VERIFIED, `scratch/hx-used/discharges.txt`)

```
#discharges: 63 open hypotheses, 1987 theorems checked, 7 discharge one
```

- All seven discharges are existing contributions in the import closure:
  - `GRCountX6.prop56X6_of_r5fpCount`, `GapSHPair.…`, `ElkiesX6Star.…`, `R16Split.coreY_of_r16`;
  - `SGA7PersistsNF.…`, `UnipotentForward.…`, `MumfordRigidity.mumfordGroupLaw_of_core`.
- None is from `X0ModuliUsed`. That is expected: this file replaces `hX` and does not prove it.
- `ZInQ.OneProof.frozenTarget` and every theorem above have axioms `[propext, Classical.choice, Quot.sound]`.

`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.X0ModuliUsed`: OK.

## 1. The new Props and their ratings

| Prop | kind | printed form? | reason |
|---|---|---|---|
| `X0EtaRoute.ThetaWeierstrass8` | **GLUE** (an identity of explicit functions) | no | <ul><li>States `θ₀₀(w)/θ₁₀(w) = 1 − 2(℘(1/2) − ℘(1/2 + w/8))/(℘(3w/8) − ℘(1/2 + w/8))` for `⟨1, w⟩`.</li><li>Classical in nature: Jacobi's θ–℘ relations, for instance `℘(u) − ℘(v) = −σ(u−v)σ(u+v)/(σ(u)²σ(v)²)` with `σ ∝ e^{ηz²/2}θ₁`.</li><li>I located no printed source; any theorem number would be UNVERIFIED.</li><li>It is stated over Mathlib's `jacobiTheta₂` and `PeriodPair.weierstrassP` only.</li><li>Numerically VERIFIED: 12 random `w`, worst relative error 5e-41 (§4).</li><li>To be proved by the project (§5).</li></ul> |
| `X0EtaRoute.XEtaWeierstrass` | GLUE, equivalent form | no | <ul><li>Implied by `ThetaWeierstrass8` (`xEtaWeierstrass_of_theta`, with the kernel's `Shimura.xC_theta`).</li><li>Conversely, it implies `ThetaWeierstrass8` at `w = 16τ`, which is every `w`.</li><li>That converse is not compiled; it is not needed.</li></ul> |
| `X0ModuliUsed.X0ModuliGaloisX0_32` (alternative) | consequence, GLUE | no | <ul><li>The canonical model of `X₀(32)` (Shimura 1971 §6.7; Deligne–Rapoport VI–VII; UNVERIFIED numbers), for two eta quotients, at CM points.</li><li>It is a specialization of `hX` (proved). It is not printed for the same reason as `hX` (x0-moduli §0).</li></ul> |

- **Leaves used:** `hCM : T5Glue.ShimuraMainCM` (Shimura 1971 Thm. 5.4, already a top hypothesis, unchanged). The eta
  route applies it at the lattices `⟨1/16, τ_Q⟩` and `⟨1/2, τ_Q⟩`; its statement quantifies over every lattice
  `𝔞 ⊂ K`.
- **Glue used, all proved in the kernel:**
  - from gt-ringclass/t5-glue: `IdeleLatticeScale` (via `ideleLatticeScale_of ringClassLattice invertibleColon`),
    `strongApprox`, `latHatInter`, `latHat_inter_of_sandwich`, `autExtends`, `fixedAlgebraic`,
    `artinLift_of_abs absArtinSurjectiveQNeg`, `ringClass_of_artin`;
  - from tyz-cm: `xC_theta`, `etaModelEquation`, `etaModelInvariant`, `etaModelFricke`, `xC_sub_two_ne_zero`,
    `phiC_eq_some`, `frickeH`.
- **Proposed kinds row** (for the lead):
  - `frozenTarget hT`, `X0EtaRoute.ThetaWeierstrass8`, kind `glue`, counts GLUE;
  - flag "explicit θ–℘ identity, numerically verified (40 digits, 12 points); proof route: Jacobi θ/σ relations";
  - it replaces row `frozenTarget hX` (consequence, GLUE, unread);
  - the strict GLUE count is unchanged (1 → 1).

## 2. The manual fold (not run; for the integration lead)

`autofold.py` does not apply. `hX` is a plain argument of `frozenTarget`, not a bundle field (x0-moduli recorded
`autofold: not a field of the current bundles: ['hX']`). So there is no `autofold.json`. The fold, at base `43513d87`:

- `ZInQKernel/OneProof/Main.lean` imports (l. 1–6): add `import ZInQKernel.Contrib.OneProof.X0ModuliUsed`.
- l. 64: replace the binder `(hX : _root_.T5Glue.X0ModuliGalois)` with `(hT : X0EtaRoute.ThetaWeierstrass8)`.
- l. 70: replace
  `(tyzThm35ReadingA_of_leaves h11 h29 (_root_.T5Glue.shimuraReciprocityModFn_of_printed hCM hX) (ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33 h33))`
  with `(X0ModuliUsed.tyzThm35ReadingA_of_theta h11 h29 hCM hT h33)`.
- The result is exactly `X0ModuliUsed.frozenTarget_of_theta`, which compiles (VERIFIED). Its body is the body of
  `frozenTarget` with that one subterm replaced.
- Docs to regenerate (lead): the `kinds.tsv` row for `hX` → `hT`, `OPEN.md`, and `claims`.
- The Main.lean docstring paragraph "the third, Shimura reciprocity for modular functions, from the two printed
  leaves…" becomes "from `ShimuraMainCM` and the explicit identity `ThetaWeierstrass8` by
  `X0ModuliUsed.tyzThm35ReadingA_of_theta`".
- The alternative fold uses `X0ModuliGaloisX0_32` instead: binder `(hXU : X0ModuliUsed.X0ModuliGaloisX0_32)` and term
  `X0ModuliUsed.tyzThm35ReadingA_of_used h11 h29 hCM hXU h33` (`frozenTarget_of_used`).
- Nothing else in the kernel needs rerouting. `tyzThm35ReadingA_of_theta` re-proves the TYZ chain from the CM inputs
  in this file (§3.2).

## 3. The consumers of `hX` (VERIFIED, read at base)

### 3.1 From `hX` to `ShimuraReciprocityModFn`

- `OneProof/Main.lean:64,70`: `hX` occurs only in `T5Glue.shimuraReciprocityModFn_of_printed hCM hX`.
- `Contrib/OneProof/RingClassLattice.lean`: the chain is
  `:3352 _of_printed` → `:2762 _of_t5''` → `:2754 _of_t5'` → `:2741 _of_t5`
  → `shimuraReciprocityModFn_of_split (cmModuli_of_t5 …) (x0RatStructure_of_leaf hX)` (`:2686`, `:2716`).
- `x0RatStructure_of` (`:819`) applies `hL` at `(N, g, σ₀, τ, τ)` (algebraicity) and at `(N, g, σ, τ, τ')`.
- `_of_split` instantiates `τ = Q.tauH` and `τ' = Q'.tauH` for `Q Q' : HeegnerForm N D` with the same `D`.
- So the used form is `X0ModuliGalois` at Heegner points (`X0ModuliGaloisHeegnerAt`), with `IsRatModFn N g`.

### 3.2 From `ShimuraReciprocityModFn` to TYZ reading A

The chain is `TYZChain/Main.lean:56` (`tyzThm35ReadingA_of_leaves`) → `L321.lean:2156` → `:2137` → `Bridge.lean:3134`
→ `:3071`. Its uses of `hS : ShimuraReciprocityModFn` are:

| use | where | instance used |
|---|---|---|
| `Shimura.shimuraReciprocityPic_of_shimuraModFn hS` | Bridge 3141, 3143; L321 2118, 2127, 2129 | `ShimuraMain.lean:188-191` → `ShimuraModFn.lean:122-128`: `hS 32 xC`, `hS 32 yC` |
| `Shimura.cmFieldOfDefinition_of_shimuraModFn hS` | Bridge 3140; L321 1990 (`znOverH4_of`) | `ShimuraTheta.lean:335` → `cmValueRingClass_of_modFn` → `ShimuraMain.lean:55-59`: `CMValueRingClass` at `32, xC` and `32, yC` |
| `cmAlgebraic_of_cmValue (cmValueRingClass_of_modFn hS)` | Bridge 3144; L321 2117, 2119, 2130 | `Bridge.lean:3102-3108`: `CMValueRingClass` at `32, xC` and `32, yC` |

- `cmValueRingClass_of_modFn` (`ShimuraMain.lean:131`) is generic in `(N, g)`. Its restriction is `cmValueRingClassAt_of`.
- Every use is at `N = 32` and `g ∈ {X0.xC, X0.yC}`.
- This file re-proves the chain from these instances:
  - `shimuraReciprocityPic_of_at`, `cmFieldOfDefinition_of_at`, `cmAlgebraic_of_at`;
  - `znOverH4_of_field`, `lemma321Five_of_cmInputs`, `tyzThm35ReadingA_of_cmInputs`.
- These are the kernel's proofs with the restricted hypothesis. They end in the same Bridge theorem
  `tyzThm35ReadingA_of_ringClassD_sigmaFixesZn_lemma318_thm35First_lemma321Five_shimura`.

### 3.3 gz-heegner

origin/wip/gz-heegner does not use the kernel's `hX`. It introduces the stronger `X0ModuliGaloisMero`, for Heegner
points on `X₀(N)` at the levels of the curves `C_d`. Its relation to `hX` is `x0ModuliGalois_of_mero`. The eta route
covers level 32 only, so it does not replace gz-heegner's hypothesis.

## 4. Numerics (VERIFIED, mpmath 40 digits; `scratch/hx-used/num/`)

- `search_x.py 8`: I searched the weight-0 ratios `(℘(P1) − ℘(P2))/(℘(P3) − ℘(P2))` of `℘_{⟨1/16, τ⟩}`, with `P1`,
  `P2`, `P3` points of `(1/8)⟨1/16, τ⟩` taken mod ±. Exactly two match `x − 2` up to a constant:
  - (Ix): `x = 2 − 4(℘(1/32) − ℘(1/32 + τ/8))/(℘(3τ/8) − ℘(1/32 + τ/8))`;
  - the same with `τ/8 ↔ 3τ/8`.

  With 4-torsion points only (`search_x.py 4`) there is no match. `search_y.py` (℘'-ratio × ℘-ratio) finds no direct
  formula for `y`.
- `check_xy.py`: 12 random `τ`. Worst relative errors:
  - (Ix): 1e-36;
  - (Ix) with `τ/8 ↔ 3τ/8`: 1e-37;
  - (IxW) `x(−1/(32τ)) = 2 − 4(℘₂(τ/2) − ℘₂(τ/2 + 1/16))/(℘₂(3/16) − ℘₂(τ/2 + 1/16))`: 2e-40;
  - (Iy) `8y = x³ + 4x + 16 − (x − 2)²(x(−1/(32τ)) + x + 2)`: 1e-33.
- `check_theta.py`: `ThetaWeierstrass8` at 12 random `w`, worst relative error 5e-41.
- In Lean, only (Ix), as `XEtaWeierstrass` or `ThetaWeierstrass8`, remains an assumption. The second form, (IxW) and
  (Iy) are proved from it and from kernel facts (§6).

## 5. What remains

`ThetaWeierstrass8` needs a Lean proof. A route that I have not attempted (SPECULATIVE):

1. Prove `℘(z) − ℘(v) = c·θ₁(z − v)θ₁(z + v)/(θ₁(z)²θ₁(v)²)`, with `c` independent of `z`, for `⟨1, w⟩`.
   - Both sides are elliptic in `z` with the same double poles and zeros. Their ratio is a bounded entire function,
     hence constant by Mathlib's Liouville theorem.
   - This needs removable singularities at the lattice points and `θ₁`'s quasi-periodicity. Mathlib has
     `jacobiTheta₂` and its functional equations.
2. Evaluate the ratio of differences at `(1/2, 3w/8, 1/2 + w/8)`. The constant `c` and the exponential factors cancel,
   leaving a theta-constant identity. The kernel's theta machinery (tyz-cm's `ShimuraTheta*`, jacobi-lambda) has the
   needed product forms and duplication formulas.

The used-form alternative `X0ModuliGaloisX0_32` remains unprovable for the reason x0-moduli gives: no coarse moduli
schemes in Mathlib.

## 6. Method (the eta route, `X0ModuliUsed/EtaRoute.lean`)

Let `Q, Q'` be Heegner forms of level 32 and discriminant `D`, `J` an ideal, `ρ` acting as `Art(J ∩ O)`, and
`κ(J∩O)(L', L'_N) = c(L, L_N)`.

1. **Choose `σ` and `s`.** `autExtends` gives `σ ∈ Aut(ℂ)` extending `ρ`. `σ` fixes `κ(K)`, so ArtinLift gives an idele
   `s` with `σ = [s, K]` (`ArtinCond`). `ringClass_of_artin` pins its ring class, and the kernel's `IdeleLatticeScale`
   gives `κ(s⁻¹𝔞) = c'L'` and `κ(s⁻¹𝔞_N) = c'L'_N`. These are recorded in the structure `TData`.
2. **Intermediate lattices** (`sInv_latM`). For `dM = 32`, `κ(s⁻¹⟨1/M, τ_Q⟩) = c'⟨1/M, τ_{Q'}⟩`.
   - `exists_v1` gives `v₁` with `s_f v₁ − 1/32 ∈ 𝔞̂` and `κv₁ = c'(p₁/32 + q₁τ')`, `p₁` odd. Oddness holds because
     `16v₁ ∈ s⁻¹𝔞` would force `1/2 ∈ 𝔞` by `K ∩ 𝔞̂ = 𝔞`.
   - ⊆: take `x − jv₁` with `j = p·p₁⁷` and use `32 | p₁⁸ − 1`. Then `j/32 ∈ 𝔟̂ ∩ K = 𝔟` (`latHat_inter_latM`), so
     `d | j`, hence `d | p`.
   - ⊇: by the same construction run backwards.
3. **Torsion points** (`exists_vt`). `s⁻¹(τ/n) ≡ c'(p/n + qτ'/n)` with `q` odd, for `n = 8, M = 16` and `n = 2, M = 2`.
   If `q` were even, `τ/2 ∈ ⟨1/M, τ⟩`, which is false.
4. **Apply `ShimuraMainCM`** (`cm_point`) at `𝔞 = κ⁻¹⟨1/M, τ_Q⟩`, `P = ⟨1/M, τ_Q⟩`, `P' = c'⟨1/M, τ_{Q'}⟩`. This
   gives `σ(℘_P(u)) = μ²c'^{-2}℘_{⟨1/M, τ'⟩}(w)` whenever `κ(s⁻¹u) = c'w`.
5. **Orbits** (`wp16_cases`, `wp2_cases`). In `⟨1/16, τ'⟩` the images of `(1/32, 3τ/8, 1/32 + τ/8)` are `(1/32,
   3qτ'/8, 1/32 + qτ'/8)`. For `q` odd these reduce mod the lattice and ± to one of the two forms of (Ix). The same
   holds in `⟨1/2, τ'⟩` for `(τ/2, 3/16, τ/2 + 1/16) ↦ (τ'/2, 3p₁/16, τ'/2 + p₁/16)`.
6. **Transport and conclusion.**
   - `transport16` and `transport2`, with `ratio_conj`, show that σ maps each ℘-ratio to the corresponding ratio at
     `τ'`.
   - `x_conj` uses (Ix) and its second form (`xEtaWeierstrassPair_of`, from `Γ₀(32)`-invariance under
     `[[3,1],[32,11]]`).
   - `xW_conj` uses (IxW), obtained from (Ix) at `−1/(32τ)` via the scaling `⟨1/16, −1/(32τ)⟩ = (−1/(16τ))⟨1/2, τ⟩`
     (`xC_fricke_wp`).
   - `y_conj` uses `yC_formula`, which comes from `etaModelFricke` and Mathlib's chord formula.
   - Algebraicity: `σ₀` fixing `ℚ̄` satisfies `ArtinCond m e σ₀ 1`, and `s = 1` gives `T₀` with `Q' = Q`, `c' = 1`. Then
     `fixedAlgebraic` applies.
   - The conclusion is `srAt_of_conj`.

Compile notes are in `scratch/hx-used/log.md` §2, §5 and §6. The helper builds in about 30 s and the contributor file
in about 30 s. File sizes: 62 KB and 24 KB.
