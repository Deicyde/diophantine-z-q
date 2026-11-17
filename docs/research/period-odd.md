# period-odd: the Gross–Zagier formula for `C_d` without `CdTwistedPeriodOdd`

Status: research note (task period-odd, 2026-11-16), branch `wip/period-odd`, base wip/cd-optimal 04d7251c.
Lean: new files `ZInQKernel/Contrib/OneProof/PeriodOdd.lean` and `ZInQKernel/Contrib/OneProof/PeriodOdd/`
(`LFunction.lean`, `Isogeny.lean`, `NeZero.lean`). Nothing else under `ZInQKernel/` was edited. Scratch, checks
and log: `scratch/period-odd/`.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published theorem with an
exact reference. **SPECULATIVE**: an assessment. This host has no network; **every theorem number and locator of
the literature below is UNVERIFIED** (from memory).

---

## 0. Main result

**Target met.** `CdTwistedPeriodOdd` is not proved. It is no longer needed: the Gross–Zagier formula for `C_d`
now follows from the two printed leaves alone (Lean, standard axioms, VERIFIED):

```lean
-- ZInQKernel/Contrib/OneProof/PeriodOdd.lean
theorem ZInQ.PeriodOdd.grossZagierFormulaCd_of_etaW32
    (hGZ : ZInQ.GZOptimal.GrossZagierModuliOptCd) (hW : ZInQ.CdOpt.EtaW32Character) :
    ZInQ.GZHL3.GrossZagierFormulaCd
```

So in gz-optimal's route A, `hL3` is replaced by `GrossZagierModuliOptCd` + `EtaW32Character`. Both are printed
leaves with unchanged statements and ratings:
- `GrossZagierModuliOptCd`: Gross–Zagier 1986, the strong Weil case. It is gz-optimal's leaf.
- `EtaW32Character`: one instance of the Newman / Gordon–Hughes eta-quotient law. It is cd-optimal's leaf.

The chain also uses heegner-32's `hCM` (already an argument of the top theorem) and gz-conj's proved conjugation
relation. **No new leaf and no new glue.** `scratch/period-odd/MainEdit.lean` proves `ZInQ.FrozenTarget`
(`frozenTarget_periododd`, axioms `[propext, Classical.choice, Quot.sound]`, VERIFIED). It is cd-optimal's
`frozenTarget_cdoptimal` with the argument `CdTwistedPeriodOdd` deleted.

**Why `CdTwistedPeriodOdd` can be skipped.** cd-optimal proved `Λ_d ⊆ L` from `EtaW32Character`. Its Gaussian
classification then leaves two cases (with `Λ_d ≠ 0`, proved here):
1. `L = c₀ Λ_d` with `c₀ ∈ ℚ`: `C_d` is the strong Weil curve. This is route A as before.
2. `Λ_d = k(1+i)L`: then `L' = ((1+i)/2) L = Λ_d/(2k)` is a period lattice of the 2-isogenous curve
   `E'_d : y² = x³ + 4d² x`, so `E'_d` is the strong Weil curve. gz-optimal's leaf already covers `E'_d`: it is
   stated for every short model with the L-function of `C_d`. The leaf gives the formula at `E'_d`. The explicit
   2-isogeny `φ : C_d → E'_d` carries the Heegner point and preserves torsion, which gives the formula at `C_d`.

`CdTwistedPeriodOdd` only decides which of the two curves is optimal, and the formula does not depend on that.

Proved in Lean along the way (all VERIFIED, standard axioms, `scratch/period-odd/out_axioms.txt`):

| theorem | content |
| --- | --- |
| `LFunction_ePrime_eq` | `L(E'_d, s) = L(C_d, s)` for Mathlib's L-function, odd squarefree `d` (every local factor) |
| `charSum_isog` | `Σ_x χ(x³ + ax) = Σ_X χ(X³ − 4aX)` over a finite field of odd characteristic, `a ≠ 0` |
| `isPeriodLattice_ePrime` | `((1+i)/2) L` is a period lattice of `E'_d` |
| `weierPt_ePrime_eq` | `φ(weierPt C_d L z) = weierPt E'_d L' z` for all `z ∈ ℂ` |
| `map_isogPt` | `φ` commutes with every `ℚ`-algebra map (it is defined over `ℚ`) |
| `periodLattice_ne_zero` | `Λ_f ≠ 0` for every weight-2 newform (any level and character) |
| `lattice_cases` | `Λ_d ⊆ L`, `Λ_d ≠ 0` ⇒ `L = c₀ Λ_d` or `L' = c Λ_d` (`c₀, c ∈ ℚ`) |
| `cd_or_ePrime_optimal` | from `EtaW32Character`: `C_d` or `E'_d` has period lattice `ℚ^× · Λ_f` |
| `core_isog` | the formula at `C_d` from the optimal leaf at `E'_d` |

## 1. The objects

* `C_d : y² = x³ − d² x` (`shortCurve (-(d:ℚ)^2)`), `d ≡ 5 (mod 8)` squarefree.
* `E'_d : y² = x³ + 4d² x` (`ePrime d := shortCurve (4 * d^2)`).
* `φ(x, y) = (x − d²/x, y(x² + d²)/x²)` for `x ≠ 0`, and `φ(0, 0) = φ(O) = O` (`isogPt`). This is the 2-isogeny
  with kernel `{O, (0, 0)}` (Silverman, AEC, III.4.5, UNVERIFIED).
* `L`: a period lattice of `C_d` (`g₂ = 4d²`, `g₃ = 0`). It is `ℤ[i] ω` (cd-optimal's Gaussian rounding).
* `L' = latP L = scalePP L ((1+i)/2)`, `h = (1+i) ω / 2`.
* `Λ_d = LamCd d`: the periods of gz-weil's Eichler integral `Φ_d` over `Γ₀(32d²)`. For the newform `f` of `C_d`
  it equals `periodLattice f` (cd-optimal).

## 2. The proof

### 2.1 `L(E'_d) = L(C_d)` (`PeriodOdd/LFunction.lean`)

For every place `v`, the local polynomials of `E'_d` and `C_d` agree (`localPolynomial_eLocal_eq`). Mathlib's
`LFunction` is the Euler product of these, so the L-functions are equal. By place:
* **`p ∤ 2d`.** Both curves have good reduction, and `#E'_d(𝔽_p) = #C_d(𝔽_p)` (`natCard_point_ePrime_zmod`).
  This follows from `charSum_isog`: with `X = x + a/x`,
  - `χ(x³ + ax) = χ(X)` for `x ≠ 0`;
  - each `X` has `1 + χ(X² − 4a)` preimages, counted via `u = 2x − X`;
  - so the sum is `Σ χ(X) + Σ χ(X³ − 4aX) = Σ χ(X³ − 4aX)`.
* **`p ∣ 2d`.** The model `y² = x³ + (2d)² x` is minimal with additive reduction, so the local polynomial is `1`,
  as for `C_d`. At odd `p ∣ d`, `v_p(Δ) = 6`. At `p = 2`, `v₂(Δ) = 12`. There minimality comes from `c₄ = −192 d²`
  (`v₂ = 6`): an integral model has `v₂(c₄) ∉ {1, 2, 3}`, by `HeckeAll/LocalCd.lean`'s `c₄_two_adic`, the same
  argument as for even `d` there.

### 2.2 The 2-isogeny analytically (`PeriodOdd/Isogeny.lean`)

1. **`L' = L ⊔ (h + L)`** (`latPEquiv`), with `h ∉ L`, from `L = ℤ[i] ω`. `λ(m + ni) ∈ ℤ[i]` iff `m ≡ n (mod 2)`.
2. **Splitting the series** (`weierstrassP_split`, `derivWeierstrassP_split`). Split Mathlib's `℘` over the two
   cosets. This holds for every `z`, junk values included:
   - `℘_{L'}(z) = ℘_L(z) + ℘_L(z − h) − ℘_L(−h)`;
   - `℘'_{L'}(z) = ℘'_L(z) + ℘'_L(z − h)`.
3. **`℘_L(h) = 0`.** First, `℘_L(iz) = −℘_L(z)` for `i`-stable `L` (`weierstrassP_I_mul`). Second, `ih = h − ω`.
4. **The group law** (Mathlib's `Affine.Point.add_some`, through gz-optimal's `weierPt_add'`):
   - `weierPt(z − h) = weierPt(z) + (0, 0)`;
   - so `℘_L(z − h) = −d²/x` and `℘'_L(z − h)/2 = d² y/x²` (with `x = ℘_L(z)`, `y = ℘'_L(z)/2`).
5. **Combining 2–4** gives `φ(weierPt C_d L z) = weierPt E'_d L' z` in three cases:
   - `z ∈ L`: both sides are `O`;
   - `z ∈ h + L`: both sides are `O`;
   - otherwise: field algebra with `y² = x³ − d² x`.
6. **`L'` is a period lattice of `E'_d`.** `g₂(λL) = λ⁻⁴ g₂(L)` with `λ⁴ = −1/4`, so `g₂(L') = −16 d² = c₄(E'_d)/12`,
   and `g₃(L') = 0`.

Numerical check of 2–5 for `d = 5` (PARI, `scratch/period-odd/isog_check.gp`): residuals `< 10⁻¹²` (VERIFIED).

### 2.3 `Λ_f ≠ 0` (`PeriodOdd/NeZero.lean`)

Suppose every period of a newform `f` vanishes. Then `φ_f` is `Γ₀(N)`-invariant. It is a weight-0 modular form
for `Γ₀(N)`:
- it is holomorphic (gz-heegner's `mdiff_eichler`);
- it is bounded at every cusp `γ∞`: gz-heegner's `exists_const_eichler` gives `φ_f(γτ) = K₀ + Σ_{m≥1} b_m q_N^m`,
  and this is analytic at `q_N = 0` (`analyticAt_Gser`).

Mathlib's `ModularForm.eq_const_of_weight_zero` then makes `φ_f` constant. So `f = D φ_f = 0` (`D_eichler`),
which contradicts `f ≠ 0`. This was needed because `CdTwistedPeriodOdd` had been the only source of a nonzero
period, and nothing in the tree proved `Λ_f ≠ 0`.

### 2.4 Classification and transfer (`PeriodOdd.lean`)

* **`lattice_cases`.** Write `L = ℤ[i] ω` and `Λ_d = ℤ[i] μ` (shortest vectors), with `μ = (p + qi) ω`.
  Conjugation stability forces `q = 0`, `p = 0` or `p = ±q` (cd-optimal's `gauss_conj_cases`):
  - `μ = kω` or `kiω`: then `L = (1/k) Λ_d` (`lattice_eq_of_mu`). This needs no oddness: `k` even is allowed.
  - `μ = p(1 ± i)ω`: then `L' = (1/(2p)) Λ_d` (`latP_eq_of_mu`).
* **`core_isog`.** Let `c Λ_f ⊆ L ⊆ L' = c' Λ_f`. Then `n = c/c' ∈ ℤ` (gz-optimal's `rat_mem_int`). Put
  `P' = φ(y) ∈ E'_d(K)`. Then `ι(P') = φ(ι y) = weierPt E'_d L' (n c' u) = n · y_K(φ_opt)`.
  - gz-optimal's leaf at `E'_d` (optimal parametrization `weierPt E'_d L' (c' φ_f)`) gives
    `(FG)'(1) = κ' ĥ(P')`.
  - `y` and `P'` are torsion together, because `L ⊆ L'` and `2L' ⊆ L` (gz-optimal's `isOfFinAddOrder_iff`).
  - So `(FG)'(1) = κ ĥ(y)` (`exists_pos_of_torsion_iff`).
* **`grossZagierFormulaCd_of_etaW32`.** Case 1 is gz-optimal's `core_selfOptimal`. Case 2 is `core_isog`.

## 3. Leaves and ratings

No new leaf. The discharge uses:

| Statement | Kind | Rating |
| --- | --- | --- |
| `GZOptimal.GrossZagierModuliOptCd` | published | **LEAF, printed form**, as rated by gz-optimal: Gross–Zagier 1986, Thm I.6.3 and Ch. V Thm 2.1, strong Weil parametrization, constant forgotten (weaker than the print). Used here at `C_d` and at `E'_d`. Both are short models with the L-function of `C_d`, which the leaf's statement covers; in each case the parametrization used is the optimal one. |
| `CdOpt.EtaW32Character` | published | **LEAF, printed form**, as rated by cd-optimal: an instance of the Newman / Gordon–Hughes eta-quotient transformation law (Ono, *Web of modularity*, Thm 1.64; UNVERIFIED locator). |

## 4. `CdTwistedPeriodOdd` itself (not needed; still open)

The statement is unchanged and unproved. With this note it has no consumer on the route to the headline theorem.

**What it is.** Given `lattice_cases`, `CdTwistedPeriodOdd(d)` says that the first case holds with `k` odd:
`Λ_d = kL` or `kiL`. So `C_d`, not `E'_d`, is `X₀(32d²)`-optimal, up to an odd factor. cd-optimal checked it
numerically for every squarefree `d ≡ 5 (mod 8)` up to 301, using a mod-2 reduction to level 32.

**Status.** No general proof was found (SPECULATIVE assessment, as in cd-optimal §4). The level-32 classes of
periods modulo `(1+i)L₁` form a non-congruence character, so no cusp or eta-quotient computation decides it.

**Smallest named form** (cd-optimal §4, derivation, not formalized): for every such `d`, some `γ ∈ Γ₀(32d²)` has
`Σ_{e ∣ d} ρ(diag(e²,1) γ diag(e²,1)⁻¹) ∉ (1+i) L₁`. Here `ρ` is the period homomorphism of `f₁` (level 32) and `L₁`
is a lattice of `y² = x³ − x`. Rating: **GLUE, not printed** (SPECULATIVE). A possible proof for prime `d`: an
Ihara-type argument with the congruence subgroup property of `SL₂(ℤ[1/p])` (Serre 1970), plus a proof that the
level-32 parity character is non-congruence (Wohlfahrt's level theorem and one Manin-symbol computation in
`Γ(32)`). Both are unformalized, and the composite case is open.

**`CdOptimal`** (gz-optimal's glue: `C_d` itself is optimal, `L = c₀ Λ_f`) is not proved either and is not needed.
The weaker, unconditional replacement is `cd_or_ePrime_optimal`, proved from `EtaW32Character`: `C_d` or `E'_d` is
optimal.

## 5. Checks

| File | Content | Check |
| --- | --- | --- |
| `ZInQKernel/Contrib/OneProof/PeriodOdd/LFunction.lean` | `charSum_isog`, model `y² = x³ + (2d)² x`, minimality and reduction types, `LFunction_ePrime_eq` | `lake build` (VERIFIED) |
| `ZInQKernel/Contrib/OneProof/PeriodOdd/Isogeny.lean` | `℘` splitting, `℘(iz) = −℘(z)`, `L' = L ⊔ (h+L)`, `isogPt`, `map_isogPt`, `isPeriodLattice_ePrime`, `weierPt_ePrime_eq` | `lake build` (VERIFIED) |
| `ZInQKernel/Contrib/OneProof/PeriodOdd/NeZero.lean` | `periodLattice_ne_zero` | `lake build` (VERIFIED) |
| `ZInQKernel/Contrib/OneProof/PeriodOdd.lean` | `lattice_cases`, `core_isog`, `cd_or_ePrime_optimal`, **`grossZagierFormulaCd_of_etaW32`** | `lake build` (VERIFIED) |
| `scratch/period-odd/AxMain.lean`, `out_axioms.txt` | `#print axioms` for the six main theorems | `[propext, Classical.choice, Quot.sound]` (VERIFIED) |
| `scratch/period-odd/MainEdit.lean`, `out_mainedit.txt` | `frozenTarget_periododd`: `ZInQ.FrozenTarget` with `hL3` replaced by the two leaves | standard axioms (VERIFIED) |
| `scratch/period-odd/Discharges.lean`, `discharges-output.txt` | `#discharges` | below |
| `scratch/period-odd/autofold.json` | spec for the field `grossZagierFormulaCd` | dry run: see below |
| `scratch/period-odd/isog_check.gp` | numerical check of §2.2 | VERIFIED |

**Build.** `lake build ZInQKernel.Contrib.OneProof.PeriodOdd`. The build tree was copied from
the cd-optimal worktree, which is the same commit. Each new file elaborates in under 10 s, and `lake env lean` on each
file shows no warnings.

**`#discharges`** (`scratch/period-odd/discharges-output.txt`, VERIFIED):
- command: `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.PeriodOdd`,
  then `lake env lean scratch/period-odd/Discharges.lean`;
- result: `61 open hypotheses, 3247 theorems checked, 9 discharge one`. These are the same 9 `DISCHARGES` lines as in
  cd-optimal's run.
- None is by a period-odd theorem. As for cd-optimal, the discharged field `grossZagierFormulaCd` exists only after
  `hL3` (`GZDecomp.GrossZagierHeegner`, for every `E`) is split into its `C_d` chain (heegner-32 + gz-conj); the
  Main edit is `scratch/period-odd/MainEdit.lean`.

**autofold.** `scratch/period-odd/autofold.json`:
- field: `grossZagierFormulaCd`;
- proof: `ZInQ.PeriodOdd.grossZagierFormulaCd_of_etaW32 {n}.grossZagierModuliOptCd {n}.etaW32Character`;
- leaves: `grossZagierModuliOptCd` and `etaW32Character`, both kind `published` with flag `""`, entries copied from
  cd-optimal.

It replaces cd-optimal's `autofold-formula.json`: the same field with one leaf fewer, and the GLUE count does not
rise. `autofold.py --dry-run` stops with `not a field of the current bundles: ['grossZagierFormulaCd']`, as expected
until the `C_d` split is folded; cd-optimal's spec stops the same way.

## 6. Remaining

* Folding: the `C_d` split of `hL3` (gz-optimal, heegner-32, gz-conj) has to land before this spec applies.
* `CdTwistedPeriodOdd` and `CdOptimal` stay open (§4). Nothing on the route to the headline theorem needs them.
