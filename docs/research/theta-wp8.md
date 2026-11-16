# theta-wp8: `X0EtaRoute.ThetaWeierstrass8` proved; Theorem 1.1 without `hX`

Task theta-wp8 (2026-11-15). Base: wip/hx-used `4bdc3ad1`, with wip/jacobi-lambda `b6fc38e9` and
wip/gz-heegner `58a780e4` merged in (both merges clean). Scratch and log: `scratch/theta-wp8/`.

## 0. Results

1. **`X0EtaRoute.ThetaWeierstrass8` is proved outright** (VERIFIED, compiled; standard axioms; no new hypotheses).
   - Theorem: `ThetaWP8.thetaWeierstrass8 : X0EtaRoute.ThetaWeierstrass8`.
   - File: `ZInQKernel/Contrib/OneProof/ThetaWeierstrass8.lean` (new, 907 lines). It imports
     `ZInQKernel.Contrib.OneProof.X0ModuliUsed`, not `ZInQKernel.OneProof.Main`.
   - The statement is unchanged: for every `w ∈ ℍ`,
     `θ(0; w) / (e^{πiw/4} θ(w/2; w)) = 1 − 2(℘(1/2) − ℘(1/2 + w/8))/(℘(3w/8) − ℘(1/2 + w/8))`,
     with `℘ = ℘_{⟨1, w⟩}` and Mathlib's `jacobiTheta₂`.
   - Inputs: Mathlib, and the kernel's Jacobi triple product `ZInQ.GZTheta.jacobiTheta₂_eq_jtpP` (gz-theta).
     Nothing from jacobi-lambda was needed.
2. **The top hypothesis `hX` is removed, with nothing in its place** (VERIFIED, compiled; standard axioms).
   - `ThetaWP8.frozenTarget_noHX` has the binders of `ZInQ.OneProof.frozenTarget` minus `hX`:
     `(r t l g h11 h29 hCM h33 hFH hL3) : ZInQ.FrozenTarget`.
   - `ThetaWP8.tyzThm35ReadingA_noHX (h11 h29 hCM h33) : ZInQ.Literature.TYZThm35ReadingA`.
   - Also proved: `ThetaWP8.xEtaWeierstrass : X0EtaRoute.XEtaWeierstrass`.
   - Effect on the counts: hx-used's recommended fold replaced `hX` with `hT : ThetaWeierstrass8` (GLUE, strict count
     1 → 1). With `hT` proved, the row goes away and nothing is added: **−1 GLUE**, and no new leaf.
3. **gz-heegner's `X0ModuliGaloisMero` is not used at level 32, so the eta route does not cover it** (VERIFIED: read,
   and computed with PARI; §4).
   - It is used at the level `N` of the newform of the curve, for the coordinates `x(φ)`, `y(φ)` of that curve's
     modular parametrization.
   - For the `C_d` form (`HeegnerPointRationalCd`, `d ≡ 5 (mod 8)` squarefree), that level is `N = 32d² ≥ 800`.
   - So the hL3 fold still needs `X0ModuliGaloisMero` (or another argument; §4.3). No rerouting is given.

## 1. `#discharges` and axioms (VERIFIED, `scratch/theta-wp8/discharges-output.txt`)

```
lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ThetaWeierstrass8
  → Build completed successfully (12997 jobs)
#discharges: 63 open hypotheses, 2103 theorems checked, 7 discharge one
'ThetaWP8.core' depends on axioms: [propext, Classical.choice, Quot.sound]
'ThetaWP8.thetaWeierstrass8' depends on axioms: [propext, Classical.choice, Quot.sound]
'ThetaWP8.xEtaWeierstrass' depends on axioms: [propext, Classical.choice, Quot.sound]
'ThetaWP8.tyzThm35ReadingA_noHX' depends on axioms: [propext, Classical.choice, Quot.sound]
'ThetaWP8.frozenTarget_noHX' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- The 7 discharges are the pre-existing ones (the same list as hx-used §0.2).
- None is from this file. That is expected: `hX` is a plain argument of `frozenTarget`, not a bundle field, so
  `#discharges` cannot see its removal.
- The check that matters: `frozenTarget_noHX` compiles with exactly the other binders. I compared them with
  `ZInQKernel/OneProof/Main.lean` l. 60–66 (read).
- The file has no `#eval`, `run_cmd`, `initialize`, `syntax`, `notation` or macros.

## 2. The fold (manual; `autofold.py` does not apply)

`scratch/theta-wp8/autofold.json` records this in its `note`. Its `discharges` entry (`field: "hT"`) applies only
if a later fold makes `hT` a bundle field. At base `43513d87`, the edit of `ZInQKernel/OneProof/Main.lean` is:

- **Import:** add `import ZInQKernel.Contrib.OneProof.ThetaWeierstrass8`.
- **Binder:** delete `(hX : _root_.T5Glue.X0ModuliGalois)` (l. 64).
- **Term (l. 70):** replace
  `(tyzThm35ReadingA_of_leaves h11 h29 (_root_.T5Glue.shimuraReciprocityModFn_of_printed hCM hX) (ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33 h33))`
  with `(ThetaWP8.tyzThm35ReadingA_noHX h11 h29 hCM h33)`.
- **Check:** the result is `ThetaWP8.frozenTarget_noHX`, which compiles (VERIFIED).
- **kinds.tsv:** delete the row of `hX` (consequence, GLUE). Add no row.
- **Main.lean docstring:** "the third, Shimura reciprocity for modular functions, from the two printed leaves…"
  becomes "from `ShimuraMainCM` alone (the level-32 instances, by the eta route with the proved identity
  `ThetaWeierstrass8`; `ThetaWP8.tyzThm35ReadingA_noHX`)".

If the integrator has already applied hx-used's fold (`hT` as an argument), the edit is the same: delete `hT` and use
`ThetaWP8.tyzThm35ReadingA_noHX`.

## 3. The proof

**Notation.**
- `ϑ(z) = jacobiTheta₂ z w`.
- `s(z) = ϑ(z + (1+w)/2)` (`sF`), the odd-type theta function. Its zero set is exactly `Λ = ℤ + ℤw`.
- `c = 1/2 + w/8`. The identity's ratio is `(℘(a) − ℘(c))/(℘(b) − ℘(c))` with `a = 1/2`, `b = 3w/8`.

**A. Theta facts** (from the triple product).
- `sF_add_one`, `sF_add_w`: the exact quasi-periods `s(z+1) = s(z)` and `s(z+w) = e^{−πi(2w+2z+1)} s(z)`.
- `sF_eq_factor`: `s(y) = (1 − e(−y))·G(y)`. Here `G = A·B(y + (1+w)/2)·B(−y + (1+w)/2)` in gz-theta's
  notation, and `G(0) = A³ ≠ 0`. It comes from gz-theta's `jtpB_neg_sub_tau`.
- `sF_ne_zero`: `s(y) ≠ 0` for `y ∉ Λ`. If a factor of the product vanishes, then `y ∈ Λ`
  (`tprod_one_add_ne_zero_of_summable`).
- `sF_lat`: `s` vanishes on `Λ`.
- `sF_simple`: the zeros are simple. For each `l ∈ Λ`, `s(z) = (z − l)g(z)` with `g` entire and `g(l) ≠ 0`. The
  proof uses `s'(0) = 2πi A³` and quasi-periodicity along `Λ` (`sF_add_lat`).

**B. Removable singularities and Liouville** (generic).
- `reg h x := limUnder (𝓝[≠] x) h`. If `h` agrees on a punctured neighbourhood with a `g` analytic at `x`, then
  `reg h = g` near `x` (`reg_eventuallyEq`).
- `reg` keeps the exact periods of `h` (`reg_add_period`).
- A continuous function with periods `1` and `w` is bounded: reduce to the compact parallelogram
  (`isBounded_range_of_periodic`).

**C. The elliptic function**
`h(u) = (℘(u) − ℘(c))·s(u)²/(s(u − c)s(u + c))` (`hF`), for `c, 2c ∉ Λ`.
- It is exactly 1- and `w`-periodic (`hF_add_one`, `hF_add_w`). The exponential factors cancel, since
  `2(2u) = (2u − 2c) + (2u + 2c)`.
- `hF_local` gives an analytic representative at every point:
  - at `x ∈ Λ`: the double pole of `℘` cancels against `s(u)² = (u − x)²g(u)²`. Mathlib's `weierstrassPExcept_add`
    supplies the pole; the value at `0` is `g(0)²/(s(−c)s(c)) ≠ 0`;
  - at `x ∈ ±c + Λ`: `℘(u) − ℘(c) = (u − x)·dslope ℘ x u` cancels the simple zero of `s(u ∓ c)`;
  - elsewhere, `h` is already analytic.
- Then `reg h` is entire, doubly periodic and bounded, so it is constant by Liouville
  (`Differentiable.apply_eq_apply_of_bounded`). Hence `h ≡ K ≠ 0` off its singular set (`hF_const`).
- This is the classical `℘(u) − ℘(v) = −σ(u−v)σ(u+v)/(σ(u)²σ(v)²)` up to a constant. The constant cancels in the
  ratio, so neither Jacobi's derivative formula nor `σ` is needed.

**D. Theta values.**
- The ratio equals `s(a−c)s(a+c)s(b)²/(s(a)²s(b−c)s(b+c))`.
- Quasi-periodicity turns it into six theta values:
  - `u₃ = ϑ(1/2 + 3w/8)` and `u₁ = ϑ(1/2 + w/8)`;
  - `t₀ = ϑ(0)`, `t₂ = ϑ(w/2)` and `t₄ = ϑ(w/4)`;
  - powers of `Q = e^{πiw/8}`.
- The identity becomes `t₂ t₄ t₀ (t₀ − Q² t₂) = 2 u₃² u₁²`.
- `theta4_quarter` gives `t₀ − Q²t₂ = θ₄(w/4)`, by splitting the series of `jacobiTheta₂ (1/2) (w/4)` into even
  and odd indices.
- The triple product at base `Q`, steps 16 and 32 (`theta_gp`, `val_*`), turns every factor into products
  `∏(1 ± Q^{16n+k})`.
- The products cancel by `(1+x)(1−x) = 1−x²` (`gp_pm`), the even/odd split (`gp_even_mul_odd`) and Euler's identity
  `∏(1 − x^{2n+1})∏(1 + x^{n+1}) = 1` (`euler16`). This gives `prod_identity`.

**E. Assembly.**
- `core` holds for any `PeriodPair` with `ω₁ = 1` and `ω₂ = w`.
- `thetaWeierstrass8` is `core (T5Glue.pp w) w.im_pos rfl rfl`.
- The eight non-lattice conditions are `not_inLat` instances. They compare imaginary parts, then real parts.

**Numerics** (VERIFIED, `scratch/theta-wp8/num/check.py`, 40 digits, 4 random `w`):
- every step of the chain agrees to about `1e-39`: the identity, the ratio = theta quotient, the six-value form, and
  the constancy of `h` at 3 random `u`;
- `θ₄(w/4) = θ₃ − θ₂` also holds numerically.

## 4. gz-heegner's `X0ModuliGaloisMero`: not at level 32

### 4.1 Where it is used (VERIFIED, read: `GrossZagierHeegner/Heegner.lean` l. 1033–1123, `HeegnerCd.lean`)

- `heegnerC_fixed` applies `hX N hN g hg σ Q.tauH Q'.tauH μ …` inside `point_transport`.
- There `N` is the level of the newform `f` with `aₙ(f) = aₙ(E)` (the binder of `HeegnerPointRationalAt`), and `g`
  ranges over the coordinates `xPar`, `yPar` of `τ ↦ weierPt E L (c·φ_f(τ))`.
- `HeegnerCd.lean` restricts this to `E = C_d : y² = x³ − d²x` with `d ≡ 5 (mod 8)` squarefree
  (`HeegnerPointRationalCd`).

### 4.2 The level is `32d²`, never 32

- The conductor of `C_d` is `32d²` (VERIFIED by PARI `ellglobalred`, `scratch/theta-wp8/num/conductor.py`):
  - d = 5: 800; d = 13: 5408; d = 21: 14112; d = 29: 26912; d = 37: 43808; d = 53: 89888.
- A newform whose coefficients are those of `E` has level equal to the conductor of `E` (STANDARD: Carayol, and
  strong multiplicity one; theorem numbers UNVERIFIED).
- Directly at level 32: the only newform there is that of `C_1`, and `a_p(C_d) = (d/p)·a_p(C_1)` (VERIFIED by PARI):
  - d = 5, p = 13: `a_13(C_1) = 6`, `a_13(C_5) = −6`;
  - d = 13, p = 5: `a_5(C_1) = −2`, `a_5(C_13) = 2`.
- So no instance with `N = 32` is ever used for `C_d`.
- The functions are also different: `x(φ_f)`, `y(φ_f)` on `X₀(32d²)`, not x0-32's eta quotients `x`, `y`.
- The eta route proves the level-32 instances `ShimuraReciprocityModFnAt 32 x`, `… y`. Those cover CM points of every
  conductor (`TData m f D`, `D = discOf m f`; read), but only on `X₀(32)`.
- Conclusion: **the hL3 fold keeps `X0ModuliGaloisMero`**. Its gz-heegner rating (printed form: canonical model of
  `X₀(N)`, Shimura 1971 §6.7, UNVERIFIED numbers) is unchanged by this task.

### 4.3 A possible alternative (SPECULATIVE, not attempted)

- Heegner points on `C_d` could instead be built from `X₀(32) ≅ C_1` and CM points of conductor divisible by `d`,
  traced against the quadratic character of `ℚ(√d)`. This is the construction of Tian's congruent-number papers;
  the details are from memory and UNVERIFIED.
- Then only level-32 reciprocity is needed, and the eta route covers that.
- But the Gross–Zagier leaf `hL3` is stated for the level-`32d²` Heegner points. Switching constructions would need a
  different GZ/Waldspurger leaf. That is a redesign of the GZ side, not a rerouting.

## 5. New leaves and their ratings

**None.** The proof uses no new hypothesis: every step is proved in Lean. So there is no printed-form rating to give,
and no `locators.md` row to add.

| Prop | before | after |
|---|---|---|
| `X0EtaRoute.ThetaWeierstrass8` | GLUE (hx-used; no printed source) | **proved** (`ThetaWP8.thetaWeierstrass8`) |
| `X0EtaRoute.XEtaWeierstrass` | GLUE, equivalent form | **proved** (`ThetaWP8.xEtaWeierstrass`) |
| `hX = T5Glue.X0ModuliGalois` on the frozenTarget route | consequence, GLUE | **removed** (`frozenTarget_noHX`) |

## 6. Files

- **New in the kernel:** `ZInQKernel/Contrib/OneProof/ThetaWeierstrass8.lean`. Nothing else under `ZInQKernel/` was
  edited.
- **`scratch/theta-wp8/`:**
  - `ThetaZeros.lean`: the development file, the same proof with lighter imports;
  - `Discharges.lean` and `discharges-output.txt`;
  - `autofold.json`;
  - `num/`: the numerical checks and the PARI conductor check;
  - `build_*.txt`: build logs;
  - `log.md`.
