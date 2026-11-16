# jacobi-lambda: Jacobi's derivative formula `dλ/dt = πi λ θ₄⁴` proved in Lean (gz-weil's last parametrization leaf removed)

Status: research note (task jacobi-lambda, 2026-11-15), branch `wip/jacobi-lambda` (base f4a06a48 = gz-weil).
Lean: one new contributor file `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/JacobiLambdaDeriv.lean` (681
lines, 53 lemmas and theorems, about 32 KB). Nothing else under `ZInQKernel/` was edited. Development files,
checks and log: `scratch/jacobi-lambda/`.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published theorem with
an exact reference. **SPECULATIVE**: an assessment.

---

## 0. Main result

**gz-weil's printed leaf `ZInQ.GZWeil.JacobiLambdaDeriv` is now a Lean theorem.** It is proved from Mathlib's
`jacobiTheta₂` and one bound from gz-theta's `TripleProduct.lean`, with no new leaf. VERIFIED, compiled, with
axioms `[propext, Classical.choice, Quot.sound]`:

```lean
-- ZInQKernel/Contrib/OneProof/GrossZagierHeegner/JacobiLambdaDeriv.lean
theorem ZInQ.GZWeil.jacobiLambdaDeriv : ZInQ.GZWeil.JacobiLambdaDeriv

-- the statement (gz-weil, WeilTheta.lean), unchanged:
def ZInQ.GZWeil.JacobiLambdaDeriv : Prop :=
  ∀ t : ℂ, 0 < t.im → HasDerivAt (fun s => thetaTwo s ^ 4 / thetaThree s ^ 4)
    (π * I * (thetaTwo t ^ 4 / thetaThree t ^ 4) * thetaFour t ^ 4) t
```

Here `thetaTwo t = e^{πit/4} jacobiTheta₂ (t/2) t`, `thetaThree t = jacobiTheta₂ 0 t` and
`thetaFour t = jacobiTheta₂ (1/2) t`.

As a result, these become unconditional theorems in the same file (VERIFIED, standard axioms;
`scratch/jacobi-lambda/out_check.txt`):

| theorem | type | before (gz-weil) |
| --- | --- | --- |
| `ZInQ.GZWeil.etaModelDifferential` | `ZInQ.Contrib.TYZGenus.X0.EtaModelDifferential` (x0-32's `x' = 4πi f₁ y`) | from `JacobiLambdaDeriv` |
| `ZInQ.GZWeil.modularParamC1` | `ZInQ.GZWeil.ModularParamC1` | from `JacobiLambdaDeriv` |
| `ZInQ.GZWeil.shimuraCMParamCd` | `ZInQ.GZHL3.ShimuraCMParamCd` (analytic modular parametrization of every `C_d`) | from `JacobiLambdaDeriv` |
| `ZInQ.GZWeil.grossZagierHeegnerCd_of_leaves4` | `WeierstrassUniformization → HeegnerPointRationalCd → GrossZagierFormulaCd → GrossConjugationCd → GZStatements.GrossZagierHeegnerCd` | 5 leaves (with `JacobiLambdaDeriv`) |

**The leaf count on the `C_d` route of `hL3`.** gz-weil's split had five leaves: `WeierstrassUniformization`
(printed), `JacobiLambdaDeriv` (printed), `HeegnerPointRationalCd` (composite), `GrossZagierFormulaCd` (printed)
and `GrossConjugationCd` (printed). Now it has four; the one composite is unchanged. The modular
parametrization of `C_d` (gz-hl3's `ShimuraCMParamCd`, whose general form needed Eichler–Shimura with a
rational Manin constant and Faltings' isogeny theorem) now rests on **no leaf at all**.

**No new leaves.** The proof introduces no `def … : Prop`; there is nothing to rate.

---

## 1. What exists (VERIFIED, read)

* **Mathlib v4.35.0.** `jacobiTheta₂` (`NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean`) has periodicity
  and quasi-periodicity (`jacobiTheta₂_add_left`, `jacobiTheta₂_add_left'`), parity (`jacobiTheta₂_neg_left`),
  analyticity (`hasFDerivAt_jacobiTheta₂`, `differentiableAt_jacobiTheta₂_snd`), the functional equation, and
  `norm_jacobiTheta_sub_one_le` (`OneVariable.lean`). It has **no identities between theta constants**: no
  Jacobi quartic, no Landen or duplication formula, no `θ₁' = πθ₂θ₃θ₄`. For modular forms, Mathlib has the
  level-one dimension formula and Ramanujan's `E₂, E₄, E₆` derivative formulas (`RamanujanFormula.lean`), but
  **no modular forms for `Γ(2)` or `Γ₀(4)` and no dimension formula beyond level one**. So the
  Hauptmodul / dimension-count route the task suggests would need a theory of `Γ(2)` first.
* **Kernel.** gz-theta's Jacobi triple product (`ZInQ.GZTheta.jacobiTheta₂_eq_jtpP`) and its theta bounds;
  tyz-cm's and gz-weil's product forms at `16τ`. The kernel has no four-square (`r₄`) identity: the files named
  `FourSquares` are Lagrange's existence theorem for the compiler.

**Route chosen: the Landen recursion.** It is entirely elementary: one series rearrangement, then algebra,
Cauchy's estimate, and an iteration `τ ↦ 2τ`. It needs neither the triple product nor modular forms.

---

## 2. The proof (all VERIFIED, compiled; Lean names in `ZInQ.JacobiLambda`)

1. **Duplication formula** (`jacobiTheta₂_mul_jacobiTheta₂`): for `Im τ > 0` and all `z, w`,
   `θ(z,τ)θ(w,τ) = θ(z+w,2τ)θ(z−w,2τ) + e^{2πiz+πiτ} θ(z+w+τ,2τ)θ(z−w+τ,2τ)`.
   It comes from the bijection `ℤ² ⊔ ℤ² → ℤ²`, `(a,b) ↦ (a+b, a−b)`, `(a,b) ↦ (a+b+1, a−b)` (`dupMap_bijective`),
   applied to the absolutely convergent double series (Mathlib's `tsum_mul_tsum_of_summable_norm`,
   `HasSum.sum`, `Equiv.hasSum_iff`). It was also checked numerically at three points to `10⁻¹⁴`
   (`scratch/jacobi-lambda/dup_check.py`).
2. **Landen's identities**, as specializations at `z, w ∈ {0, 1/2, τ/2}`:
   `θ₃(τ)² = θ₃(2τ)² + θ₂(2τ)²` (`landen_three`), `θ₄(τ)² = θ₃(2τ)² − θ₂(2τ)²` (`landen_four`),
   `θ₂(τ)² = 2θ₂(2τ)θ₃(2τ)` (`landen_two`) and `θ₃(τ)θ₄(τ) = θ₄(2τ)²` (`landen_three_four`). The last uses
   `θ(τ + 1/2, 2τ) = 0`. Together they give **Jacobi's quartic identity** `θ₃⁴ = θ₂⁴ + θ₄⁴` on `ℍ`
   (`jacobi_quartic`).
3. **Exponential bounds** for `Im s ≥ 1`: `‖T(s) − 2‖, ‖θ₃(s) − 1‖, ‖θ₄(s) − 1‖ ≤ 3e^{−π Im s}`, where
   `θ₂ = e^{πis/4} T` and `T(s) = jacobiTheta₂ (s/2) s = Σ e^{πin(n+1)s}`. The bound on `T` pairs `n` with
   `−1−n`. The `θ₃` bound is Mathlib's; the `θ₄` bound is gz-theta's `norm_jacobiTheta₂_half_sub_one_le`.
4. **Nonvanishing** of `θ₂, θ₃, θ₄` on `ℍ` (`thetaFour_ne_zero`, `thetaThree_ne_zero`, `thT_ne_zero`,
   `thetaTwo_ne_zero`). By Landen, a zero at `τ` gives a zero at `2τ`, hence at `2^k τ` with `Im ≥ 1`, where the
   bounds of step 3 rule it out (`not_of_iterate`). No infinite products are used.
5. **Landen recursion** (`Fq_rec`). Put `h = θ₂/θ₃` and `F = h'/h − (πi/4)θ₄⁴`. Landen gives
   `h(τ)²(1 + h(2τ)²) = 2h(2τ)` on `ℍ` (`hq_rel`). Differentiating this, with the quartic identity at `2τ`,
   gives `F(τ) = (θ₄(τ)²/θ₃(τ)²) F(2τ)`.
6. **Decay** (`norm_Fq_le`): `‖F(σ)‖ ≤ C e^{−π Im σ}` for `Im σ ≥ 2`, with `C = 15e^π + 12π`. Here
   `h'/h = πi/4 + T'/T − θ₃'/θ₃` (`logDeriv_hq`), and `T'` and `θ₃'` are bounded by Cauchy's estimate on the
   unit circle (`norm_deriv_le_of_bound`, from Mathlib's `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`).
7. **`F = 0`.** For `Im σ ≥ 43`: `‖θ₄²/θ₃²‖ ≤ 64`, `e^{−π Im 2σ} = (e^{−π Im σ})²` and
   `64e^{−π Im σ} ≤ 1/2`. So by induction `‖F(σ)‖ ≤ C e^{−π Im σ} 2^{−k}` for every `k`, hence `F(σ) = 0`
   (`Fq_eq_zero_of_large`). For general `τ ∈ ℍ`, a nonzero `F(τ)` would give a nonzero `F(2^k τ)` by step 5
   (`Fq_eq_zero`).
8. **Conclusion** (`jacobiLambdaDeriv'`): `λ = h⁴`, so `λ' = 4h³h' = πi h⁴ θ₄⁴`.

The proof uses Mathlib and one kernel lemma (gz-theta's `norm_jacobiTheta₂_half_sub_one_le`, standard axioms).
Byproducts that other tasks may reuse: the duplication formula, Landen's identities, Jacobi's quartic identity,
and nonvanishing of the theta constants on `ℍ`, all over Mathlib's `jacobiTheta₂`.

---

## 3. Statement checks (VERIFIED)

* **Verbatim.** `scratch/jacobi-lambda/Check.lean` copies `JacobiLambdaDeriv` and its three definitions
  verbatim from `WeilTheta.lean` into a fresh namespace. It proves `JLCopy.JacobiLambdaDeriv ↔
  ZInQ.GZWeil.JacobiLambdaDeriv` by `Iff.rfl`, and proves the copy from the new theorem. The theorem itself has
  type exactly `ZInQ.GZWeil.JacobiLambdaDeriv` (`#check`).
* **Axioms** (`out_check.txt`): `jacobiLambdaDeriv`, `etaModelDifferential`, `modularParamC1`,
  `shimuraCMParamCd` and `grossZagierHeegnerCd_of_leaves4` depend on `[propext, Classical.choice, Quot.sound]`.
* **Not vacuous.** The statement asserts a derivative at every point of `ℍ`. gz-weil uses it at `t = 16τ`, and
  the proof here is a real proof of that statement, not a consequence of a false hypothesis.

---

## 4. Integration

* **Contributor file**: `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/JacobiLambdaDeriv.lean`, next to
  gz-weil's files. It imports `ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilTheta` (the module that
  defines the statement), `Mathlib.Analysis.Real.Pi.Bounds` and `Mathlib.Analysis.Complex.Liouville`; it never
  imports `OneProof.Main`, and it has no build-time code (`#eval`, macros, notation).
  `lake build ZInQKernel.Contrib.OneProof.GrossZagierHeegner.JacobiLambdaDeriv` succeeds (11342 jobs, no
  warnings in the file).
* **`#discharges`** (`scratch/jacobi-lambda/Discharges.lean` → `discharges-output.txt`): 65 open hypotheses,
  1526 theorems checked, 6 discharge one. These are the same six as at the base. The new theorems discharge no
  open hypothesis directly, as gz-weil already explained: `JacobiLambdaDeriv` is not a field of the current
  bundles, and `hL3` is stated for all elliptic curves, while this chain covers `C_d`.
* **Autofold spec** (`scratch/jacobi-lambda/autofold.json`): field `jacobiLambdaDeriv`, proof
  `_root_.ZInQ.GZWeil.jacobiLambdaDeriv`, no leaves. The dry run at this base stops with
  `not a field of the current bundles: ['jacobiLambdaDeriv']` (`autofold-dryrun.txt`), as expected. The spec
  applies once gz-weil's leaves are folded under that field name.
* **`Main.lean` edit, checked out of tree** (`scratch/jacobi-lambda/MainEdit.lean` → `out_mainedit.txt`):
  `ZInQ.Contrib.TYZChain.frozenTarget_jacobiLambda` proves `ZInQ.FrozenTarget` from `frozenTarget`'s open
  hypotheses with `hL3` replaced by **four** leaves: `WeierstrassUniformization`, `HeegnerPointRationalCd`,
  `GrossZagierFormulaCd` and `GrossConjugationCd`. Axioms are standard. It is gz-weil's `frozenTarget_gzweil'`
  with `hD := ZInQ.GZWeil.etaModelDifferential`. For `kinds.tsv`, gz-weil's proposed `JacobiLambdaDeriv` row is
  not needed. No `locators.md` row is needed either: the leaf is gone.

---

## 5. What remains

* On the `C_d` route of `hL3`: `WeierstrassUniformization` (printed), `HeegnerPointRationalCd` (composite;
  gz-hl3 §10 sketches a route), `GrossZagierFormulaCd` (printed, constant forgotten) and `GrossConjugationCd`
  (printed). None of them was in scope here.
* The integrator still has to replace `hL3` by the `C_d` chain in `Main.lean` (§4); `#discharges` cannot show
  it as a discharge of `hL3` itself.
