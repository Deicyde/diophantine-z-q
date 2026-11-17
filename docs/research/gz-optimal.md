# gz-optimal: the Gross–Zagier leaf for the strong Weil parametrization only

Status: research note (task gz-optimal, 2026-11-16), branch `wip/gz-optimal`. Base: wip/gz-moduli 85111fc7, with
origin/wip/heegner-32 (718d8d4c) and origin/wip/gz-conj (2c7ce521) merged; both merges were clean. Lean: new files
`ZInQKernel/Contrib/OneProof/GrossZagierOptimal.lean` and `ZInQKernel/Contrib/OneProof/GrossZagierOptimal/NonVacuous.lean`.
Nothing else under `ZInQKernel/` was edited. Scratch and log: `scratch/gz-optimal/`.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published theorem with an
exact reference. **SPECULATIVE**: an assessment. This host has no network and no copy of Gross–Zagier, Gross 1984,
Shimura 1971 or Silverman. **Every theorem number and locator of the literature below is UNVERIFIED** (from memory),
except the two Gross–Zagier page locators quoted from `docs/research/locators.md`.

---

## 0. Main result

1. **The new leaf `ZInQ.GZOptimal.GrossZagierModuliOptCd` is printed under either reading of Gross–Zagier.** It is
   gz-moduli's moduli form restricted to the **strong Weil (optimal) parametrization**. In `IsOptimalParam`, φ
   lifts to `c φ_f` and `L = c Λ_f`. Equivalently, `φ_* : H₁(X₀(N), ℤ) → H₁(E(ℂ), ℤ)` is onto, i.e. the map
   `J₀(N) → E` has connected kernel. It is proved weaker than gz-moduli's leaf (`grossZagierModuliOptCd_of_moduli`).
2. **The consumer `GZHL3.GrossZagierFormulaCd` (all admissible `φ = weierPt C_d L (c φ_f)`) is proved from it in
   Lean.** The new leaf cannot do this alone, because `C_d` need not be the strong Weil curve of its class. The
   kernel lacks a statement that identifies the optimal curve. Two variants of that statement are isolated, and both
   compile:
   - **Route A** (`grossZagierFormulaCd_of_selfOptimal`): the new leaf plus **`CdOptimal`**, a period computation
     (GLUE). It says `C_d` is its own strong Weil curve: `L(C_d) = c₀ Λ_f`. **Numerically `Λ_f = L(C_d)` (c₀ = 1)
     for all 18 values of d tested, d ≡ 5 (mod 8) squarefree between 5 and 165** (§4, VERIFIED, computed).
     Then every admissible φ is `[n] ∘ φ_opt`.
   - **Route B** (`grossZagierFormulaCd_of_transfer`): the new leaf plus **`StrongWeilOptimalCd`** (the strong Weil
     curve `E'` with `L(E') = c' Λ_f`) and **`AnalyticIsogenyRational`** (the isogeny `z ↦ μz`, μ ∈ ℚ, is defined
     over ℚ). Both are textbook statements, composite in today's Lean. Here `φ = ψ ∘ φ'`, and the formula
     transfers along `ψ̂ : C_d → E'` because `y` and `ψ̂(y)` are torsion together.
3. **`y_K`.** Gross–Zagier's `y_K = Σ_{σ ∈ Gal(H/K)} φ(x)^σ = Tr_{H/K} φ(x)` is the sum over a complete set of
   Heegner points with fixed `𝔫`, which is what gz-moduli uses (§2). **No fix is needed.**
4. **Counts.** The fold is **not a clean −1 today.**
   - Route A replaces the GLUE field `grossZagierFormulaCd` by one LEAF and one project-glue computation. That is
     neutral now, and **−1 once `CdOptimal` is a Lean theorem**.
   - Route B is +1 (two composite leaves).
   - gz-moduli's own leaf gives −1 if a statement check finds Gross–Zagier V.2.1 printed for every modular
     parametrization. In that case nothing here is needed, and the new leaf is a weaker printed statement.

The checks, all VERIFIED (compiled):
- every theorem uses only `[propext, Classical.choice, Quot.sound]` (`scratch/gz-optimal/Check.lean`, `out_check.txt`);
- `lake build ZInQKernel.Contrib.OneProof.GrossZagierOptimal.NonVacuous` succeeds;
- `scratch/gz-optimal/MainEdit.lean` proves `ZInQ.FrozenTarget` with `hL3` replaced by
  `{GrossZagierModuliOptCd, CdOptimal}` (`frozenTarget_gzoptimal`), or by
  `{GrossZagierModuliOptCd, StrongWeilOptimalCd, AnalyticIsogenyRational}` (`frozenTarget_gzoptimal_transfer`).
  The rest of the chain is heegner-32's `grossZagierHeegnerCd_of_printed` (from `hCM`, already an argument) and
  gz-conj's proved `grossConjugationCd`.

---

## 1. The new leaf

`ZInQ.GZOptimal.GrossZagierModuliOptAt E` (`GrossZagierOptimal.lean` §3) is `GZModuli.GrossZagierModuliAt E`
(gz-moduli) with two changes.

* **An added hypothesis `IsOptimalParam N f E X Y`**: `∃ L c, IsPeriodLattice E L ∧ L.lattice = c · Λ_f ∧
  ∀ τ, modPt E X Y τ = weierPt E L (c φ_f(τ))`, with `c ∈ ℚ`. Here
  `Λ_f = periodLattice f = span_ℤ {φ_f(γτ) − φ_f(τ) : γ ∈ Γ₀(N), τ ∈ ℍ}`, the integrals of `2πi f dτ` over
  `H₁(X₀(N), ℤ)`.
* **`y` with `ι(y) = n · Σ_r modPt E X Y (τ_r)`, `n ∈ ℤ ∖ {0}`**, instead of `n = 1`.

The leaf for the curves of the route is `GrossZagierModuliOptCd`: `GrossZagierModuliOptAt E'` for every short model
`E'` (`a₁ = a₂ = a₃ = 0`) with `aₙ(E') = aₙ(C_d)`, `d ≡ 5 (mod 8)` squarefree.

**Which definition of "optimal" matches Gross–Zagier's.** The task offered minimal degree or connected kernel on
Jacobians. The leaf states **connected kernel**, as surjectivity on `H₁`, for these reasons:

* For the Albanese map `J₀(N) → E` induced by φ, the cokernel of `H₁(J₀(N), ℤ) → H₁(E, ℤ)` is the group of
  components of the kernel. So `L = c Λ_f` (φ_* onto) is equivalent to a connected kernel, and dually to
  `E → J₀(N)` being injective (STANDARD).
* That is the definition of the strong Weil parametrization of a strong Weil curve (the optimal quotient). Sources,
  all UNVERIFIED: Mazur–Swinnerton-Dyer 1974 §1; Stevens 1989; Cremona, *Algorithms for modular elliptic curves*
  §2.14; Gross–Zagier Ch. V.
* "Minimal degree" cannot be stated, because Mathlib has no degree of a map of curves. It is also a different notion
  for a fixed non-optimal `E`, where the minimal-degree φ is not optimal.

`IsOptimalParam` also asks that `c ∈ ℚ`. For the true strong Weil parametrization this holds: `c` is the Manin
constant relative to the model, rational by the `q`-expansion principle (Manin 1972, UNVERIFIED). So the hypothesis
is met by the strong Weil parametrization (`NonVacuous.lean`, given route A's or route B's statement).

**Rating: printed form (constant forgotten), under either reading.**
* If Gross–Zagier Ch. V Thm 2.1 holds for every modular parametrization, the leaf is a restriction of it. In Lean,
  gz-moduli's leaf implies it (`grossZagierModuliOptAt_of_moduliAt`, using `[n] ∘ φ`).
* If the theorem is printed only for the strong Weil curve with its strong parametrization, the leaf is that case.
  Gross–Zagier state `y_K ∈ E(K)`, so `y = n y_K` and `ĥ(n y_K) = n² ĥ(y_K)` give the `n`-form.
* The other departures are gz-moduli's:
  - the constant `‖ω‖²/(c² u² √|D|)` becomes `∃ κ > 0`;
  - `L(E/K, s) = L(f, s) L(f ⊗ χ_D, s)` is folded in;
  - `X₀(N)` and Heegner points are rendered in the lattice model, and φ through `ℚ(X₀(N))`.
* `docs/research/locators.md` records Gross–Zagier as read at "I height formula (6.3), p.230" and "V §2
  rational-point deduction, p.312". It does not record the hypothesis on φ. **That hypothesis is the one item for a
  statement check** (pages-wanted: Gross–Zagier p. 230, I (6.3), and Ch. V §2 around p. 312).

**Why the `n`-form is needed.** heegner-32 makes the Heegner point rational for even `c` only. On the route, `c = 2`
with `c₀ = 1`, so the leaf is applied with `n = 2`; `y_K(φ_opt)` itself is not known in Lean to lie in `E(K)`. In
route B, `ψ̂(y)` is `M · y_K(φ')` for the index `M`.

## 2. `y_K`: a trace or a sum over a complete set

* Gross–Zagier (Ch. I §6 and Ch. V §2, UNVERIFIED locators) define `y_K = Σ_{σ ∈ Gal(H/K)} φ(x^σ) = Tr_{H/K} φ(x)`
  for one Heegner point `x = (𝒪_K, 𝔫, [𝔞])`. The trace of the divisor class `Σ_σ (x^σ − ∞)` has the same image,
  since `φ(∞) = O`.
* By Shimura reciprocity, `Gal(H/K) ≅ Cl(K)` acts on the Heegner points with fixed `𝔫` by `[𝔞] ↦ [𝔞 𝔟⁻¹]`, simply
  transitively (Gross 1984 §1–§2; Gross–Zagier II §1; STANDARD, locators UNVERIFIED). Elements of `Gal(H/K)` fix
  the ideal `𝔫` of `𝒪_K`.
* So `{x^σ}` is exactly a complete set of representatives of the `h(D)` Heegner points with that `𝔫`.
* gz-moduli's `IsHeegnerPointReps N D β τ` is such a set: β fixed, so `𝔫 = (N, (−β + √D)/2)` is fixed, and the set
  covers all homothety classes with that `𝔫`. With `D < −4`, `u = |𝒪_K^×|/2 = 1`, so there are no multiplicities.
* The sum over the reps is the trace. It is not the sum over all `2^s h(D)` Heegner points of discriminant `D`
  (both orientations), and neither is the leaf's.

**Verdict: the leaf matches the print. No change.** The `n`-form (§1) also covers a reader who takes `y_K` up to a
nonzero integer multiple.

## 3. From the optimal case to the consumer

The consumer is `GZHL3.GrossZagierFormulaAt (C_d)`: for every `c ∈ ℚ^×` with `c Λ_f ⊆ L`, and every `y ∈ E(K)` with
`ι(y) = Σ_{Q ∈ S} weierPt E L (c φ_f(τ_Q))`, `L'(E/K, 1) = κ ĥ(y)`.

**Additivity first.** `weierPt E L` is additive for models `y² = x³ + a₄x + a₆` (`weierPt_add'`, from the vendored
FLT uniformization theorem `PeriodPair.isUniformization_toPoint`, generalizing heegner-32's `y² = x³ + Ax`). So
`ι(y) = weierPt E L (c u)` with `u = Σ_Q φ_f(τ_Q)` (`heegnerC_eq`).

**Route A: `C_d` is its own strong Weil curve** (`core_selfOptimal`, `grossZagierFormulaCd_of_selfOptimal`).
1. With `L = c₀ Λ_f`, `c Λ_f ⊆ L` gives `(c/c₀) L ⊆ L`.
2. A rational multiplier of a lattice is an integer (`rat_mem_int`), so `c = n c₀` with `n ∈ ℤ ∖ {0}`.
3. Then `weierPt E L (c u) = n · weierPt E L (c₀ u) = n · Σ_r modPt(φ_opt)(τ_r)`, and the leaf applies to
   `φ_opt = (xPar E L f c₀, yPar E L f c₀)`. This φ is a modular parametrization by gz-moduli's `isModularParam_of`,
   and optimal by `L = c₀ Λ_f`.

This is the factorization "every admissible φ is an isogeny composed with the optimal one", with the isogeny `[n]`.

**Route B: through the strong Weil curve `E'`** (`core_transfer`, `grossZagierFormulaCd_of_transfer`).
1. `StrongWeilOptimalCd` gives a short model `E'` with `aₙ(E') = aₙ(f)` and `L' = c' Λ_f`.
2. The consumer's φ is `ψ ∘ φ'`, with `φ' = weierPt E' L' (c' φ_f)` and `ψ : z ↦ (c/c') z`; `(c/c') L' ⊆ L`.
3. Finite index (`exists_int_mul_mem`, the determinant of the inclusion) gives `M ≠ 0` with `M L ⊆ (c/c') L'`.
   So `ψ̂ : z ↦ μ z`, `μ = M c'/c ∈ ℚ`, maps `L` into `L'`.
4. `AnalyticIsogenyRational` gives `P' ∈ E'(K)` with `ι(P') = weierPt E' L' (μ c u) = M · Σ_r modPt(φ')(τ_r)`.
5. The leaf at `E'` gives `L'(E/K, 1) = κ' ĥ(P')`. This is the same L-value: `aₙ(E') = aₙ(E)` and the same `F`, `G`.
6. `y` and `P'` are torsion together (`isOfFinAddOrder_iff`: a point is torsion iff `k w ∈ L` for its parameter `w`):
   - `k c u ∈ L ⇒ μ k c u = k M c' u ∈ L'`;
   - `k M c' u ∈ L' ⇒ (c/c') k M c' u = kM · c u ∈ L`.
7. Tau Ceti's `ĥ ≥ 0` and `ĥ = 0 ⇔ torsion` (Northcott over number fields) turn `κ' ĥ(P')` into `κ ĥ(y)`, κ > 0
   (`exists_pos_of_torsion_iff`).

No height comparison between different curves is needed. That would be `ĥ(ψP) = deg ψ · ĥ(P)`, which is not in
Tau Ceti.

**gz-moduli's all-φ leaf.** `GZModuli.GrossZagierModuliCd` quantifies over every `IsModularParam` φ, not only the
analytic ones.
* It follows from either route plus `ModularParamAnalyticCd` (`grossZagierModuliCd_of_selfOptimal`,
  `grossZagierModuliCd_of_transfer`). `ModularParamAnalyticCd` says every modular parametrization of `C_d` lifts to
  `c φ_f`.
* That statement is composite: it needs `g = c f` for `φ^*ω = 2πi g dτ`, by Eichler–Shimura, Faltings and
  multiplicity one.
* **The consumer does not need it.** Its φ are analytic by definition, so the fold should discharge
  `grossZagierFormulaCd` directly, not gz-moduli's leaf.

### The isolated statements and their ratings

| Statement | Kind | Rating and reason |
| --- | --- | --- |
| `GrossZagierModuliOptCd` | published | **LEAF, printed form under either reading** (§1). Weaker than gz-moduli's leaf (proved). |
| `CdOptimal` (route A) | project glue | **GLUE.** A period computation: `L(C_d) = c₀ Λ_f`. Numerically true, c₀ = 1, for 18 values of `d` (§4). gz-weil proved `2 Λ_f ⊆ L`. Open: `Λ_f ⊆ L` and `L ⊆ Λ_f`. It fails for `d = 1` (`y² = x³ − x` is 32a2, not optimal), so it depends on `d ≡ 5 (mod 8)`. Not known to me as a published theorem (SPECULATIVE). |
| `StrongWeilOptimalCd` (route B) | composite | **GLUE.** Textbook (Shimura 1971 Thm 7.14, §7.5; Diamond–Shurman §6.6; Manin 1972; AEC III.1; UNVERIFIED). Printed over `J₀(N)`; the analytic form `L' = c Λ_f` adds the period computation for the optimal quotient and the rationality of `c`. It sharpens gz-hl3's `StrongWeilCurve` (inclusion, rated composite) to equality. |
| `AnalyticIsogenyRational` (route B) | composite | **GLUE.** Textbook (AEC Thm VI.4.1, Prop. VI.3.6, Thm III.5.2, Cor. III.5.3; UNVERIFIED). Composite only because Mathlib has no isogenies of Weierstrass curves, so the isogeny is given by its multiplier (as gz-hl3's `IsogenyLattice`). |
| `ModularParamAnalyticCd` (not used by the consumer) | composite | **GLUE.** Eichler–Shimura + Faltings + multiplicity one. |

All five statements are true mathematically. Route A's `CdOptimal` is true for the 18 tested `d`; for general `d` it
is SPECULATIVE.

## 4. Numerical evidence for `CdOptimal`

**PARI `ellweilcurve`** (`scratch/gz-optimal/py/optimal_cd.py`) returns the Smith invariants of `L_{E'}` in `L_f`
over the isogeny class.
* `d = 5` (`N = 800`) and `d = 13` (`N = 5408`): `C_d` is the curve with `[1, 1]`, i.e. the optimal one. The class
  pattern is `[[1,1],[2,1],[2,1],[2,1]]` (VERIFIED, computed).
* `d = 21` overflowed 14 GB.

**Direct periods** (`scratch/gz-optimal/py/periods_cd.gp`, `periods_cd.py`, output `periods_cd_out.txt`).
* Method:
  - `Ψ(γ) = φ_f(γτ) − φ_f(τ)`, with `φ_f = Σ aₙ/n qⁿ` exactly as `GZHL3.eichler`;
  - `γ = [a, b; c, e] ∈ Γ₀(N)`, `c = kN`, `τ = (−e + i)/c`, so that `γτ = (a + i)/c`;
  - the `q`-series is truncated at `|q|^M < 10⁻¹⁷`;
  - each `Ψ(γ)` is written in the basis `E.omega` of `L(C_d)` (the differential `dx/2y`, as `IsPeriodLattice`).
* Results for `d = 5, 13, 21, 29, 37, 53, 61, 69, 77, 85, 93, 101, 109, 133, 141, 149, 157, 165` (outputs
  `periods_cd_out.txt`, `periods_cd_out2.txt`, `periods_cd_out3.txt`):
  - every coordinate is an integer, to within `10⁻¹⁸`;
  - the sampled periods span `L(C_d)`, index 1. The sample was `a ≤ 25`, `k = 1`; for `d = 77` and `d = 165` it
    needed `a ≤ 80`, `k ≤ 2`.
* So numerically `Λ_f = L(C_d)`: `C_d` is X₀(N)-optimal with Manin constant 1. This agrees with heegner-32's
  observation for `d = 5, 13`.
* VERIFIED as a computation. It is a sample: the integrality of every `Ψ(γ)` is not proved.

**How `CdOptimal` could be proved in Lean (SPECULATIVE).** The twisting formula
`Φ_d(τ) = g⁻¹ Σ_a χ(a) φ₃₂(τ + a/d)` gives
`Λ_{f_d} = g⁻¹ {Σ_a χ(a) ℓ(γ_a) : γ ∈ Γ₀(32 d²)}`, where `ℓ : Γ₀(32) → H₁(X₀(32), ℤ)` is the level-32 period map.
Here `X₀(32) = 32a1` with degree-1 parametrization. So `CdOptimal` reduces to integrality and generation of twisted
modular symbols at level 32, a finite-flavoured computation per `d` but not uniform in `d`. heegner-32 notes that its
level-32 route reaches only even `c`; the odd part is the open point.

## 5. Deliverables

| File | Content | Check |
| --- | --- | --- |
| `ZInQKernel/Contrib/OneProof/GrossZagierOptimal.lean` | §1 additivity of `weierPt`, torsion criterion; §2 lattice lemmas; §3 statements; §4 glue; §5 new leaf ⇐ gz-moduli's leaf; §6 cores; §7 the consumer by routes A and B; §8 gz-moduli's all-φ leaf given `ModularParamAnalyticCd` | `lake build` (VERIFIED) |
| `ZInQKernel/Contrib/OneProof/GrossZagierOptimal/NonVacuous.lean` | `exists_optimalParam_cd` (route A), `exists_optimalParam_of_sw` (route B) | `lake build` (VERIFIED) |
| `scratch/gz-optimal/Target.lean` | verbatim copy of `GrossZagierModuliAt`/`GrossZagierModuli`/`GrossZagierModuliCd`, `rfl` against the original | compiled (VERIFIED) |
| `scratch/gz-optimal/Check.lean`, `out_check.txt` | `#print axioms`, 12 theorems | standard axioms (VERIFIED) |
| `scratch/gz-optimal/Discharges.lean`, `discharges-output.txt` | `#discharges` | §6 |
| `scratch/gz-optimal/MainEdit.lean`, `out_mainedit.txt` | `frozenTarget_gzoptimal` (route A), `frozenTarget_gzoptimal_transfer` (route B) | standard axioms (VERIFIED) |
| `scratch/gz-optimal/autofold.json` | route A spec for the field `grossZagierFormulaCd` | JSON checked |
| `scratch/gz-optimal/autofold-routeB.json` | route B spec (needs `--allow-rise`) | JSON checked |
| `scratch/gz-optimal/py/` | PARI scripts and outputs (§4) | computed |

Proposed `locators.md` rows (for the integrator; this task does not edit that file):
- `GrossZagierModuliOptCd` → Gross–Zagier 1986, Thm I.6.3 (p. 230 per locators.md) and Ch. V Thm 2.1 (V §2, p. 312
  per locators.md), strong Weil case; read the hypothesis on φ.
- `StrongWeilOptimalCd` → Shimura 1971 Thm 7.14 / §7.5; Cremona 1997 §2.14.
- `AnalyticIsogenyRational` → Silverman AEC VI.4.1, III.5.2.

## 6. `#discharges`

`scratch/gz-optimal/discharges-output.txt` (VERIFIED):
- command: `lake env lean scratch/gz-optimal/Discharges.lean`, after `lake build +ZInQKernel.OneProof.Main
  +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.GrossZagierOptimal
  +ZInQKernel.Contrib.OneProof.GrossZagierOptimal.NonVacuous`;
- result: 61 open hypotheses, 3011 theorems checked, no line for `GZOptimal`.

As for heegner-32, gz-conj and gz-moduli, `hL3` is a top-level `frozenTarget` argument stated for all `E`, and the
theorems here prove its `C_d` chain. An all-`E` theorem would need additivity of `weierPt` for general Weierstrass
models, which needs the variable-change point map to be additive. That is not in Mathlib, and it is not needed on
the route. The fold is the Main edit (`MainEdit.lean`). Once `hL3` is split into the field `grossZagierFormulaCd`,
`autofold.json` applies; use it in place of gz-moduli's spec.

## 7. What remains

* **A statement check of Gross–Zagier Ch. V §2 for the hypothesis on φ.** If V.2.1 is printed for every modular
  parametrization, gz-moduli's leaf is printed and gives the −1 directly. Otherwise use route A.
* **`CdOptimal` in Lean** (route A then gives the clean −1), or a published source for it. The numerics cover
  18 values of `d ≤ 165`.
* The explicit constant could be restored once a reading fixes the normalization of `ĥ`, as in gz-moduli.
