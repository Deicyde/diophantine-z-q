# linyang-printed: `LinYangThetaCurve` from two printed leaves; `igusaPsi4` and `igusaChi10` become theorems

Task linyang-printed, 2026-11-14/15. Base b5ff0474 (w63, leaf-fold12, `sixContactMin_of_open15`, 61 fields). Inputs read
with `git show`, not merged: theta-glue (origin/wip/theta-glue, §5 of its report) and igusa-alg (origin/wip/igusa-alg
c9360203). Lean files are in `scratch/linyang-printed/`, the results log is `scratch/linyang-printed/log.md`, and the
Fourier check is `scratch/linyang-printed/py/fourier.py`. No file under `ZInQKernel/` or `blueprint/`, and no other
task's notes or scratch, was edited. This is model work with no human review.

Marks: **VERIFIED** means compiled, computed, or read in a file. **STANDARD** means published, with a reference.
**SPECULATIVE** means a judgement. Theorem numbers and locators recalled from memory are **UNVERIFIED** (no network).

## 1. Main result

1. **`LinYangThetaCurve` is a theorem from two leaves stated in printed form** (VERIFIED, compiled, standard axioms).
   Its statement is theta-glue's, copied verbatim:
   * `linYangThetaCurve_of_printed : IgusaThetaExpressions → LinYangEx29 → LinYangThetaCurve`;
   * the strict variant `linYangThetaCurve_of_printedAll : IgusaThetaExpressions → LinYangEx29All →
     PkgI1.QMHauptmodul → LinYangThetaCurve`. Here the Lin–Yang leaf asserts only the relations, for every
     normalized Hauptmodul, and the Hauptmodul comes from the chain's own `QMHauptmodul`.

   The two leaves:
   * **`IgusaThetaExpressions`** (Igusa). On `𝔥₂`, the theta expressions equal Igusa's generators:
     `ψ₄ = psi4Th`, `ψ₆ = psi6Th`, `χ₁₀ = chi10Th`, `χ₁₂ = chi12Th`. The generators are defined genuinely:
     * `ψ_k` is the degree-2 Siegel Eisenstein series, a sum over `Γ_∞\Sp₄(ℤ)`;
     * `χ₁₀` and `χ₁₂` are Igusa's 1962 combinations of Eisenstein series.
   * **`LinYangEx29`** (Lin–Yang, Example 29). There is a Hauptmodul `j₆` of `Γ*\ℍ` with values `0, ∞, −16/27` at the
     CM points of discriminants −4, −3, −24, such that wherever `j₆ = z ≠ ∞` along `Ω(τ)`:
     `s₃² = z s₂³`, `s₅ = s₂s₃`, `s₆ = (z+1)s₂³`. These are Lin–Yang's printed `s₃²/s₂³ = j₆`, `s₅/(s₂s₃) = 1`,
     `s₆/s₂³ = j₆ + 1` with denominators cleared. Here `s₂ = ψ₄`, `s₃ = ψ₆`, `s₅ = 2¹²3⁵χ₁₀`, `s₆ = 2¹²3⁶χ₁₂`.

   **Eliminating `j` is easy.** In Lin–Yang's normalized variables `s_k` the printed relations are linear in `j₆`.
   Where `j₆` is finite, `s₆ = s₂³ + z s₂³ = s₂³ + s₃²` follows by `linear_combination`. The points where `j₆ = ∞`
   form one `Γ*`-orbit, which is countable since `Γ* ⊂ ι(B)` and `B ≅ ℚ⁴`. Both sides are continuous on `ℍ`
   (copy of period-map's analyticity step), so the identity extends by density.

   No large polynomial identity arises, so igusa-alg's `IgusaAlgEval.Data.gen_eq_zero` is not needed for the
   elimination. It is still used, unchanged, on the Route 1 path (item 4).
2. **Fourier check (VERIFIED, exact).** All 76 Fourier coefficients agree, at every half-integral `T` with `n, m ≤ 2`,
   between:
   * theta-glue's theta expressions, parsed from the Lean text, and
   * the Eisenstein series (Maass/Cohen formula) with Igusa's constants
     `χ₁₀ = −43867·2⁻¹²3⁻⁵5⁻²7⁻¹53⁻¹(ψ₄ψ₆ − ψ₁₀)` and
     `χ₁₂ = 131·593·2⁻¹³3⁻⁷5⁻³7⁻²337⁻¹(3²7²ψ₄³ + 2·5³ψ₆² − 691ψ₁₂)`.

   Since `dim M_k = 1, 1, 2, 3` for `k = 4, 6, 10, 12`, and theta-glue showed the theta expressions are modular,
   this pins `IgusaThetaExpressions`. That includes theta-glue's sign choice in `ψ₆` (it is `+ψ₆`) and the recalled
   1962 constants.
3. **`igusaPsi4` and `igusaChi10` become theorems** (VERIFIED, compiled). The modularity of the Siegel Eisenstein
   series is proved in Lean (§4.2): `ψ_k(MΩ) = det(CΩ+D)^k ψ_k(Ω)` for even `k`, with no convergence needed.
   From it:
   * `igusaPsi4_of_printed : IgusaThetaExpressions → QMSplit.Theta.IgusaPsi4`;
   * `igusaChi10_of_printed : IgusaThetaExpressions → QMSplit.Theta.IgusaChi10`;
   * `thetaModularity_of_printed : IgusaThetaExpressions → PkgI1.ThetaModularity`.

   These hold for every `M ∈ Sp₄(ℤ)` and are stated over the kernel's own constants. At chain level,
   `HDec.HSyn.sixContactMin_of_open15P` proves `ZInQ.SixContactMin` from a research bundle of **31** fields:
   leaf-fold12's 32 with `igusaPsi4` and `igusaChi10` replaced by `igusaThetaExpressions`.
4. **Route 1 from the printed leaves** (VERIFIED, compiled together with igusa-alg's file):
   * `thetaRatiosAtQM_of_printed : IgusaThetaExpressions → LinYangEx29 → ThetaRatiosAtQM`;
   * `thetaPointOfFibre_of_printed : FibreQMPeriod → IgusaThetaExpressions → LinYangEx29 → ThetaPointOfFibre`;
   * `thetaPointOfFibre_of_printedAll : FibreQMPeriod → QMHauptmodul → IgusaThetaExpressions → LinYangEx29All →
     ThetaPointOfFibre`.
5. **Bonus** (VERIFIED, compiled): `qmHauptmodul_of_printed : IgusaThetaExpressions → LinYangEx29 → PkgI1.QMHauptmodul`.
   The function `j₆` is pkg-I1's `j_θ`, since `16·144⁵χ₁₀²/ψ₄⁵ = s₃²/s₂³` when `s₅ = s₂s₃`.
6. **Cross-check with R3** (VERIFIED, compiled). `jTuple_of_sForm` shows that the `s`-form relations, combined with
   Igusa's conversion as restated in Lin–Yang (13)-(14), give exactly the `J`-tuple
   `[12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]` of `ZInQ.LeafPush2.LinYangTuple`, with scale `t = −s₃/(12js₂)`.
   So the project's two transcriptions of the printed result agree.
7. **gap-triage's note is correct** (VERIFIED by reading):
   * `igusaPsi4` and `igusaChi10` are used only through `r4 = ThetaModularity`, and `r4` only at `M4` and `M6` along
     `Ω(z)`;
   * Route 1 as theta-split and igusa-alg stated it does **not** make them unnecessary. Route 1's
     `thetaPointOfFibre_of_linYang` still needs `FibreQMPeriod`, whose inputs `qmHauptmodul` and `qmDenZeroCM3`
     use `r4` (§6);
   * with the printed leaf `IgusaThetaExpressions`, which Route 1 needs anyway, both fields are unnecessary. The
     proof is item 3.

**Verdict.** Under the strict convention, theta-glue's composite leaf `LinYangThetaCurve` is replaced by two leaves
in printed form: `IgusaThetaExpressions` (Igusa) and `LinYangEx29All` (Lin–Yang Example 29, the relations only).
`LinYangEx29` is the variant that also carries `j₆`'s existence. The same Igusa leaf also absorbs the two research
fields `igusaPsi4` and `igusaChi10`. No statement was found false, vacuous or inert.

## 2. Statements (namespace `HDec.HSyn.G0Split.ThetaPt.LinYangPrinted` unless noted)

| name | kind | content | status |
|---|---|---|---|
| `ThetaGlue.psi4Th`, `psi6Th`, `chi10Th`, `chi12Th`, `ThetaGlue.LinYangThetaCurve` | verbatim copies | theta-glue ThetaGlue.lean l.392-470, 534-551, 578-597 (`sed -n`, same namespace) | — |
| `botRel`, `botSetoid`, `SiegelCosets` | definitions | `Γ_∞\Sp₄(ℤ)` as bottom block rows modulo `GL₂(ℤ)` | — |
| `siegelEis k` | definition | `Σ_{c ∈ Γ_∞\Sp₄(ℤ)} det(CΩ+D)^{-k}` (`tsum`, one representative per class) | genuine for even `k ≥ 4` (absolutely convergent) |
| `igusaChi10E`, `igusaChi12E` | definitions | Igusa 1962 combinations (constants above) | VERIFIED by Fourier coefficients |
| `lyS2`, `lyS3`, `lyS5`, `lyS6` | definitions | Lin–Yang's `s₂ = ψ₄, s₃ = ψ₆, s₅ = 2¹²3⁵χ₁₀, s₆ = 2¹²3⁶χ₁₂` | — |
| `IgusaThetaExpressions` | **LEAF** (printed) | on `𝔥₂`: `ψ₄, ψ₆, χ₁₀, χ₁₂` = theta expressions | cited; Fourier VERIFIED |
| `LinYangEx29` | **LEAF** (consequence of printed) | `∃ j₆` Hauptmodul (QMHauptmodul's clauses) with the three cleared relations where `j₆ ≠ ∞` | cited; numerically consistent |
| `LinYangEx29All` | **LEAF** (printed, strict) | `∀ j₆` with those clauses → the relations | cited |
| `linYangThetaCurve_of_printed`, `…_of_printedAll` | theorems | `LinYangThetaCurve` | **PROVED** |
| `qmHauptmodul_of_printed` | theorem | `PkgI1.QMHauptmodul` | **PROVED** |
| `linYangEx29_of_all` | theorem | `LinYangEx29All → QMHauptmodul → LinYangEx29` | **PROVED** |
| `jTuple_of_sForm` | theorem | `s`-form ⇒ R3's `J`-tuple | **PROVED** |
| `spFactor_ne_zero`, `spAct_mem`, `spFactor_mul`, `spFactor_botRel`, `rightEquiv` | theorems | `det(CΩ+D) ≠ 0`; `Sp₄(ℤ)𝔥₂ ⊆ 𝔥₂`; cocycle; representative independence; `c ↦ cM` | **PROVED** |
| `siegelEis_modular` | theorem | `ψ_k(MΩ) = det(CΩ+D)^k ψ_k(Ω)`, even `k` | **PROVED** |
| `igusaPsi4_of_printed`, `igusaChi10_of_printed`, `thetaModularity_of_printed` | theorems | the kernel's `QMSplit.Theta.IgusaPsi4`, `IgusaChi10`, `PkgI1.ThetaModularity` | **PROVED** |
| `HDec.HSyn.OpenResearchLeaves12P`, `researchLeaves12_of_P`, `sixContactMin_of_open15P` | bundle, theorems | 31 research fields → `ZInQ.SixContactMin` | **PROVED** |
| `IgusaAlgFinal.thetaRatiosAtQM_of_printed`, `thetaPointOfFibre_of_printed`, `…_printedAll` | theorems | Route 1 from the printed leaves | **PROVED** |

## 3. The two leaves (Lean text in `LinYangPrinted.lean` §2)

**`IgusaThetaExpressions`:**
`∀ Ω ∈ PkgI1.SiegelH2, siegelEis 4 Ω = psi4Th Ω ∧ siegelEis 6 Ω = psi6Th Ω ∧ igusaChi10E Ω = chi10Th Ω ∧
igusaChi12E Ω = chi12Th Ω`.
* *Sources:* J.-I. Igusa, *On Siegel modular forms of genus two (II)*, Amer. J. Math. 86 (1964), and *Modular forms
  and projective invariants*, Amer. J. Math. 89 (1967), p. 848 (locators UNVERIFIED). The Eisenstein-series
  definition of `ψ_k` and the constants of `χ₁₀`, `χ₁₂` are from Igusa 1962, Amer. J. Math. 84 (constants recalled,
  UNVERIFIED as a citation).
* *Form:* printed. The theta expressions are printed as theorems about Igusa's forms. The kernel's docstring of
  `IgusaPsi4` already says that its leaf is the conjunction "Eisenstein modularity ∧ theta expression"; the first
  conjunct is now proved.
* *Evidence:* py/fourier.py, 76/76 exact coefficients (§1 item 2).
* *Genuineness:* `siegelEis` uses `Quotient.out`, one representative per coset. For even `k` the summand does not
  depend on the choice (proved, `spFactor_botRel`). For `k ≥ 4` the series converges absolutely on `𝔥₂`, so the
  `tsum` is the classical value. The relation `botRel` (bottom rows equal up to `GL₂(ℤ)`) is the coset relation of
  `Γ_∞ = {C = 0}` (STANDARD).

**`LinYangEx29`, `LinYangEx29All`:** the text is in §1 item 1 and in the docstrings. The CM clauses are verbatim
those of `PkgI1.QMHauptmodul`.
* *Sources:* Y.-H. Lin, Y. Yang, *Quaternionic loci in Siegel's modular threefold*, Math. Z. 295 (2020), 775-819;
  arXiv:1807.00466v1 Example 29, pp. 20-21:
  * the definition of `j₆` by its CM values was VERIFIED in arXiv v1 by h-v14 (row L719);
  * the constants `c₁ = c₂ = c₃ = c₄ = 1` and the `s`-normalization were derived from the arXiv text in h-v14 §5.3
    (scratch/h-v14/igusa_check.py);
  * the display itself was not re-read here (UNVERIFIED).
* *Form:* `LinYangEx29All` is a consequence of the printed identity of meromorphic functions, evaluated where `j₆`
  is holomorphic: never stronger, and it makes no existence claim. `LinYangEx29` adds the existence of `j₆`, which
  Lin–Yang presuppose (genus 0 of `X₆/W`). Under the strictest reading that makes it composite, so `LinYangEx29All`
  is the recommended field.
* *Faithfulness:* as for `PkgI1.QMHauptmodul`, `Ω(τ)` is pkg-I1's period matrix of the QM surface at `τ`. The ratios
  `s₃²/s₂³`, `s₅/(s₂s₃)`, `s₆/s₂³` are `Sp₄(ℤ)`-invariant, so the choice of symplectic basis does not matter.
* *Consistency:* with Igusa's theta expressions this is theta-glue's 80-digit check of `LinYangThetaCurve`, together
  with pkg-I1's numerical values of `j_θ = s₃²/s₂³∘Ω`.

## 4. Proofs

### 4.1 Eliminating `j` (`linYangThetaCurve_of_printed`, `qmHauptmodul_of_printed`)
* Let `S = {τ : j₆(τ) = ∞}`, viewed in `ℂ`. Since the fibres of `j₆` are `Γ*`-orbits, `S` is countable
  (`fibre_countable`, with `gammaStar_countable` from `B ≃ ℚ⁴`).
* Off `S`, put `z = j₆(τ)`. `IgusaThetaExpressions` at `Ω(τ) ∈ 𝔥₂` (`omegaSiegel_proof`) converts the `s_k` to theta
  expressions, and then `linear_combination (-1)·h₂` and `linear_combination h₁ − h₃` give the two relations.
* Each `θ_m∘Ω` is analytic on `ℍ`. The proof copies the inner step of `thetaOmegaAnalytic_of` in TailJ. The four
  forms are continuous polynomials in the ten `θ_m`.
* `eqOn_of_countable` (via `Set.Countable.dense_compl`) extends the relations to `ℍ`.
* For `QMHauptmodul`:
  * where `j₆ = z` and `ψ₄ ≠ 0`: `z = s₃²/s₂³ = 3779136Π²/Σ⁵`, since `3779136 = 2⁶3¹⁰`;
  * where `j₆ = ∞` but `ψ₄ ≠ 0`: near the point, `j₆∘ofComplex` agrees with the continuous `ℂ`-valued `s₃²/s₂³` off a
    countable set, so it is finite there. Contradiction.

### 4.2 Modularity of the Eisenstein series (§6, about 300 lines; the development copy `EisDev.lean` imports only LPrefix)
* **Positivity.** `ω(a, b) = a·Jb` is preserved by `M ∈ Sp₄(ℤ)` (Mathlib's `mem_iff'`: `MᵀJM = J`), in both its
  bilinear and hermitian forms. For `u = (Ωv, v)` one has `M u = (Wv, Xv)` with `W = AΩ+B`, `X = CΩ+D`. Comparing
  the two sides gives `−(Wv)*·Xv + (Xv)*·Wv = 2i·v̄ᵀ(Im Ω)v > 0`.
* **Consequences.**
  * `det X ≠ 0`, because `Xv = 0` forces `v = 0`;
  * `WX⁻¹` is symmetric (bilinear form);
  * `Im(WX⁻¹)` is positive definite (hermitian form, at real `a = Xv`).
* **Cocycle.** `X_{NM} = (C_N(MΩ) + D_N)X_M`, using block multiplication and `X⁻¹X = 1`.
* **Reindexing.** `c ↦ c·M` is a bijection of `Γ_∞\Sp₄(ℤ)`. The summand of a class does not depend on its
  representative for even `k`, since `det U = ±1`. `Equiv.tsum_eq` and `tsum_mul_left` hold without summability.

## 5. Field table (before and after)

| field | bundle | w63 (open15) | after, compiled here (`sixContactMin_of_open15P`) | after the Route 1 fold (igusa-alg + this task) |
|---|---|---|---|---|
| `igusaPsi4` | research | LEAF (Igusa; "Eisenstein modularity ∧ theta expression") | **theorem** `igusaPsi4_of_printed` | theorem |
| `igusaChi10` | research | LEAF (Igusa; same) | **theorem** `igusaChi10_of_printed` | theorem |
| `igusaThetaExpressions` | research | — | **LEAF** (printed, Igusa 1964/1967) | LEAF |
| `thetaRatiosAlgebraic` | added | LEAF? (universal, composite) | unchanged | removed: the consumer uses `thetaPointOfFibre_of_printedAll` (igusa-alg's interim was the composite `LinYangThetaCurve`) |
| `linYangEx29All` | added | — | — | **LEAF** (printed, Lin–Yang Ex. 29) |
| totals research/textbook/added/glue | | 32 / 15 / 13 / 1 = 61 | **31** / 15 / 13 / 1 = 60 | 31 / 15 / 13 / 1 = 60, with no composite theta leaf |

The fold's `thetaPointOfFibre_of_printedAll` also needs `PkgI1.QMHauptmodul`. That is available at the consumer:
TailK's assembly passes `l.qmHauptmodul` to `fibreQMPeriod_main_rep`.

Optional further step, not done: `qmHauptmodul_of_printed` could replace the derivation of `QMHauptmodul` through
`qmHauptmodulBase3_of_leaves` (r4, `valenceFormulaCocompactEq`, `shimizuCovolumeO1`, `igusaCMValue24`). Dropping
`valenceFormulaCocompactEq` and `shimizuCovolumeO1` would also require `QMDenZeroCM3` from the printed leaves, which
needs "ψ₄, ψ₆, χ₁₀, χ₁₂ have no common zero on `Ω(ℍ)`" (not proved here), and a PruneScan of their other uses.

## 6. gap-triage's note, checked (VERIFIED by reading the kernel)
* `r.igusaPsi4` and `r.igusaChi10` occur only in `QMSplit.Theta.thetaModularity_of` (TailX l.199, TailZ4 l.235).
* `r4 : ThetaModularity` is used by:
  * `qmDenZeroCM3_of_leaves4` (TailK l.317);
  * `base2_of_base3` (TailO l.2779, l.2967);
  * `qmHauptmodulBase3_of_leaves` (TailZ4 l.235, through TailZ2's `auto8` and `auto20`).
* All of these go through `s8WeightExact_of` and `s20WeightExact_of`, that is through
  `g8Auto_g4/g6` and `g20Auto_g4/g6`, which call `g8Auto_gen hT g _ M4 …` and `… M6 …` with `Ω = Omega z`. So the
  fields are used only at `M4` and `M6`.
* Route 1 (theta-split, igusa-alg) removes neither field, because `FibreQMPeriod` still consumes `qmHauptmodul` and
  `qmDenZeroCM3`.
* `IgusaThetaExpressions` removes both, for all of `Sp₄(ℤ)`, not just `M4` and `M6`. This supersedes gap-triage's
  plan A2 (theta transformation at `M4`, `M6`).

## 7. Files and compile results (all `lake env lean`; outputs in `*.out`)

| file | content | result |
|---|---|---|
| `LinYangPrinted.lean` | §0-§8; imports TailU, uses the kernel's `IgusaPsi4`/`IgusaChi10` | 0 errors, 13 s, 9 axiom lines standard |
| `LinYangPrintedChain.lean` | the same with import TailZ19, plus §9 (31-field bundle, `sixContactMin_of_open15P`) | 0 errors, 13 s, 11 standard |
| `LinYangPrintedFull.lean` | igusa-alg's IgusaAlg.lean (verbatim, import TailZ19) + Chain minus §0 + §10 (Route 1) | 0 errors, 1 min 45 s, 13.4 GB, 16 standard |
| `EisDev.lean` | development copy of §6 (imports LPrefix only) | 0 errors |
| `py/fourier.py`, `fourier1.out`, `fourier2.out` | Fourier check | 76/76 equal |

Olean caveat: `.lake/build` was copied from ~/dzq-check2 (29885092). Its TailY, TailZ7, TailZ14 and TailZ15 differ
from b5ff0474 only in docstrings: `git diff` shows no changed `def`, `theorem`, `structure` or field line. TailZ19
and every bundle file are identical. A rebuild of the chain on this base was not run.

## 8. Integration notes
* Add `IgusaThetaExpressions`, with its definitions `SiegelCosets`, `siegelEis`, `igusaChi10E`, `igusaChi12E`
  (§1-§2), as a research field in place of `igusaPsi4` and `igusaChi10`. The proofs in §3, §6 and §8 are
  self-contained and need only TailJ (analyticity of `θ∘Ω`) and TailU (the two Props). §9 is the bundle step.
* For Route 1, combine with igusa-alg's fold. Replace `thetaRatiosAlgebraic` by `linYangEx29All` and the consumer
  `thetaPointOfFibre_of_qm_ratios hQM hAlg` by `IgusaAlgFinal.thetaPointOfFibre_of_printedAll hQM l.qmHauptmodul hI hA`.
  The verbatim copies `psi4Th`, …, `LinYangThetaCurve` are byte-identical to theta-glue's, and igusa-alg copied
  them verbatim too.
* Do not count `LinYangEx29` and `LinYangEx29All` both: they are alternatives.
