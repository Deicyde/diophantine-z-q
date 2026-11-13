# contrib-tidy: the Contrib folders made ready for two proof-only upstream PRs

Task contrib-tidy, 2026-11-12/13. Branch `wip/contrib-tidy`, base `32cdf928`
(origin/wip/integrate-w35a). Log: `scratch/contrib-tidy/log.md`. Marks: VERIFIED means compiled
or run here.

## Result

- **One copy of the bp-hecke-fe development.** `GaussFE/HeckeFE.lean` and `HeckeAll/HeckeFE.lean`
  were identical apart from the namespace (`diff` after renaming the namespace was empty). One copy
  is kept, as `ZInQKernel/Contrib/HeckeFE/Basic.lean` with namespace `ZInQ.Contrib.HeckeFE`. The
  other copy is deleted. `GaussPointCount`, `GaussSplit`, `HeckeContinuation5` and the other
  definitions now exist once. The `GaussFE` and `HeckeAll` modules import the shared module and
  `open ZInQ.Contrib.HeckeFE`.
- **Statements.** Both providers keep their names and types. VERIFIED: `scratch/contrib-tidy/Types.lean`
  checks with `Expr` equality that the type of each provider is exactly the target constant. The only
  changes to statements are these:
  - the namespace of the shared copy (`GaussFE.*` and `HeckeAll.*` became `HeckeFE.*`);
  - `HeckeAll.GaussPointCount` became `HeckeFE.GaussPointCount` in the two `HeckeAll/Continuation.lean`
    theorems that mention it;
  - line wrapping, which changes whitespace only.

  `git diff -w --word-diff` from `32cdf928` shows nothing else: in the shared copy, the namespace,
  the module docstring and the `if_pos` renames listed below.
- **Hygiene.** Every module has a module docstring saying what it proves. The docstring of
  `HeckeFE/Basic.lean` was rewritten to cover the whole file; the others were already adequate and
  only file references were updated. No Contrib line is over 100 characters except one, at
  `GaussFE/Headline.lean:34`: it is the upstream headline identifier
  `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzInputs_functionalEquation5_grossZagier`,
  115 characters long, which cannot be split. There is no `sorry`, `admit`, `axiom` or `native_decide`
  (checked with `grep -w`).
  - **Lint fixes.** I replaced the deprecated `if_pos`, `if_neg`, `dif_pos`, `dif_neg`, `if_true`
    and `if_false` with `ite_eq_left`, `ite_eq_right`, `dite_eq_left`, `dite_eq_right`, `ite_true`
    and `ite_false`. Lean 4.35 deprecated these names on 2026-07-21, and the replacements have
    identical types. I also removed four no-op `<;> norm_num` in `Gauss.lean` and turned two `<;>`
    into `;` in `Hasse.lean` and `Convergence.lean`.
  - **Warnings left on purpose.**
    - Seven `unusedSectionVars` warnings: `HeckeFE.norm_piZ` and `norm_conj_piZ`;
      `GaussFE.chi_pow_four`, `chi_neg_one_sq`, `chi_ne_one`, `chi_sq_ne_one` and `chi_cube_ne_one`.
      The fix (`omit … in`) would remove hypotheses from these theorems' signatures, which the task
      forbids.
    - The note "imports … designed for use with the module system", which every baseline file also
      gets.
- **Builds and checks (VERIFIED).**
  - All 15 Contrib modules build, and so does `lake build ZInQKernel`.
  - `scratch/contrib-check/Check.lean` compiles unchanged. Its imports (`HeckeAll.Provider`,
    `GaussFE.Headline`, the PSide modules) kept their names.
  - Every `#print axioms` line is `[propext, Classical.choice, Quot.sound]`.
  - Nothing outside `ZInQKernel/Contrib/` imports a Contrib module.
  - No file outside `ZInQKernel/Contrib/` and `scratch/contrib-tidy/` changed.
- **Upstream CI dry run (VERIFIED). Upstream main is now `a5937595`** (the merge of PR #36). It
  carries `KERNEL_CONTRACT.json` (baseline `9c7b60ef`), `scripts/check_kernel_contract.py` and
  `scripts/audit_kernel.lean`. Three checks:
  1. **Same dependencies as upstream.** The import closure of every Contrib module has 538 project
     files, and all of them are byte-identical to `a5937595` (`git diff a5937595 HEAD` is empty on
     them). The `lean/` package's Lean files, `lakefile.toml`, `lake-manifest.json` and
     `lean-toolchain` are also identical. So the builds here are builds of the PR content on
     upstream main.
  2. **Contract classification.** `scratch/contrib-tidy/make-pr-commits.sh` uses git plumbing to
     build commit = `a5937595` + the PR's `.lean` files, creating no ref. For each such commit, I ran
     upstream's `check_kernel_contract.py --base-ref a5937595` in a temporary worktree. Both commits
     give `valid_candidate_contract`, route **`proof_only_astra_review`** and `lock_changed: []`.
  3. **Kernel audit.** I ran upstream's `audit_kernel.lean` (a verbatim copy is in
     `scratch/contrib-tidy/`) on each PR's module set. This replays the declarations through the
     kernel, walks the axiom closure and checks the exact provider types. Both runs **passed**:
     - PR 1: 514 declarations; **`heckeContinuation` and `functionalEquation5` have status
       `proved_exact_type`**.
     - PR 2: 93 declarations; no provider, as expected.

## Draft PR 1: `HeckeContinuation` and `FunctionalEquation5`

> **Title:** Contrib: prove `HeckeContinuation` and `FunctionalEquation5` (Gauss's point count and
> Hecke's theta series over ℤ[i])
>
> **Summary.** This PR closes two of the five registered premises of the conditional headline:
>
> ```lean
> theorem ZInQ.Contrib.heckeContinuation : ZInQ.Literature.HeckeContinuation
> theorem ZInQ.Contrib.functionalEquation5 : ZInQ.Literature.FunctionalEquation5
> ```
>
> Both are closed theorems with exactly the registered type and no hypotheses. Nothing outside
> `ZInQKernel/Contrib/` changes, and no baseline file is touched. The PR also adds a discharge
> theorem: the headline with these two premises removed.
>
> ```lean
> theorem ZInQ.Contrib.GaussFE.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagier
>     (hH : ZInQ.SixContactMin) (hA : ZInQ.Literature.TYZThm35ReadingA)
>     (hG : ZInQ.Literature.GrossZagier) : ZInQ.FrozenTarget
> ```
>
> **Mathematics.**
> - `HeckeFE/Basic.lean`, 2765 lines, namespace `ZInQ.Contrib.HeckeFE`.
>   - The weight-two theta kernels `Σ (m+a + i(n+b)) e^{−π|·|²x}` over shifted copies of ℤ[i] are
>     built from Mathlib's Hurwitz kernels. They form strong FE-pairs, so the twisted lattice series
>     `Σ_α c(α mod M) α N(α)^{−s}` have entire continuations (`twistedL_continuation`) and a
>     functional equation.
>   - The Hecke character `ψ_d` is completely multiplicative, with an Euler product.
>   - Deuring's identity `L(C_d, s) = L(ψ_d, s)` is proved for squarefree `d ≡ 1 (mod 4)`. It is
>     reduced to `GaussPointCount`, Gauss's count of `y² = x³ − x` over `𝔽_p` for `p ≡ 1 (mod 4)`.
>   - The Fourier identity comes from quadratic Gauss sums.
>   - Main result: `literature_hecke_fe_of_gaussPointCount : GaussPointCount →
>     HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5`.
> - `GaussFE/Gauss.lean`. Gauss's theorem through a quartic Jacobi sum `J(χ, χ²)` over ℤ[i]:
>   `#{y² = x³ − x} = p + 2A`, where `A + Bi = J`, `A² + B² = p` and `−J` is primary
>   (`gauss_jacobi`).
> - `GaussFE/FunctionalEquation5.lean`.
>   - Matches the two forms of the count: `GaussFE.gaussPointCount : HeckeFE.GaussPointCount`, with
>     no hypotheses.
>   - Closes `ZInQ.Contrib.functionalEquation5`.
> - `HeckeAll/LocalCd.lean`. Mathlib's `L(C_d, s)` for every squarefree `d`, odd or even. At `p = 2`
>   with `d` even, the model is shown minimal by a `c₄` valuation argument (`isMinimal_cdLocal'`,
>   `LSeries_cd_eq'`).
> - `HeckeAll/Iso.lean`. Mathlib's L-function does not change under a change of variables over ℚ
>   when `j` is integral. Hence `L(C_{m²d}, s) = L(C_d, s)` (`LSeries_cd_sq_mul`).
> - `HeckeAll/Continuation.lean`.
>   - The quadratic twist `cdCoeff d n = (d/n) · cdCoeff 1 n` (`cdCoeff_twist`).
>   - With Deuring at `d = 1`, this writes `L(C_d, s)` as a twisted lattice series mod `4d`, so it
>     has an entire continuation (`isLContinuation_of_squarefree`).
>   - `ZInQ.Contrib.heckeContinuation_of_gaussPointCount`.
> - `HeckeAll/Provider.lean`. `ZInQ.Contrib.heckeContinuation`.
> - `GaussFE/Headline.lean`.
>   - `certifiedRankTYZClRk_of_readingA_grossZagier`.
>   - The two discharge theorems `frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagier` and
>     `frozenTarget_of_sixContactMin_tyzInputs_grossZagier`.
>
> **Files** (8 new files, 4068 lines; only `.lean` under `ZInQKernel/Contrib/`):
> `HeckeFE/Basic.lean` (2765), `GaussFE/Gauss.lean` (408), `GaussFE/FunctionalEquation5.lean` (108),
> `GaussFE/Headline.lean` (37), `HeckeAll/LocalCd.lean` (297), `HeckeAll/Iso.lean` (150),
> `HeckeAll/Continuation.lean` (292), `HeckeAll/Provider.lean` (11).
>
> **Dependencies.** Mathlib, plus these baseline modules, all pinned and unchanged:
> - `ZInQKernel.RouteK.Rank.LFunctionCd`
> - `ZInQKernel.Hypotheses.CR3Literature`
> - `ZInQKernel.MainLiterature` (used only by `GaussFE/Headline.lean`)
>
> **Build** (Lean 4.35.0, Mathlib v4.35.0, the pinned toolchain):
> ```sh
> lake build ZInQKernel.Contrib.HeckeFE.Basic ZInQKernel.Contrib.GaussFE.Gauss \
>   ZInQKernel.Contrib.GaussFE.FunctionalEquation5 ZInQKernel.Contrib.GaussFE.Headline \
>   ZInQKernel.Contrib.HeckeAll.LocalCd ZInQKernel.Contrib.HeckeAll.Iso \
>   ZInQKernel.Contrib.HeckeAll.Continuation ZInQKernel.Contrib.HeckeAll.Provider
> ```
> Result: `Build completed successfully`, no errors. Wall times on a shared 192-core host with
> `LEAN_NUM_THREADS=8` and Mathlib already built: the `lake build` that first compiled
> `HeckeFE/Basic` took 4 min 25 s, and the first build of all Contrib modules took 6 min 20 s.
>
> Remaining warnings:
> - Two `unusedSectionVars` (`HeckeFE.norm_piZ`, `norm_conj_piZ`) and five in `GaussFE/Gauss.lean`
>   (`chi_pow_four`, `chi_neg_one_sq`, `chi_ne_one`, `chi_sq_ne_one`, `chi_cube_ne_one`). Fixing
>   them would change these lemmas' signatures; that can be done in a follow-up if wanted.
> - The `module`-system import notes that every file in the project gets.
>
> **Axioms.**
> ```
> 'ZInQ.Contrib.functionalEquation5' depends on axioms: [propext, Classical.choice, Quot.sound]
> 'ZInQ.Contrib.heckeContinuation' depends on axioms: [propext, Classical.choice, Quot.sound]
> 'ZInQ.Contrib.GaussFE.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagier' depends on
>   axioms: [propext, Classical.choice, Quot.sound]
> ```
> - Every one of the 389 declarations under `ZInQ.Contrib` uses only these three axioms.
> - Upstream's `scripts/audit_kernel.lean`, run on these 8 modules, gives `status: passed`:
>   - 514 declarations replayed, axioms used `[Quot.sound, Classical.choice, propext]`, no
>     runtime-only declarations;
>   - `ZInQ.Contrib.heckeContinuation`: `proved_exact_type`;
>   - `ZInQ.Contrib.functionalEquation5`: `proved_exact_type`;
>   - the other three providers: `open`.
> - `scripts/check_kernel_contract.py --base-ref a5937595` gives route
>   `proof_only_astra_review`, `lock_changed: []`.
>
> **Headline check.** This file, outside the PR, compiles:
> ```lean
> theorem contribCheck_headline (hH : ZInQ.SixContactMin) (hA : ZInQ.Literature.TYZThm35ReadingA)
>     (hG : ZInQ.Literature.GrossZagier) : ZInQ.FrozenTarget :=
>   ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier
>     hH hA ZInQ.Contrib.heckeContinuation ZInQ.Contrib.functionalEquation5 hG
> -- 'contribCheck_headline' depends on axioms: [propext, Classical.choice, Quot.sound]
> ```
>
> **Commit built.**
> - Fork branch `wip/contrib-tidy`. The Contrib sources are those of `68c0411e`, and the same files
>   were checked at the report commit. The PR's file set is unchanged since `68c0411e`.
> - PR commit = upstream main `a5937595` + these files, made by
>   `scratch/contrib-tidy/make-pr-commits.sh`: `b4bbf5dd` (dangling, with fixed author and date,
>   so it is reproducible).
> - The import closure is byte-identical between the fork and `a5937595`.
>
> **Provenance.** The Lean code was written by AI agents (Claude, Anthropic; model `claude-opus-5-5`):
> - the bp-hecke-fe, gauss-proof and hecke-all tasks wrote the proofs;
> - the contrib-tidy task deduplicated them and cleaned the lint.
>
> A human has not reviewed the proofs. Lean's kernel checks them. The statements proved are the
> registered `ZInQ.Literature` propositions, which this PR does not touch.

## Draft PR 2: `PSide`, the coefficients and convergence of `L(C_d, s)`

> **Title:** Contrib: coefficients, Hasse bound and absolute convergence of `L(C_d, s)`; `TYZInputs`
> is equivalent to reading A
>
> **Summary.** These are helper results about Mathlib's L-function of
> `C_d : y² = x³ − d²x` and about the TYZ encoding. The PR closes no registered premise, adds no
> provider and changes nothing outside `ZInQKernel/Contrib/PSide/`. It does not depend on PR 1.
>
> **Exact declarations** (namespace `ZInQ.Contrib.PSide`; `d` is odd squarefree where Mathlib's
> `LFunction` appears):
> ```lean
> -- P1 (APZero.lean)
> theorem LFunction_cd_apply_prime_of_mod_four_eq_three {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
>     (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) (hp : ¬ p ∣ 2 * d) :
>     (shortCurve (-(d : ℚ) ^ 2)).LFunction p = 0
> theorem natCard_point_cd_of_mod_four_eq_three {d : ℕ} (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3)
>     (hp : ¬ p ∣ 2 * d) :
>     Nat.card (shortCurve (-(d : ZMod p) ^ 2)).toAffine.Point = p + 1
> -- P2 (Coeff.lean)
> theorem LFunction_cd_eq_cdCoeff {d : ℕ} (hd : Odd d) (hsq : Squarefree d) (n : ℕ) :
>     (shortCurve (-(d : ℚ) ^ 2)).LFunction n = cdCoeff d n
> theorem LFunction_cd_prime_pow_succ_succ {d : ℕ} (hd : Odd d) (hsq : Squarefree d) {p : ℕ}
>     (hp : p.Prime) (h : ¬ p ∣ 2 * d) (k : ℕ) :
>     (shortCurve (-(d : ℚ) ^ 2)).LFunction (p ^ (k + 2)) =
>       (shortCurve (-(d : ℚ) ^ 2)).LFunction p * (shortCurve (-(d : ℚ) ^ 2)).LFunction (p ^ (k + 1))
>         - p * (shortCurve (-(d : ℚ) ^ 2)).LFunction (p ^ k)
> -- P3 (BadPrimes.lean)
> theorem LFunction_cd_apply_prime_eq_sub_card_all {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
>     (p : ℕ) [Fact p.Prime] :
>     (shortCurve (-(d : ℚ) ^ 2)).LFunction p =
>       p - Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1}
> -- P4 (Hasse.lean, Convergence.lean)
> theorem cdCoeff_prime_sq_le (d : ℕ) {p : ℕ} (hp : p.Prime) : cdCoeff d p ^ 2 ≤ 4 * p
> theorem LFunction_cd_prime_sq_le {d : ℕ} (hd : Odd d) (hsq : Squarefree d) {p : ℕ}
>     (hp : p.Prime) : (shortCurve (-(d : ℚ) ^ 2)).LFunction p ^ 2 ≤ 4 * p
> theorem LSeriesSummable_cd {d : ℕ} (hd : Odd d) (hsq : Squarefree d) {s : ℂ}
>     (hs : 3 / 2 < s.re) :
>     LSeriesSummable ((↑) ∘ (shortCurve (-(d : ℚ) ^ 2)).LFunction) s
> theorem abscissaOfAbsConv_cd_le {d : ℕ} (hd : Odd d) (hsq : Squarefree d) :
>     LSeries.abscissaOfAbsConv ((↑) ∘ (shortCurve (-(d : ℚ) ^ 2)).LFunction) ≤ (3 / 2 : ℝ)
> theorem differentiableOn_LSeries_cd {d : ℕ} (hd : Odd d) (hsq : Squarefree d) :
>     DifferentiableOn ℂ (shortCurve (-(d : ℚ) ^ 2)).LSeries {s : ℂ | 3 / 2 < s.re}
> -- P5 (TYZInputsIff.lean)
> theorem tyzInputs_iff_readingA :
>     TYZInputs ↔ TYZThm35ReadingA ∧ ∀ n : ℕ, n % 8 = 5 → Squarefree n →
>       (∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(n : ℚ) ^ 2)) F) ∨
>         (T5aCl n = 0 ∧ T5bCl n = 0)
> theorem tyzInputs_iff_readingA_of_hecke (hH : HeckeContinuation) :
>     TYZInputs ↔ TYZThm35ReadingA
> theorem tyzInputs_of_readingA (hA : TYZThm35ReadingA) (hH : HeckeContinuation) : TYZInputs
> ```
>
> Further results:
> - `Coeff.lean`: the `cdCoeff` API, including `cdCoeff_mul`, `isMultiplicative_cdArith` and
>   `cdCoeff_prime_pow_succ_succ`.
> - `Hasse.lean`: Hasse's bound by Jacobsthal sums (`jac_sq_le_four_mul`).
> - `Convergence.lean`: `recurrence_bound`, `cdCoeff_sq_le`.
> - `Supersingular.lean`: `cdCoeff_prime_pow_of_mod_four_eq_three` (`c_{p^{2k}} = (−p)^k` and
>   `c_{p^{2k+1}} = 0` for `p ≡ 3 (mod 4)`).
>
> Each module's docstring lists its results.
>
> **Files** (7 new files, 1003 lines): `PSide/APZero.lean` (121), `PSide/BadPrimes.lean` (90),
> `PSide/Coeff.lean` (162), `PSide/Hasse.lean` (242), `PSide/Convergence.lean` (189),
> `PSide/Supersingular.lean` (48), `PSide/TYZInputsIff.lean` (151).
>
> **Dependencies.** Mathlib, plus the pinned and unchanged baseline modules
> `ZInQKernel.RouteK.Rank.LFunctionCd` and `ZInQKernel.RouteK.PropN`.
>
> **Build:**
> ```sh
> lake build ZInQKernel.Contrib.PSide.APZero ZInQKernel.Contrib.PSide.BadPrimes \
>   ZInQKernel.Contrib.PSide.Coeff ZInQKernel.Contrib.PSide.Convergence \
>   ZInQKernel.Contrib.PSide.Hasse ZInQKernel.Contrib.PSide.Supersingular \
>   ZInQKernel.Contrib.PSide.TYZInputsIff
> ```
> Result: `Build completed successfully`, no errors. The only warnings are the `module`-system
> import notes.
>
> **Axioms.**
> ```
> 'ZInQ.Contrib.PSide.tyzInputs_iff_readingA' depends on axioms: [propext, Classical.choice, Quot.sound]
> 'ZInQ.Contrib.PSide.LSeriesSummable_cd' depends on axioms: [propext, Classical.choice, Quot.sound]
> ```
> - All 67 declarations under `ZInQ.Contrib.PSide` use only these three axioms.
> - Upstream's `audit_kernel.lean`, run on the 7 modules, gives `status: passed`: 93 declarations,
>   axioms `[Quot.sound, Classical.choice, propext]`, all providers `open`.
>   - The headline and `SixContactMin` lie outside this PR's import closure. For this run only, the
>     spec's headline entry pointed at `tyzInputs_iff_readingA`, and the `SixContactMin` target was
>     dropped.
> - `check_kernel_contract.py --base-ref a5937595` gives `proof_only_astra_review`,
>   `lock_changed: []`.
>
> **Commit built.**
> - Fork `wip/contrib-tidy`, with Contrib sources as of `68c0411e`.
> - PR commit = `a5937595` + `PSide/*.lean`: `28a66a98` (dangling, reproducible with
>   `scratch/contrib-tidy/make-pr-commits.sh`).
>
> **Provenance.** The Lean code was written by AI agents (Claude, Anthropic; model `claude-opus-5-5`):
> - the p-side task wrote the proofs;
> - the contrib-tidy task made the lint fixes.
>
> A human has not reviewed the proofs. Lean's kernel checks them.

## How to open the PRs (not done here)

1. Run `scratch/contrib-tidy/make-pr-commits.sh HEAD pr/contrib-hecke-fe pr/contrib-pside`. It
   creates the two branches on top of `a5937595`.
2. Push them and open the PRs against `elliotglazer/diophantine-z-q` `main`.

Each PR must contain only `.lean` files under `ZInQKernel/Contrib/`. Any other changed path, such as
these notes or `scratch/`, moves the PR to `statement_or_infrastructure_review`. If upstream `main`
has moved past `a5937595`, rebase. The pinned closure may also have changed, in which case rebuild.

## Files

- `scratch/contrib-tidy/`:
  - `log.md`
  - `modules.txt`: the 15 Contrib modules
  - `wrap.py`: the line-wrapping edits
  - `Types.lean`: exact provider types
  - `AllAxioms.lean` with `allaxioms-1.txt`
  - `Names.lean` with `names-output.txt`. Every constant is under `ZInQ.Contrib` except private
    names and three auto-generated equation lemmas (`*.eq_1`, `PeriodPair.mk.congr_simp`), which
    the upstream audit treats as mergeable duplicates.
  - `audit_kernel.lean` (upstream's, verbatim) with `spec-pr{1,2}.json` and `audit-pr{1,2}.json`
  - `contract-pr{1,2}.json`
  - `make-pr-commits.sh`
  - `decls.md`: every declaration name, by file
  - `check-1.txt`: output of `Check.lean`
- `scratch/contrib-check/Check.lean`: unchanged.
- **Not updated.** The task notes `docs/research/gauss-proof.md` and `hecke-all.md` still name
  `GaussFE/HeckeFE.lean` and `HeckeAll/HeckeFE.lean`. Both are now `Contrib/HeckeFE/Basic.lean`.
  Those notes belong to other tasks.
