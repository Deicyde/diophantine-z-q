# gt-search log

Started 2026-11-09. Task: find Lean formalizations of Green-Tao / relative Szemeredi; import plan; scope Prop D.

## Network reachability (2026-11-09, plain curl, 15 s timeout)
- export.arxiv.org API: HTTP 200 (works).
- github.com, api.github.com, raw.githubusercontent.com, leanprover-community.github.io (Zulip archive),
  leanprover.zulipchat.com API, vilin97.github.io, gitlab.com, codeberg.org: no connection (curl code 000),
  also through the configured HTTP proxy (code 000). pypi.org reachable through proxy only.
- gh CLI: stored token invalid; no GitHub API access.
- WebFetch tool: ECONNRESET on vilin97.github.io.
- external web search tool (titles + URLs only, no page text): works.
=> Primary sources on GitHub/Zulip can't be read from here. Evidence comes from (a) web search
   result titles/URLs, (b) arXiv abstracts and TeX sources, (c) local Mathlib checkout at 56a00585.

## Searches
- Local Mathlib 56a00585 (from ~/dzq-wt/ap-lean/.lake/packages/mathlib): docs/1000.yaml entry Q922012
  "Green–Tao theorem" has no decl/url (unformalized in Mathlib's list); Q1046232 "Szemerédi's theorem" also
  no decl. docs/overview.yaml lists only Szemerédi regularity, triangle removal etc. VERIFIED locally.
- web search "Lean 4 formalization of the Green-Tao theorem": only expository pages, arXiv 2603.09281
  (Green-Tao for sparse sets, math), Mathlib docs/1000.yaml. No formalization.
- web search "Vasily Ilin Green-Tao theorem Lean formalization": nothing relevant (AI-formalization blogs).
- web search "\"Green-Tao\" Lean github formalized primes arithmetic progressions": google-deepmind/
  formal-conjectures issue 2446 (title only "Issues"), expository pages. No formalization.
- web search "relative Szemerédi theorem formalized in Lean 4": only Szemerédi regularity lemma
  (Dillies-Mehta ITP 2022, Isabelle Roth). Nothing relative.
- web search "Lean Zulip Green-Tao theorem formalization project": unrelated Zulip threads.
- web search "Vilin97 GreenTao repository": nothing.
- web search "Szemerédi's theorem formalized Lean 2026": leanprover-community 1000-missing.html,
  regularity lemma papers. Nothing.
- web search "AI autoformalization Green-Tao theorem Lean proof completed": news on other AI
  results (Axiom CFSG, OpenAI zeta zero-free regions); nothing on Green-Tao.
- web search "Gowers uniformity norm Lean mathlib formalization": only math papers.
- web search "Math Inc Gauss formalized Green-Tao theorem", "\"formalisation of the Green-Tao theorem\"",
  "Green-Tao theorem Lean sorry-free proof 2026 ...", "Harmonic Aristotle Green-Tao theorem formalization":
  nothing relevant.
- arXiv API (export.arxiv.org) queries, 2026-11-09: all:"Green-Tao" AND all:Lean -> 0;
  "Green-Tao" AND formalization -> 0; "Green-Tao" AND formalized -> 0; "relative Szemeredi" AND Lean -> 0;
  Szemeredi AND Lean AND formalization -> 0; "arithmetic progressions" AND primes AND Lean -> 1
  (2503.00959 "Formalizing zeta and L-functions in Lean", Loeffler-Stoll, not Green-Tao);
  "lean-eval" -> 3 unrelated agent papers; "Lean Pool" -> 2609.25199.
- arXiv 2609.25199 (Vasily Ilin, "Lean Pool: An AI-Maintained Archive of Formalized Mathematics",
  submitted 2026-09-21): downloaded TeX source (e-print). Searched all 451 hrefs and the bibliography
  for green/tao/szemer/progression/prime/gowers/sieve. Prime-related projects listed: Selberg sieve
  (amellendijk/selberg-sieve4), AxiomMath/partial-regularity, AxiomMath/ramanujan-tau-misses-primes,
  ElNando888/KrafftSieve, openai/LongGapsBetweenPrimes, flt-regular. No Green-Tao, no Szemerédi,
  no relative Szemerédi. Ilin's own repos listed: lean-pool, Clawristotle, MazurTheorem,
  homotopy-groups-lean, Autoformalization. VERIFIED (paper source).
- web search "Vasily Ilin twitter Green-Tao formalized", "lean-pool GreenTao vilin97.github.io",
  "primes contain arbitrarily long arithmetic progressions Lean ... github",
  "Conlon Fox Zhao relative Szemerédi Lean formalization dense model theorem": nothing relevant
  (found the Reservoir page reservoir.lean-lang.org/@LeanPool/lean-pool, title only).
- Hugging Face API search (datasets/models/spaces) for green-tao, greentao, green_tao, lean-pool,
  leanpool, lean-eval, Vilin97, szemeredi: no Green-Tao artefact. Vilin97 on HF: datasets KilterBoard,
  Clawristotle-Logs, space VeriDeepResearch.
- Source archives of public GitHub repos CAN be downloaded here at exact commits (no code search, no
  listing of a user's repos). Used below.
- Vilin97/lean-pool, branch main at commit 9c7629e5549220179437cc258a5b0787257d4d54 (2026-09-29; latest
  tag v4.34.0 = 374d6870, 2026-09-15). Lean v4.34.0, Mathlib v4.34.0. License Apache-2.0.
  250 projects in LeanPool/projects.yml. grep -i "green.?tao|GreenTao|relative.?szemer|szemer" over the
  whole tree: hits only LeanPool/DensityHalesJewett/* (Szemerédi's theorem, see below), PFR files
  (Ruzsa distance, BSG), candidates/shortlist.md (Bourgain extractor / Szemerédi–Trotter; Erdős 1196
  Erdős–Sárközy–Szemerédi), candidates/decisions.jsonl (leanprover/lean-eval-leaderboard: "250+
  problem-statement stubs (FermatLastTheorem, RiemannHypothesis, Szemeredi...) each ':= by sorry'").
  NO Green-Tao and no relative Szemerédi in Lean Pool at this commit. VERIFIED.
- LeanPool/lean-pool (the organisation copy, newer): archive too large to download (>500 MB); not checked.
- FOUND: Lean Pool project "densityhalesjewett" (Gabriel Dahia; upstream gdahia/densityhalesjewett commit
  1c2f5aa1b99caa8e2a87beacf80f07f066c309d3, commit time 2026-09-17; Apache-2.0; projects.yml
  "status: verified", "provenance: AI"). 4426 lines. Density Hales–Jewett (DKT proof) =>
  Szemerédi's theorem `Combinatorics.ArithmeticProgression.exists_of_density_nat_atTop` and the
  Varnavides count `Combinatorics.ArithmeticProgression.exists_many_of_density_nat`
  (LeanPool/DensityHalesJewett/DensityHalesJewett/Varnavides.lean:296). Not Green-Tao (needs density
  in ℕ), but it is the combinatorial black box of the transference proofs.
  The upstream repo archive itself could not be fetched ("not found", version-control timestamp
  2026-09-17 14:55:36 confirmed for 1c2f5aa).
- Guessed repo names (green-tao, greentao, GreenTao, green_tao, relative-szemeredi, GreenTaoTheorem,
  szemeredi) under gdahia, Vilin97, LeanPool, YaelDillies, b-mehta, AxiomMath, teorth: none exist.
- YaelDillies/LeanAPAP exists (tag v4.34.0, 26a124f5, 2026-09-17): Kelley–Meka 3-AP bounds, not Green-Tao.
- math-inc/FormalQualBench main = efaa113c6a00a79e92842ce541b407d7695d7699 (2026-03-19), Lean v4.28.0,
  Apache-2.0: FormalQualBench/GreenTaoTheorem/Main.lean is a `sorry` stub
  `theorem MainTheorem : ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i : Fin k, Nat.Prime (a + i.1 * d)`. VERIFIED.
- arXiv 2605.26959 (MerLean-Prover; TeX source): FormalQualBench table: GreenTaoTheorem is among the
  13 problems NOT closed by MerLean. arXiv 2610.35962 (h1; TeX source): 14/23 FormalQualBench, no
  per-problem list, no mention of Green-Tao.
- web search "FormalQualBench results Green-Tao theorem solved by agent", "FormalQualBench leaderboard",
  "OpenGauss FormalQualBench solved problems list GreenTaoTheorem", "\"GreenTaoTheorem\" Lean proof",
  "LeanTriathlon Green-Tao numina": no solution found.
- project-numina/LeanTriathlon 2aede4209c203ae9901eff870744e4b77dc6173f (2026-06-27): only
  LiveLeanTriathlonSorry/GreenTaoTheorem/All.lean (sorry statement).
- google-deepmind/formal-conjectures main 84cf7f8adfb0ea8d14c7d00bdf145cc9032bdf88 (2026-10-14):
  mentions Green-Tao only in ErdosProblems/3.lean and 210.lean (see doc).
- math-inc/OpenGauss, Koerbser/erdos-3-autolab, gdahia/densityhalesjewett: exist (commit lookups
  answer) but their source archives could not be produced; not inspected.
- *** leanprover/lean-eval main 38361be884302c7edce1908c4aef8296eb2cb27e (2026-10-07), Lean
  v4.35.0-rc3, Apache-2.0: problem `green_tao` (LeanEval/NumberTheory/GreenTao.lean, submitter Kim
  Morrison): `theorem green_tao : ContainsArbitraryAPs {p : ℕ | Nat.Prime p}` with
  `def ContainsArbitraryAPs (A : Set ℕ) : Prop := ∀ k : ℕ, ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ A`.
  audits/v1/selection-2026-08-20.md: green_tao solves 2 (issues 907, 1052), first accepted
  2026-08-01T07:07:21Z.
- *** leanprover/lean-eval-submissions main e6cee4be3b6ce6f7625c5a2914a090be1ff24729 (2026-10-14),
  results/*.json: SEVEN comparator-accepted green_tao results (all with submission.public = false):
    1. Vilin97 (Vasily Ilin), accepted 2026-08-01T07:07:21Z, model gpt-5.6-Sol, issue 907,
       repo Vilin97/lean-eval-green-tao @ 0c5d3337c3ebb59c318ab9030e31b835826141f8, benchmark commit
       3f3786f3b4d9a4b64a5859b3036aca190cd25613. production_description: "Produced autonomously by
       gpt-5.6-Sol in Codex, with human direction. Builds on Mathlib and LeanEval's transference/majorant
       framework, adding a source-full ordered hypergraph-removal assembly. The submitted source contains
       no sorry, admit, added axioms, set_option, or native_decide."
    2. ZhengyangZhang06, 2026-08-16T10:52:12Z, "Humanifa + GPT 5.6 sol", issue 1052, humanfia/lean-eval
       @ ab2e8d68a5e4e07055f919e0e38bb43bf53a252b, publication "planned" 2026-08-31.
    3. Vilin97 file also: Axiom Prover (Axiom Math), 2026-08-29T06:44:34Z, issue 1481,
       AxiomMath/lean-eval-submissions-final @ b092f7455ac0cf0c405e42fbb669ef8144de9fd9, private.
    4. lukerj00, Tau (caj.al), 2026-09-05T18:47:17Z, lukerj00/tau-lean-eval-submission @ 04868934, private.
    5. skidanovalex, NEAR AI w/ DeepSeek V4, 2026-09-16T02:40:44Z, SkidanovAlex/leaneval-deepseek @ 865b8d22.
    6. sarjinius, Midas, 2026-09-27T20:24:03Z, midas-intelligence/midas-leaneval-submission @ 87b09d3b, private.
    7. ma4ypic4y, max gp (GPT-6 / gpt-6.1-sol), 2026-10-12T13:11:02Z, ma4ypic4y/lean-eval-top1 @ f0705867,
       "92 submitted Lean sources", private.
  None of these seven repositories is publicly readable now (all lookups: git ls-remote fails = private
  or deleted). VERIFIED (records read from results JSON).
- Hugging Face dataset humanfia-lab/lean-eval-source @ 6a6d9f67a91d546677321aeea559c2857b697635
  (2026-08-18; green_tao workspace unchanged since 2528f9e2, 2026-08-08): problems/green_tao/ =
  Humanize attempt, 15370 lines, Lean v4.32.0-rc1, Mathlib 360da6fa. Submission.lean:
  `by_cases hk : k ≤ 27; · exact Lucas.primeAP_of_le_twenty_seven k hk; · sorry` -> INCOMPLETE
  (pre-acceptance snapshot). License: "UNLICENSED © Zijian Zhang". VERIFIED (downloaded).
- humanfia snapshot green_tao: components are conditional reductions specialised to the primes
  (`prime_progression_of_uniform_dense_model`, `prime_progression_of_selberg_apDual_pseudorandom`,
  `contains_of_wTrickedPrimes`, ...); no general relative Szemerédi theorem; the final step is `sorry`.
  Not built (incomplete, unlicensed, needs Mathlib 360da6fa which is not available here).
- lean-eval-submissions README (e6cee4be): server submissions default to "scheduled" publication:
  "Accepted scheduled source is released under Apache License 2.0 exactly two UTC calendar months after
  acceptance." The results JSON does not record the publication choice. Legacy issue submissions
  (Vilin97 #907, humanfia #1052, Axiom #1481, ...) have no required embargo and no automatic release.
  Server-intake green_tao results: skidanovalex (accepted 2026-09-16 -> earliest scheduled release
  2026-11-16 if "scheduled" was chosen; UNVERIFIED whether it was).
- Mathlib 56a00585 (local): Dirichlet series lower bound for primes in a class
  `ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound`, continuation
  `continuousOn_LFunctionResidueClassAux`, Dirichlet's theorem `Nat.forall_exists_prime_gt_and_modEq`,
  `Nat.infinite_setOf_prime_and_modEq`; Selberg sieve set-up `Mathlib/NumberTheory/SelbergSieve.lean`
  (`BoundingSieve`, `SelbergSieve`, `siftedSum_le_mainSum_errSum_of_upperMoebius`,
  `upperMoebius_lambdaSquared`, `mainSum_lambdaSquared_eq_sum_mul_sum_sq`); Chebyshev bounds
  `Chebyshev.theta_le_log4_mul_x`, `theta_ge`, `primeCounting_eq_theta_div_log_add_integral`;
  `Nat.Prime.sq_add_sq`, GaussianInt; Jacobi sums `jacobiSum_mul_jacobiSum_inv`,
  `exists_jacobiSum_eq_neg_one_add`, `gaussSum_pow_eq_prod_jacobiSum`. No Brun–Titchmarsh, no PNT in APs,
  no Mertens. VERIFIED by grep.
- PrimeNumberTheoremAnd main = tag v4.34.0 = c39a751132c88b6e8080b74c74023fd95b3d8be0 (2026-10-01),
  Lean v4.34.0, Apache-2.0: `WeakPNT_AP` (Wiener.lean:4025; ψ(N;q,a)/N → 1/φ(q)), `WeakPNT_AP_prelim`,
  `dirichlet_thm`, `chebyshev_asymptotic` (Consequences.lean:177), Brun–Titchmarsh for intervals
  `BrunTitchmarsh.primesBetween_le` (BrunTitchmarsh.lean:248), Selberg sieve bound
  `SelbergSieve.selberg_bound_simple` (Mathlib/NumberTheory/Sieve/Selberg.lean:435), Mertens' first
  theorem `sum_mangoldt_div_eq_log`, `E₁Λ.bounded` (IEANTN/Mertens.lean). Wiener.lean has 2 sorries
  (`prelim_decay_2`, `prelim_decay_3`), used only by `decay_alt` -> IEANTN/CH2; static grep says
  `WeakPNT_AP` does not use them (NOT verified by #print axioms: no Mathlib v4.34 build available).
  No Gaussian-integer sieve, no Hecke/Chebotarev proof (Chebotarev section is blueprint prose).
- BUILD (2026-11-09 16:01, load 6, 110 GB free): Lean Pool LeanPool/DensityHalesJewett (17 modules, all
  files from Vilin97/lean-pool 9c7629e5, unchanged) compiled with plain `lean` v4.35.0 one module at a
  time against the local Mathlib 56a00585 oleans: all 17 modules OK, 0 warnings, ~35 s total.
  `#print axioms` (~/gt-builds/dhj/Axioms.lean): exists_of_density_nat_atTop, exists_many_of_density_nat,
  Line.exists_of_density_atTop, exists_of_density_nat: [propext, Classical.choice, Quot.sound].
  No `sorry`/`axiom`/`native_decide` in the sources. VERIFIED. So Szemerédi + Varnavides port to our
  pinned versions with zero changes.
- *** google-deepmind/formal-conjectures 84cf7f8a: FormalConjectures/ErdosProblems/219.lean
  `theorem erdos_219 : ∀ N : ℕ, ∃ l ∈ primeArithmeticProgressions, N ≤ ENat.card l` (Green–Tao 1.1)
  is tagged `formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/1268917deaaaa0d674f651287027baa26cea9920/src/latest/ErdosProblems/Erdos219.lean"`;
  ErdosProblems/1187.lean `erdos_1187.parts.i` (monochromatic k-APs of primes in every finite colouring
  of ℤ; the docstring derives it from the dense-subset Green–Tao) is tagged `formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1187.lean#L246"`.
  Erdős 3 `erdos_3.variants.green_tao` is the r_4 bound (sorry); Erdős 210 is Green–Tao ordinary lines.
- web search "plby lean-proofs Erdos219 Green-Tao formal proof": nothing beyond formal-conjectures PRs.
- arXiv 2606.05400 (LeanMarathon; TeX source): no Green–Tao (Szemerédi hits are Erdős 1196/1217).
- plby/lean-proofs: first archive request timed out (large repository); retrying.
