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
