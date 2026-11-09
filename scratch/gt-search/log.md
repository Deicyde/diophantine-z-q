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
