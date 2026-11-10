# gt-search report: Lean formalizations of Green–Tao, import plan, Proposition D scope

Full write-up: `docs/research/gt-search.md`. Search log, with every query including the empty ones:
`scratch/gt-search/log.md`. No file in `ZInQKernel/` was edited.

## Summary

- **Jack is right.** Vasily Ilin (`Vilin97`) has a complete Lean proof of Green–Tao. It is the first
  accepted solution of the lean-eval problem `green_tao`, accepted 2026-08-01, model gpt-5.6-Sol in
  Codex "with human direction", described as having no sorry, no added axioms and no
  native_decide. The source repository `Vilin97/lean-eval-green-tao` @ `0c5d3337` is
  **private**. Six more accepted solutions exist (Humanfia + GPT 5.6 Sol, Axiom Prover, Tau, NEAR AI
  with DeepSeek V4, Midas, "max gp" GPT-6). All seven repositories are private. Source: the
  `results/*.json` records of `leanprover/lean-eval-submissions` @ `e6cee4be`.
- All seven prove **only Theorem 1.1** (the primes). The comparator-fixed statement is
  `theorem green_tao : ContainsArbitraryAPs {p : ℕ | Nat.Prime p}`, with
  `ContainsArbitraryAPs A := ∀ k, ∃ a b, 1 ≤ b ∧ ∀ j < k, a + b * j ∈ A`. Our 22P_AP needs Theorem 1.2
  (dense subsets).
- **Unread public lead:** `formal-conjectures` @ `84cf7f8a` links formal proofs of Erdős 219
  (Theorem 1.1) and Erdős 1187(i) (monochromatic prime progressions; on paper this comes from
  Theorem 1.2) in `plby/lean-proofs` (`Erdos219.lean` @ `1268917d`, 2026-09-07; `Erdos1187.lean` @
  `8822f7dd`). The repository is too large for the access I had, so this needs reading from a
  machine with GitHub access.
- **Verified component:** Lean Pool's `LeanPool.DensityHalesJewett` (Gabriel Dahia, AI-produced,
  Apache-2.0, `Vilin97/lean-pool` @ `9c7629e5`) proves Szemerédi's theorem
  (`Combinatorics.ArithmeticProgression.exists_of_density_nat_atTop`) and the Varnavides count
  (`exists_many_of_density_nat`). I compiled all 17 files unchanged against Lean 4.35.0 and Mathlib
  `56a00585`: no errors, no warnings. `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
  It is the finitary input of the transference proofs, not Green–Tao.
- **Other finds:** a public Humanfia snapshot of a `green_tao` attempt (Hugging Face
  `humanfia-lab/lean-eval-source` @ `6a6d9f67`). It is incomplete: the proof is
  `k ≤ 27` by explicit progressions plus `sorry` otherwise, and the licence is "UNLICENSED".
  `sorry` stubs exist in FormalQualBench, LeanTriathlon and lean-eval. Mathlib has no Green–Tao
  and no Szemerédi.

## Candidates and their statements

| Candidate | Where, revision | Licence | Authors / AI | Complete? | Lean / Mathlib | Statement | 1.2? |
| --- | --- | --- | --- | --- | --- | --- | --- |
| lean-eval #1 | `Vilin97/lean-eval-green-tao` @ `0c5d3337c3ebb59c318ab9030e31b835826141f8` (private) | none published | Vasily Ilin; gpt-5.6-Sol in Codex | accepted by comparator (axioms ⊆ propext, Quot.sound, Classical.choice) | lean-eval benchmark `3f3786f3` (Aug 2026, probably Lean 4.32.0-rc1) | `green_tao` above | no; small extension if its relative Szemerédi step takes a general `f ≤ ν` |
| lean-eval #2–#7 | see doc §1.1 table (all private) | none published | Humanfia, Axiom Math, Tau, NEAR AI, Midas, ma4ypic4y; all AI | accepted | #7 checked on `v4.35.0-rc3` | same | no |
| plby Erdos219/1187 | `plby/lean-proofs` @ `1268917d…` / `8822f7dd…` (public, unread) | unknown | Boris Alexeev's repository (presumed); unknown AI use | per formal-conjectures tag; not checked | unknown | `erdos_219`: `∀ N, ∃ l ∈ primeArithmeticProgressions, N ≤ ENat.card l`; `erdos_1187.parts.i` (colouring) | possibly inside 1187 |
| Humanfia snapshot | HF `humanfia-lab/lean-eval-source` @ `6a6d9f67` | UNLICENSED | Zijian Zhang / Humanize workflow | **no** (`sorry` for `k > 27`) | 4.32.0-rc1 / `360da6fa` | `green_tao` | no |
| Lean Pool DHJ | `Vilin97/lean-pool` @ `9c7629e5` | Apache-2.0 | Gabriel Dahia; AI | **yes, built here** | 4.34.0, also builds on 4.35.0 / `56a00585` | Szemerédi in ℕ (doc §1.5) | no (component) |

## Recommendation

1. Ask Vasily Ilin for `lean-eval-green-tao` @ `0c5d3337` under Apache-2.0, and ask whether its
   relative Szemerédi theorem is stated for a general weight `0 ≤ f ≤ ν`. Its description,
   "transference/majorant framework, … ordered hypergraph-removal assembly", suggests a
   Conlon–Fox–Zhao-type proof. In parallel, read `plby/lean-proofs` `Erdos1187.lean`, which may
   already contain Theorem 1.2.
2. Import by **vendoring**, not by a Lake `require`. Lake allows one Mathlib per build, so a
   `require` only works if the dependency is pinned to our Mathlib commit. Keep the Apache headers,
   add a `THIRD_PARTY_NOTICES.md` entry, and port from about 4.32 to 4.35.0. By Lean Pool's upgrade
   statistics this is a few hundred changed lines for a 15–20k-line proof. Then prove
   `GreenTaoDense` (Theorem 1.2) by redoing the density step for a dense set `A`: pigeonhole over
   W-classes with `f = (φ(W)/W) log(Wn+b) 1_A(Wn+b) ≤ ν`.
3. The hypothesis that replaces `ZInQ.GoodPrimeAP`:
   `GoodPrimeDensity := PrimesRelUpperDensityPos {p | ZInQ.GoodSlopePrime p}`, where
   `PrimesRelUpperDensityPos A := ∃ c > 0, ∃ᶠ N in atTop, c * π(N) ≤ #(A ∩ [0, N])`. The reduction
   `GTSearch.progressions_above_of_greenTaoDense` (GreenTaoDense + density ⇒ the exact shape of
   `GoodPrimeAP`, with `S := Mult.S_b`) is in `scratch/gt-search/GreenTaoReduction.lean`. It compiles
   against our Mathlib, and `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
4. **Proposition D in Lean** (doc §4) needs five pieces:
   - (D1) The CM point count for `y² = x³ − d²x`: the twist relation plus Gauss's quartic Jacobi
     sum evaluation. Mathlib has the Jacobi sum ingredients but not the evaluation. About 1.5–3k
     lines.
   - (D2) Primes in the main classes. Mathlib's
     `ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound` is enough for Dirichlet
     density; PrimeNumberTheoremAnd `WeakPNT_AP` (Lean 4.34) would give natural density. Plus a
     Mertens product bound. About 1k lines.
   - (D3) Uniform Brun–Titchmarsh for Gaussian primes modulo `ℓ`, as a two-dimensional instance of
     the Selberg sieve (Mathlib `BoundingSieve`/`SelbergSieve`; PrimeNumberTheoremAnd
     `SelbergSieve.selberg_bound_simple`, `BrunTitchmarsh.primesBetween_le` as template). Not in
     either library. About 3–5k lines, and the hardest piece.
   - (D4) The lattice count for `ℓ > N^{1/8}`, which is elementary.
   - (D5) The assembly.

   **Positive Dirichlet density is the easier target.** It needs only our Mathlib for (D2) and (D5),
   and it implies positive relative upper density, which is all Theorem 1.2 needs. It does not
   remove (D1) or (D3). Total: about 6–10k lines (an estimate, not a measurement).

## Limits of this run

- GitHub search and API, the Lean Zulip archive, GitLab and Codeberg could not be queried here.
  So the project's earlier GitHub sweeps were not repeated, and the seven private repositories,
  `plby/lean-proofs` and the organisation copy `LeanPool/lean-pool` were not read.
- PrimeNumberTheoremAnd's `WeakPNT_AP` was not checked with `#print axioms`: I had no Mathlib
  `v4.34` build. A static grep says the two `sorry`s in `Wiener.lean` are not on its path.
- Lean runs: three short single-process `lean` runs (the DHJ build of about 35 s, two axiom checks
  and the scratch file). Load was at most 6 and at least 110 GB of memory was free; I was never
  blocked.
- Commits are local. The push is left to the background job.
