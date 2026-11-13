# Lean formalizations of the Green–Tao theorem, and what replacing 22P_AP would take

Task `gt-search`, 2026-11-09. The search log, with every query and its result, is
`scratch/gt-search/log.md`. Labels: **VERIFIED** means I downloaded the file at the stated
revision and read it, or built it; **METADATA** means the claim comes from a public record
(a results file or a manifest) that I read, but the Lean source behind it was not available to me;
**UNREAD** means the source exists but I could not obtain it.

## Summary

- Jack's recollection is right. Vasily Ilin (GitHub `Vilin97`) has a complete Lean proof of the
  Green–Tao theorem: it is the first accepted solution of the `green_tao` problem of the lean-eval
  benchmark, accepted on 2026-08-01, "produced autonomously by gpt-5.6-Sol in Codex, with human
  direction". Its source repository `Vilin97/lean-eval-green-tao` is **private** (METADATA). Six
  other accepted `green_tao` solutions exist (Humanfia + GPT 5.6 Sol, Axiom Prover, Tau, NEAR AI with
  DeepSeek V4, Midas, "max gp" GPT-6); all seven repositories are private (METADATA).
- Every one of these proves only Theorem 1.1 of Green–Tao 2008 (the primes themselves): the
  benchmark statement is fixed to `ContainsArbitraryAPs {p : ℕ | Nat.Prime p}`. None states
  Theorem 1.2 (dense subsets of the primes), which is what 22P_AP needs.
- One public lead is unread: `formal-conjectures` marks Erdős 219 (Theorem 1.1) and Erdős 1187
  part (i) (monochromatic prime progressions in every finite colouring, which on paper comes from
  Theorem 1.2) as formally proved in `plby/lean-proofs`. That repository is too large for the
  source-archive route I had, so I could not read it.
- A public, Apache-2.0, AI-produced proof of Szemerédi's theorem with the Varnavides count exists in
  Lean Pool (`LeanPool.DensityHalesJewett`, by Gabriel Dahia). I compiled all 17 modules
  **unchanged** against our pins (Lean 4.35.0, Mathlib `56a00585`). `#print axioms` gives
  `[propext, Classical.choice, Quot.sound]` (VERIFIED). This is the combinatorial input of the
  transference proofs, but it is not Green–Tao.
- I wrote the hypothesis that would replace `ZInQ.GoodPrimeAP` and the reduction to it in a
  scratch Lean file, which compiles against our Mathlib with standard axioms (VERIFIED):
  `scratch/gt-search/GreenTaoReduction.lean`.
- Proposition D in Lean needs five pieces: (D1) the CM point count; (D2) primes in progressions;
  (D3) a uniform Brun–Titchmarsh bound for Gaussian primes in residue classes; (D4) a lattice count;
  (D5) the assembly. Mathlib already has the Dirichlet-series lower bound for primes in a progression
  and a Selberg-sieve skeleton. PrimeNumberTheoremAnd has the natural-density PNT in progressions
  and a one-dimensional Brun–Titchmarsh bound. Nothing in either library does (D1) or (D3). Positive
  Dirichlet density is easier to reach than natural density, because it avoids importing
  PrimeNumberTheoremAnd, and it is enough: it implies positive relative upper density, which is all
  Theorem 1.2 asks for. It does not remove the Gaussian sieve (D3).

## 0. How the search was done

GitHub code search, the GitHub API, the Lean Zulip archive and its API, GitLab, Codeberg,
vilin97.github.io and the Lean Pool documentation site could not be queried in this run. What
worked: the arXiv API and arXiv TeX sources; a web search that returns titles and URLs only;
the Hugging Face API; and downloads of source archives of public GitHub repositories at exact
commits. The archive route cannot search code, cannot list a user's repositories, and fails for
repositories over 500 MB. So the GitHub sweeps already done by the project (all 108 `Vilin97`
repositories, `uw-math-ai`, the 337 projects of `LeanPool/lean-pool`, code search for
`GreenTao`/`green_tao`) were not repeated. Instead I read the repositories that those sweeps could
not see into: the lean-eval benchmark and its submission records, Lean Pool's source at its last
public commit, `formal-conjectures`, PrimeNumberTheoremAnd, FormalQualBench and LeanTriathlon.
Every search is in the log, including the ones that found nothing.

## 1. The candidates

### 1.1 lean-eval `green_tao`: seven accepted, private solutions (METADATA)

**The problem.** [`leanprover/lean-eval`](https://github.com/leanprover/lean-eval) at
`38361be884302c7edce1908c4aef8296eb2cb27e` (2026-10-07; Lean `v4.35.0-rc3`; Apache-2.0),
file `LeanEval/NumberTheory/GreenTao.lean`, submitter Kim Morrison (VERIFIED):

```lean
def ContainsArbitraryAPs (A : Set ℕ) : Prop :=
  ∀ k : ℕ, ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ A

@[eval_problem]
theorem green_tao : ContainsArbitraryAPs {p : ℕ | Nat.Prime p} := by
  sorry
```

The module docstring says: "As of 2026 it has not been formalized in any major proof assistant." A
solution is accepted only if comparator checks the fixed statement, with permitted axioms
`propext`, `Quot.sound` and `Classical.choice` (`generated/green_tao/config.json`). The current
workspace (`generated/green_tao/lakefile.toml`) pins Mathlib `5e0c4e52` and
`Vilin97/lean-pool` `e9d53e9c`.

**The accepted solutions.** [`leanprover/lean-eval-submissions`](https://github.com/leanprover/lean-eval-submissions)
at `e6cee4be3b6ce6f7625c5a2914a090be1ff24729` (2026-10-14), files `results/<login>.json`
(VERIFIED that these records say this):

| # | Owner (results file) | Declared model | Accepted (UTC) | Source repository @ commit | Intake |
| --- | --- | --- | --- | --- | --- |
| 1 | `Vilin97` (Vasily Ilin) | gpt-5.6-Sol | 2026-08-01 07:07 | `Vilin97/lean-eval-green-tao` @ `0c5d3337c3ebb59c318ab9030e31b835826141f8` | issue 907 |
| 2 | `ZhengyangZhang06` | Humanifa + GPT 5.6 sol | 2026-08-16 10:52 | `humanfia/lean-eval` @ `ab2e8d68a5e4e07055f919e0e38bb43bf53a252b` | issue 1052 |
| 3 | `Vilin97` (same results file) | Axiom Prover (Axiom Math) | 2026-08-29 06:44 | `AxiomMath/lean-eval-submissions-final` @ `b092f7455ac0cf0c405e42fbb669ef8144de9fd9` | issue 1481 |
| 4 | `lukerj00` | Tau (caj.al) | 2026-09-05 18:47 | `lukerj00/tau-lean-eval-submission` @ `048689343f7b1c3a81bed1f7ad9751140d8375c2` | issue 1690 |
| 5 | `skidanovalex` | NEAR AI w/ DeepSeek V4 | 2026-09-16 02:40 | `SkidanovAlex/leaneval-deepseek` @ `865b8d22b5c90d4e0b5a1a487690d1df647cf2a6` | server |
| 6 | `sarjinius` | Midas | 2026-09-27 20:24 | `midas-intelligence/midas-leaneval-submission` @ `87b09d3be013f0aad646f54721df147ee40ade33` | issue 1829 |
| 7 | `ma4ypic4y` | max gp (GPT-6; corrected to gpt-6.1-sol) | 2026-10-12 13:11 | `ma4ypic4y/lean-eval-top1` @ `f0705867b4113800f875a9e7749275b8f0d66adf` | issue 2058 |

Every record has `"public": false`. All seven repositories refuse anonymous access today: they
are private, or they have been deleted.

What the records say about the proofs:

- Vilin97 (#1): "Produced autonomously by gpt-5.6-Sol in Codex, with human direction. Builds on
  Mathlib and LeanEval's transference/majorant framework, adding a source-full ordered
  hypergraph-removal assembly. The submitted source contains no sorry, admit, added axioms,
  set_option, or native_decide." Benchmark commit `3f3786f3b4d9a4b64a5859b3036aca190cd25613`.
  The private replay plan
  (`evidence/historical-replay/private-plans/d9561ad6….json`, entry for result
  `r2_f91d3217…`) classifies it `bound`, `profile_qualified`.
  The hypergraph-removal wording points to a Conlon–Fox–Zhao-type relative Szemerédi theorem
  (relative hypergraph removal, then transference to a majorant), not to Green–Tao's original
  Gowers-norm route. This is my inference from the description; I have not seen the source.
- ma4ypic4y (#7): "92 submitted Lean sources", "lake test exit 0, Nanoda and Lean default kernel
  acceptance, no prohibited axioms" against benchmark `38361be8` (Lean `v4.35.0-rc3`), which is
  the closest of the seven to our pins.
- Humanfia (#2): publication "planned", 2026-08-31. I found no publication (see 1.3).
- Licence: none is stated, because the sources are not published. The lean-eval README says
  that server submissions default to scheduled publication: "Accepted scheduled source is
  released under Apache License 2.0 exactly two UTC calendar months after acceptance." The results
  files do not record whether an owner chose that. Issue-intake submissions (all except #5) have
  no automatic release. If #5 chose scheduled publication, its earliest release date is
  2026-11-16 (unverified).

**Which theorem.** Theorem 1.1 only. The comparator-fixed statement is the set of all primes.

**Is 1.2 a small step from it?** Only if the solution's relative Szemerédi layer is stated for a
general weight. Every transference proof proves, for a pseudorandom majorant `ν` on the W-tricked
progression, a statement of the form "if `0 ≤ f ≤ ν` and `E f ≥ δ` then `E f(x)f(x+d)⋯f(x+(k−1)d)
≥ c(k,δ) − o(1)`". If the private proof has that statement for an arbitrary `f`, then Theorem 1.2
needs only the density step redone for a set `A` instead of all primes. Take `N` with
`|A ∩ [1,N]| ≥ δπ(N)`. Pigeonhole over the `φ(W)` reduced classes gives a class `b` with
`Σ_{n ≤ N/W, Wn+b ∈ A} log(Wn+b) ≫ δ N/φ(W)`. Put `f(n) = (φ(W)/W) log(Wn+b) 1_A(Wn+b)`, which
satisfies `0 ≤ f ≤ ν` because `A` is a set of primes. Discarding the `O(N)` progressions with zero
difference among the `≫ N²` counted is the same as in the prime case. I would expect a few hundred
lines. If instead the formal proof hard-codes the prime indicator, for instance by using a prime
number theorem in classes inside the transference step, the change is larger. I cannot tell which
without the source.

### 1.2 `plby/lean-proofs`: Erdős 219 and Erdős 1187 (UNREAD, public)

[`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures) at
`84cf7f8adfb0ea8d14c7d00bdf145cc9032bdf88` (2026-10-14) (VERIFIED that these tags are there):

- `FormalConjectures/ErdosProblems/219.lean`:
  `theorem erdos_219 : ∀ N : ℕ, ∃ l ∈ primeArithmeticProgressions, N ≤ ENat.card l` (Theorem 1.1),
  tagged `formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/1268917deaaaa0d674f651287027baa26cea9920/src/latest/ErdosProblems/Erdos219.lean"`.
  That commit exists, with commit time 2026-09-07 04:32:25 UTC.
- `FormalConjectures/ErdosProblems/1187.lean`, `erdos_1187.parts.i`: for every `k ≥ 3` and every
  finite colouring of `ℤ` there is a monochromatic `k`-term progression of primes. The docstring
  derives it "from the theorem of Green and Tao [GrTa08] (that any set of primes with positive
  relative density contains arbitrarily long arithmetic progressions)". It is tagged
  `formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1187.lean#L246"`.

`plby` is not among the seven `green_tao` solvers (`results/plby.json` has one unrelated result).
The repository is public, but its source tree is over 500 MB, so I could not download it, and none
of the guessed smaller repositories exist. The 1187 proof is the most interesting public object
for us. Pigeonhole over finitely many colours turns 1187(i) into the dense form, so a proof of it
probably contains Theorem 1.2, or a relative Szemerédi theorem for a dense colour class.
Authorship, AI use, licence, Lean/Mathlib versions and completeness are all unknown. **This file
should be read first, from a machine with GitHub access.**

### 1.3 Humanfia snapshot on Hugging Face (VERIFIED: public, incomplete, unlicensed)

Dataset [`humanfia-lab/lean-eval-source`](https://huggingface.co/datasets/humanfia-lab/lean-eval-source)
at `6a6d9f67a91d546677321aeea559c2857b697635` (2026-08-18). The `green_tao` workspace is unchanged
since `2528f9e2`, 2026-08-08, which is before acceptance #2. `problems/green_tao/` is 15,370 lines,
on Lean `v4.32.0-rc1` and Mathlib `360da6fa`. Its `Submission.lean` reads:

```lean
theorem green_tao : ContainsArbitraryAPs {p : ℕ | Nat.Prime p} := by
  intro k
  by_cases hk : k ≤ 27
  · exact Lucas.primeAP_of_le_twenty_seven k hk
  · sorry
```

So it is explicit prime progressions, with Lucas certificates, up to length 27, plus a chain of
conditional reductions specialised to the primes (`prime_progression_of_uniform_dense_model`,
`prime_progression_of_selberg_apDual_pseudorandom`, `contains_of_wTrickedPrimes`, …). The dataset
card says "UNLICENSED © Zijian Zhang". It cannot be vendored, and it is not complete.

### 1.4 Statements without proofs (VERIFIED)

- [`math-inc/FormalQualBench`](https://github.com/math-inc/FormalQualBench) `efaa113c` (Lean 4.28.0,
  Apache-2.0), `FormalQualBench/GreenTaoTheorem/Main.lean`:
  `theorem MainTheorem : ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i : Fin k, Nat.Prime (a + i.1 * d) := by sorry`.
  MerLean-Prover ([arXiv:2605.26959](https://arxiv.org/abs/2605.26959), appendix table) lists
  `GreenTaoTheorem` among the problems it did not close. h1
  ([arXiv:2610.35962](https://arxiv.org/abs/2610.35962)) reports 14/23 on FormalQualBench without
  a per-problem list.
- [`project-numina/LeanTriathlon`](https://github.com/project-numina/LeanTriathlon) `2aede420`:
  `LiveLeanTriathlonSorry/GreenTaoTheorem/All.lean`, a `sorry` statement.
- `formal-conjectures` `erdos_219` is itself a `sorry` statement; the proof is the external link
  in 1.2. `erdos_3.variants.green_tao` is the Green–Tao bound for `r₄(N)`, and
  `erdos_210.variants.green_tao` concerns ordinary lines; neither is about primes.
- `Koerbser/erdos-3-autolab` assumes Green–Tao as a hypothesis (reported by the project; its
  archive could not be produced here).

### 1.5 A component: Szemerédi's theorem in Lean Pool (VERIFIED, built)

[`Vilin97/lean-pool`](https://github.com/Vilin97/lean-pool) at
`9c7629e5549220179437cc258a5b0787257d4d54` (2026-09-29, the last commit of the public repository;
Lean `v4.34.0`, Mathlib `v4.34.0`, Apache-2.0). Project card `densityhalesjewett` in
`LeanPool/projects.yml`: author Gabriel Dahia, upstream `gdahia/densityhalesjewett` @
`1c2f5aa1b99caa8e2a87beacf80f07f066c309d3`, `status: verified`, `provenance: AI`. It has 17
modules and 6,026 lines. Main statements:

```lean
theorem Combinatorics.ArithmeticProgression.exists_of_density_nat_atTop (k : ℕ) (hk : 3 ≤ k)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ A : Finset ℕ, A ⊆ range n → δ * n ≤ #A →
      ∃ a d : ℕ, d ≠ 0 ∧ ∀ i : Fin k, a + i * d ∈ A

theorem Combinatorics.ArithmeticProgression.exists_many_of_density_nat (k : ℕ) (hk : 3 ≤ k)
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : supersaturationBound k δ ≤ n) (A : Finset ℕ)
    (hAn : A ⊆ range n) (hA : δ * n ≤ #A) :
    supersaturationConstant k δ * n ^ 2 ≤ #(containedProgressions k n A)
```

I compiled all 17 files byte for byte with `lean` v4.35.0 against the Mathlib `56a00585` build,
one module at a time: no errors, no warnings, about 35 s. `#print axioms` on both theorems and on
`Combinatorics.Line.exists_of_density_atTop` gives `[propext, Classical.choice, Quot.sound]`. The
sources contain no `sorry`, `axiom` or `native_decide`.
The Varnavides form is exactly the finitary input of Green–Tao 2008 (their Proposition 2.3) and
of Zhao's arithmetic transference proof
([arXiv:1307.4959](https://arxiv.org/abs/1307.4959)). Lean Pool contained no Green–Tao, no relative
Szemerédi theorem and no dense model theorem at that commit: I grepped the whole tree, all 250
project cards, and the candidate lists `candidates/shortlist.md` and `candidates/decisions.jsonl`.
The newer organisation copy `LeanPool/lean-pool` was too large to download. The Lean Pool paper
([arXiv:2609.25199](https://arxiv.org/abs/2609.25199), Ilin, 2026-09-21; TeX source read) lists no
Green–Tao project either.

### 1.6 Searched, nothing found

Mathlib `56a00585` (`docs/1000.yaml`: "Green–Tao theorem" Q922012 and "Szemerédi's theorem"
Q1046232 have no declaration); arXiv full-text queries (Green-Tao with Lean, formalization or
formalized; relative Szemerédi with Lean; Szemerédi with Lean and formalization); Hugging Face
(green-tao, szemeredi, Vilin97, lean-pool, plby, Erdos219); web searches for Ilin with Green–Tao,
FormalQualBench solutions, Gowers norms in Lean, relative Szemerédi or dense model theorem in Lean,
hypergraph removal in Lean, Green–Tao in Isabelle/Coq, and the Zulip archive by title. The details
are in the log.

## 2. Theorem 1.1 against Theorem 1.2

Green–Tao 2008, Theorem 1.2 (quoted from the TeX source in `docs/research/rv-nt22p-ap.md` §5 on
`wip/rv-nt22p-ap`): "Let `A` be any subset of the prime numbers of positive relative upper
density, thus `limsup_{N→∞} π(N)^{−1}|A ∩ [1, N]| > 0` … Then `A` contains infinitely many
arithmetic progressions of length `k` for all `k`."

| Candidate | Statement formalized | Gives 1.2? | Extra work to 1.2 |
| --- | --- | --- | --- |
| lean-eval #1–#7 (private) | 1.1 | no | density step for a dense `A` (§1.1). A few hundred lines if the relative Szemerédi layer takes a general `f ≤ ν`; unknown otherwise |
| `plby/lean-proofs` Erdos219 (unread) | 1.1 | no | as above |
| `plby/lean-proofs` Erdos1187 (unread) | colouring form | probably contains it | read it; if a dense form is inside, expose it |
| Humanfia snapshot | 1.1 for `k ≤ 27` only | no | the whole transference argument |
| Lean Pool DHJ | Szemerédi in ℕ | no | majorant, linear forms, transference: the whole of Green–Tao minus its finitary input |

## 3. Import plan

**Choice of candidate.** Solution #1 by Vasily Ilin is the best candidate. It is the oldest
accepted proof and its author is reachable. It is described as sorry-free with no extra axioms.
And its relative-Szemerédi-via-hypergraph-removal structure is the one that generalises most
easily to dense subsets. If it cannot be shared, the fallback is the public `plby/lean-proofs`
Erdos1187 development, which must first be read; after that comes #7, which is closest to our
versions.

**Step 1: access and licence.** Ask Vasily Ilin for the source of `Vilin97/lean-eval-green-tao` @
`0c5d3337` under Apache-2.0, the licence of Lean Pool and of lean-eval. Also ask whether the
relative Szemerédi step is stated for a general weight `0 ≤ f ≤ ν`. Without a licence nothing can
be vendored. Our `THIRD_PARTY_NOTICES.md` would get an entry like the one for Mathlib.

**Step 2: versions and porting.** The solution targets the lean-eval workspace of benchmark commit
`3f3786f3` (2026-08-01). In August the `green_tao` workspace used Lean `v4.32.0-rc1` and Mathlib
`360da6fa`; that is the version the Humanfia snapshot records for the same problem, so the exact
pin of #1 is unverified. Our pins are Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
That is three Lean releases. For scale: Lean Pool's archive-wide upgrades changed 4,676–11,690
lines per release across 3.2 million lines (Lean Pool paper, table `migration-effort`), roughly
0.15–0.4%. The 6,026-line Szemerédi development needed no change at all from `v4.34.0` to our
pins. For a 15–20k-line proof I would plan on a few hundred changed lines (renamed and
deprecated lemmas, `simp` set changes; for example `Set.mem_setOf_eq` is deprecated in our
Mathlib), at most a few days of work. Solution #7 was checked against `v4.35.0-rc3` and would need
almost nothing.

**Step 3: Lake dependency or vendored files.** A Lake `require` is not workable unless the
dependency is pinned to our exact Mathlib commit, because Lake resolves a single Mathlib for the
whole build. It also brings in `lean-pool` if the solution uses it; the current lean-eval
workspaces depend on `Vilin97/lean-pool`. The robust option is to vendor the files into a separate
library directory, for example `ZInQKernel/External/GreenTao/`, keeping the Apache-2.0 headers,
listing the source commit and authors in `THIRD_PARTY_NOTICES.md`, and porting in place. Any Lean
Pool modules it imports (for instance `LeanPool.DensityHalesJewett`, already shown to compile
unchanged) are vendored the same way.

**Step 4: the 1.2 extension.** Prove `GreenTaoDense` (below) from the vendored relative Szemerédi
theorem, by the density step of §1.1.

**Step 5: the statement that replaces `ZInQ.GoodPrimeAP`.** With Theorem 1.2 proved, the
hypothesis becomes Proposition D in its weakest usable form: positive relative upper density of
the good slope primes. The scratch file `scratch/gt-search/GreenTaoReduction.lean` (Mathlib only)
compiles with Lean 4.35.0 and Mathlib `56a00585`. `#print axioms
GTSearch.progressions_above_of_greenTaoDense` gives `[propext, Classical.choice, Quot.sound]`
(VERIFIED). Its definitions:

```lean
def ContainsArbitraryAPs (A : Set ℕ) : Prop :=
  ∀ k : ℕ, ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ A

open Classical in
def PrimesRelUpperDensityPos (A : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ᶠ N in atTop,
    c * (Nat.primeCounting N : ℝ) ≤ (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ)

def GreenTaoDense : Prop :=
  ∀ A : Set ℕ, A ⊆ {p | p.Prime} → PrimesRelUpperDensityPos A → ContainsArbitraryAPs A

theorem progressions_above_of_greenTaoDense (hGT : GreenTaoDense) {G : ℕ → Prop}
    (hGprime : ∀ p, G p → p.Prime) (hG : PrimesRelUpperDensityPos {p | G p}) (S : Finset ℕ) :
    ∀ K : ℕ, ∃ x v : ℕ, 1 ≤ x ∧ 1 ≤ v ∧ ∀ j ≤ K, G (x + j * v) ∧ ∀ q ∈ S, q < x + j * v
```

With `G := ZInQ.GoodSlopePrime` (which includes `p.Prime`) and `S := ZInQ.Mult.S_b`, the conclusion
is literally `ZInQ.GoodPrimeAP`. So the new hypothesis, to sit in `ZInQKernel/Hypotheses/` once
`GreenTaoDense` is a theorem, is

```lean
/-- Proposition D (weak form): the good slope primes have positive relative upper density. -/
def GoodPrimeDensity : Prop := GTSearch.PrimesRelUpperDensityPos {p | ZInQ.GoodSlopePrime p}
```

and `GoodPrimeAP` follows in one line from `progressions_above_of_greenTaoDense`. Until the
import is done, the same reduction can already be stated with `GreenTaoDense` as an explicit
hypothesis. That separates the trust base into "Green–Tao 1.2" and "Proposition D". I did not edit
any file in `ZInQKernel/`.

## 4. What a Lean proof of Proposition D needs

Proposition D (`docs/research/nt-22p.md` §2.2) says the good slope primes `G` have natural density
`(1/8)∏_{ℓ≡1 (4)}(1 − 2/(ℓ−1)²) ≈ 0.106`. For 22P_AP, only `GoodPrimeDensity` above is needed. The
Hecke-free variant of §2.2 is the one to formalize. It imposes `p ≢ −1 (mod ℓ)` for the primes
`ℓ ≡ 1 (mod 4)` up to `L`, a condition on `p` alone. That gives relative density `≫ (log L)^{−1}`
(in fact `≍ (log L)^{−1/2}`) against a tail `O(1/L)`, and it never needs the Hecke prime ideal
theorem. Neither library has the Hecke theorem: PrimeNumberTheoremAnd's Chebotarev section is
blueprint prose, and `AxiomMath/DedekindZetaZeroFree` exists but I could not read it.

**(D1) The CM description, inclusion direction.** For `p > 324` with `p ≡ 1 (mod 8)`,
`(7/p) = −1`, `p = a² + b²`, `a` odd and no odd prime `ℓ` dividing both `a` and `p + 1`:
`GoodSlopePrime p`. The ingredients:

- `r² = 2` is solvable (`ZMod.exists_sq_eq_two_iff`).
- The two curves `y² = x³ − d_i² x` are quadratic twists of each other, because `d₁d₂ = 7` is a
  non-square. Then `#E₁ + #E₂ = 2(p + 1)` by a character-sum substitution.
- `4 | #E_i`, and the trace is `±2a`. This is Gauss's evaluation through the quartic Jacobi sum.
  Mathlib has the ingredients: `jacobiSum_mul_jacobiSum_inv` (norm `p`),
  `exists_jacobiSum_eq_neg_one_add`, `gaussSum_pow_eq_prod_jacobiSum`, `GaussianInt`,
  `Nat.Prime.sq_add_sq`. It does not have the evaluation, nor any point count of these curves.

The repository has `ZInQ.pointCount` but no character-sum theory. Estimate: 1.5–3k lines; this
is the most specialised piece.

**(D2) Primes in the main classes.** The class `C_L` is a union of reduced classes modulo
`M_L = 56·∏_{ℓ≤L} ℓ`, using quadratic reciprocity for `(7/p)` (`legendreSym.quadratic_reciprocity`).
Either route works:

- Dirichlet density, already in our Mathlib: `ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound`
  gives `∑' n, residueClass a n / n^x ≥ φ(q)⁻¹/(x − 1) − C` for `x ∈ (1, 2]`, and there is also
  `continuousOn_LFunctionResidueClassAux`.
- Natural density: PrimeNumberTheoremAnd `WeakPNT_AP` (`Wiener.lean:4025`, at
  `c39a751132c88b6e8080b74c74023fd95b3d8be0`, Lean `v4.34.0`): `ψ(N; q, a)/N → 1/φ(q)`. Wiener.lean
  contains two `sorry`s (`prelim_decay_2`, `prelim_decay_3`). By a static grep they are used only
  through `decay_alt` by `IEANTN/CH2`, not by `WeakPNT_AP`. I did not confirm this with
  `#print axioms`, because no Mathlib `v4.34` build was available.

Also needed is a lower bound for `∏_{ℓ≤L, ℓ≡1(4)}(1 − 1/(ℓ−1))`. It follows from an upper bound on
`Σ_{ℓ≤L} 1/ℓ`: Mertens, available as PrimeNumberTheoremAnd `Mertens.sum_mangoldt_div_eq_log` and
`Mertens.E₁Λ.bounded` (`IEANTN/Mertens.lean`, sorry-free), or derivable from
`Chebyshev.theta_le_log4_mul_x` with Abel summation (`sum_mul_eq_sub_sub_integral_mul`). The
CRT count of the classes in `C_L` is routine. Estimate: about 1k lines on the Dirichlet route.

**(D3) Tail `L < ℓ ≤ N^{1/8}`: uniform Brun–Titchmarsh for Gaussian primes.**

The bound needed is

`#{p ≤ N : p = a² + b², ℓ | a, b ≡ ±b₀ (mod ℓ)} ≤ C·N/(ℓ² log N)`

uniformly in `ℓ` (rv-nt22p-ap F5: trivial counting loses the `1/log N`, and the sum over `ℓ` then
fails).

What exists:

- The Selberg Λ² skeleton in our Mathlib (`Mathlib/NumberTheory/SelbergSieve.lean`):
  `BoundingSieve`, `SelbergSieve`, `BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius`,
  `upperMoebius_lambdaSquared`, `mainSum_lambdaSquared_eq_sum_mul_sum_sq`.
- In PrimeNumberTheoremAnd: the closed upper bound `SelbergSieve.selberg_bound_simple`
  (`siftedSum ≤ X/S + Σ_{d≤y} 3^{ω(d)}|R_d|`, `Mathlib/NumberTheory/Sieve/Selberg.lean:435`), and
  a worked one-dimensional application, `BrunTitchmarsh.primesBetween_le` (`BrunTitchmarsh.lean:248`,
  primes in an interval).

What is missing is the two-dimensional instance:

- support: the norms `a² + b²` of the points of the lattice coset in the disc;
- density `ν(q) = ρ(q)/q²`, with `ρ(q) = 2q − 1, 1, 2` for `q ≡ 1 (4)`, `q ≡ 3 (4)`, `q = 2`;
- remainders `R_d` from a lattice-point count in a disc with congruences modulo `dℓ`, uniform in
  `d` and `ℓ`;
- a lower bound `S ≫ log z`, the two-dimensional analogue of `Σ_{d≤z} 1/d ≥ log z`, through
  `Σ_{n≤y} r₂(n)/n ≫ log y` or Mertens for `q ≡ 1 (mod 4)`.

The manuscript's own two-dimensional sieve (`eq:prime-selberg`, `eq:prime-truncated-denominator`)
is the paper reference. Estimate: 3–5k lines. This is the largest piece, and it is needed on every
route, since the Hecke route still needs it for `ℓ > L`.

**(D4) Tail `ℓ > N^{1/8}`: lattice count.** The bound is
`#{(a, b) : a² + b² ≤ N, ℓ | a, b ≡ ±b₀} ≪ N/ℓ² + √N/ℓ + 1`. Summed over
`N^{1/8} < ℓ ≤ √N`, this gives `≪ N^{7/8} + √N log N` (keep the second term, F5). It is elementary.
Estimate: 300–600 lines.

**(D5) Assembly and the choice of density.** `G ⊇ C_L ∖ ⋃_{ℓ>L} Bad_ℓ` by (D1). (D2) gives the main
term `≫ (log L)^{−1}`, and (D3) with (D4) gives a tail `≤ C/L + o(1)`. Fix `L` large. On the
Dirichlet route, the counting bounds of (D3) and (D4) must be turned into bounds for
`Σ_{p∈Bad_ℓ} log p/p^x` by Abel summation. Then

`liminf_{x→1⁺} (x − 1)·Σ_{p∈G} log p/p^x > 0`

implies `GoodPrimeDensity`. The argument: if `|G ∩ [1, N]| ≤ ε π(N)` for all large `N`, Abel
summation with `π(t) ≪ t/log t` bounds that liminf by `O(ε)`. Here `π(t) ≪ t/log t` comes from
`Chebyshev.theta_le_log4_mul_x` and `Chebyshev.primeCounting_sub_theta_div_log_isBigO`. Estimate:
500–1000 lines.

**Is a positive Dirichlet density easier?** Yes, for (D2) and (D5): it uses only what is in our
Mathlib, with no PrimeNumberTheoremAnd import (a large `v4.34.0` project) and no Wiener–Ikehara.
And positive (lower) Dirichlet density implies positive relative upper natural density, which is
exactly Theorem 1.2's hypothesis. It is not easier for (D1) or (D3), the two pieces with no
library support. Natural density gives more (Proposition D's lower density) but is not needed.

**Total.** Roughly 6–10k lines of new Lean, dominated by the Gaussian sieve (D3) and the Jacobi
sum evaluation (D1). These figures are estimates, not measurements.

## 5. Recommendation

1. Ask Vasily Ilin for the source of `Vilin97/lean-eval-green-tao` @ `0c5d3337` under Apache-2.0,
   and ask whether its relative Szemerédi theorem takes a general weight `f ≤ ν`. In parallel,
   read `plby/lean-proofs` `src/latest/ErdosProblems/Erdos1187.lean` @ `8822f7dd` (public), which
   may already contain Theorem 1.2.
2. When a source is available, vendor it (Apache-2.0 headers, a `THIRD_PARTY_NOTICES.md` entry),
   port it to Lean 4.35.0 / Mathlib `56a00585`, and prove `GreenTaoDense`. Then replace
   `GoodPrimeAP` by `GoodPrimeDensity` through `progressions_above_of_greenTaoDense`.
3. Independently, Proposition D can be formalized on the Dirichlet-density route. The order would
   be (D4), (D2) and (D5) first, which are mostly library-backed, then (D1) and (D3). Once both are
   done, the main theorem's AP variant needs no number-theoretic hypothesis beyond those already in
   the kernel.

## Sources and revisions

- lean-eval: `leanprover/lean-eval` `38361be884302c7edce1908c4aef8296eb2cb27e`;
  `leanprover/lean-eval-submissions` `e6cee4be3b6ce6f7625c5a2914a090be1ff24729`;
  `leanprover/lean-eval-leaderboard` `0970e27052b71dec08cd22214f45c0e8f6ed5fd2`
  (`benchmark-snapshot/BenchmarkProblems/ProblemGreenTao.lean`).
- Lean Pool: `Vilin97/lean-pool` `9c7629e5549220179437cc258a5b0787257d4d54`; paper arXiv:2609.25199.
- `google-deepmind/formal-conjectures` `84cf7f8adfb0ea8d14c7d00bdf145cc9032bdf88`.
- `AlexKontorovich/PrimeNumberTheoremAnd` `c39a751132c88b6e8080b74c74023fd95b3d8be0` (tag `v4.34.0`).
- `math-inc/FormalQualBench` `efaa113c6a00a79e92842ce541b407d7695d7699`;
  `project-numina/LeanTriathlon` `2aede4209c203ae9901eff870744e4b77dc6173f`.
- Hugging Face `humanfia-lab/lean-eval-source` `6a6d9f67a91d546677321aeea559c2857b697635`.
- Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (this repository's pin).
- Build artefacts (outside the repository): Lean Pool DHJ compiled in `~/gt-builds/dhj`
  (`axioms.out`). The reduction file is `scratch/gt-search/GreenTaoReduction.lean`.
