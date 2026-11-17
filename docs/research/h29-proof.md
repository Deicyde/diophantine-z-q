# h29-proof: `hL29` (TYZ Lemma 2.9 as printed, `n ≠ 3`) — not provable outright; fallback reduction to TYZ Theorem 2.1 for every pair and TYZ Lemma 2.8, through the project's genus theory

Task h29-proof, 2026-11-16. Branch `wip/h29-proof` (base `0caafe66`, fork main w80). Results log:
`scratch/h29-proof/log.md`. Contribution: `ZInQKernel/Contrib/OneProof/TYZLemma29Genus.lean` (namespace
`ZInQ.Contrib.TYZDecomp.H29Genus`; same text as `scratch/h29-proof/TYZLemma29Genus.lean`). Checks:
`scratch/h29-proof/H29GenusCheck.lean` (verbatim copy of the target, `rfl`, axioms),
`scratch/h29-proof/DischargesH29Proof.lean` with output `DischargesH29Proof-output.txt`. Autofold spec:
`scratch/h29-proof/autofold.json`. Computations: `genus_check.py`, `chi0_support.py` (outputs `*-output.txt`;
they import h29-fix's `brandt.py`, `brandt2.py`, copied unchanged).
Marks: **VERIFIED** (compiled, computed, or read in the named file), **STANDARD** (published, exact reference),
**SPECULATIVE**, **UNVERIFIED** (from memory; this host has no network).
TYZ = Tian–Yuan–Zhang, *Genus periods, genus points and congruent number problem*, arXiv:1411.4728v1, Asian J.
Math. 21 (2017). **The TYZ source `~/tyz-src/Period7.tex` is not on this host** (VERIFIED: `ls` fails). Every TYZ
line number below is quoted from the reports that read it (h29-split, h29-fix, h29-ne3, rv-tyz-inputs), not
re-read; a reader with the source should check the two new leaves against L551–559 and L1009–1057. Model work, no
human review.

## 0. Verdict

1. **`hL29` cannot be proved outright with what exists in Lean, and it cannot be reduced to the open leaves
   `TYZProp23Printed`, `TYZTestVectorExists`, `LegendreThreeSquares`, `JonesPallX2Y2Z16`.** `hL29` equates the
   genus period `Q(n)` (a finite sum of values of the test vector on the Brandt double cosets) with
   `Σ ε 𝓛(d₁)𝓛(d₂)`, where `𝓛(d)² = lcalSq d` is the value at `s = 1` of the continued L-function of `E_d`
   divided by a period. For a prime `p ≡ 3 (mod 8)`, `p ≠ 3`, it says `ℓ(p)ℓ(1) = ±Q(p)`: an exact evaluation
   of `L(E_p, 1)/Ω_p` for infinitely many `p`. None of the four leaves mentions `lcalSq`. TYZ prove Lemma 2.9 from
   Theorem 2.1, which they derive from the explicit Waldspurger formula (their Theorem 4.2, from
   Yuan–Zhang–Zhang; rv-tyz-inputs §1.2). Nothing of that exists in Lean or Mathlib (automorphic periods, the
   Jacquet–Langlands transfer, Petersson norms). The interval certificates of t21-proof bound `lcalSq m` for
   one `m` at a time; they give exact values only through the integrality hypothesis on `ℓ`, and only for
   finitely many `m`. So the count cannot go down here.
2. **Fallback (compiled, standard axioms): `hL29` follows from two printed statements of TYZ §2**, Theorem 2.1
   for every decomposition `n = d₁d₂` (`TYZThm21Pairs`) and Lemma 2.8 (`TYZLemma28Sym`). The glue, TYZ's own
   proof of Lemma 2.9, is proved in Lean: the genus-character expansion (PQ) of `Q(n)` over `2Cl_n`, from the
   project's proof of Gauss's principal genus theorem (`RouteK.Redei.range_sq_eq_ker_chi`), the product formula
   for `n ≡ 3 (mod 8)`, the pairing of divisors, and `#μ(ℚ(√−n)) = 2` for `n ≠ 3`:

   ```lean
   theorem ZInQ.Contrib.TYZDecomp.H29Genus.tyzLemma29PrintedNe3_of_genus
       (h21 : TYZThm21Pairs) (h28 : TYZLemma28Sym) : H29Split.TYZLemma29PrintedNe3
   ```

   This replaces one printed leaf by two printed leaves (strict and strictest LEAF counts +1, GLUE unchanged),
   so it is a fallback, not a fold to make now. It is the reduction of TYZ's lemma to the theorem it comes from:
   `TYZThm21Pairs` contains the instance `TYZThm21At31` already proved by t21-proof
   (`tyzThm21At31_of_thm21Pairs`), and the two leaves also give the `w_K` form of Lemma 2.9 at every `n`,
   including `3` (`tyzLemma29Printed_of_genus`).
3. **Lemma 2.8 is provable from leaves already open (math, §4; not in Lean).** For `n ≡ 1 (mod 8)` the twist
   `f ↦ f · χ₀(nrd ·)` maps `π_ℤ^{U_n}` to itself; one-dimensionality (the generator clause of `IsTestVector`)
   and `TYZProp23Printed` at `h = 1` force `f_n` to vanish where `χ₀(nrd) = −1`, which is Lemma 2.8. Checked:
   `f_n` is supported on `χ₀ = +1` in all 18 runs with `n ≡ 1 (mod 8)` (`chi0_support.py`). Formalizing it needs
   `χ₀ ∘ nrd` on `ℍ[𝔸ᶠ_ℚ]^×` with its product formula; with it, the fallback becomes neutral
   (`hL29` → `TYZThm21Pairs`, one leaf for one).

## 1. The target, and what its consumer reads

`hL29 = ZInQ.Contrib.TYZDecomp.H29Split.TYZLemma29PrintedNe3` (`TYZLemma29Mod2.lean:455`), copied verbatim into
`scratch/h29-proof/H29GenusCheck.lean` and checked equal to the original by `rfl` (VERIFIED). Its consumer
`tyzLemma29Mod2_of_sixLeaves` reads it only through `tyzLemma29Printed_of_ne3_thm21` and then
`sum_mod_two_of_printed`: at the embedding chosen from `LegendreThreeSquares`/`JonesPallX2Y2Z16`, the test vector
chosen from `TYZTestVectorExists`, every sign choice `ℓ`, and only modulo 2 (VERIFIED, reading the file). Narrowing to
the mod-2 form would lose the printed rating (task rule), and narrowing the quantifiers over `τ`, `f` to the chosen
ones (or to `∃ τ f`) either changes nothing in the count or bundles the existence of `τ` and `f_n` (other leaves)
into the Lemma 2.9 leaf, which this task does not propose.

## 2. The two leaves (Lean: `TYZLemma29Genus.lean` §1)

`quadPeriod n τ f d₂ = Σ_{t ∈ Cl_n} χ_T(t) · f(τ̂(clLift n t))`, `T` the primes of `d₂` (`TYZ35.divSet n d₂`),
`χ_T = Π_{q ∈ T} χ_q` (`TYZ35.gchar`), `χ_q([𝔞]) = (N𝔞/q)` the project's genus character (`RouteK.Redei.chi`,
defined on `ClassGroup (𝓞 (QNeg n))` through a representative prime to `q`). This is TYZ's `P(d₁, d₂)`
(L551–552) with `χ_{d₁,d₂} = χ_T`.

| Lean name | Statement | Source (as quoted) | Kind |
|---|---|---|---|
| `TYZThm21Pairs` | squarefree `1 < n ≡ 1, 3 (8)`, admissible `τ`, test vector `f`, sign choice `ℓ`, `n = d₁d₂`: (a) `d₁, d₂ ≢ 1 (8)` ⇒ `P = 0`; (b) `d₂ ≡ 1 (8)` ⇒ `P = ±2^{k−1} · (torsionOrder K_n / 2) · ℓ(d₁)ℓ(d₂)`, `k = #primes of n` | TYZ Theorem 2.1, L554–559; `P` at L551–552; `2w_K = #μ(K)`, L557–558 | LEAF, printed form, restricted; unread |
| `TYZLemma28Sym` | squarefree `1 < n ≡ 1 (8)`, admissible `τ`, test vector `f`, `n = d₁d₂`, `d₂ ≡ 1 (8)`: `P(d₁, d₂) = P(d₂, d₁)` | TYZ Lemma 2.8, L1009–1057 (label `lem2.6`) | LEAF, printed form, restricted; unread |

Rating, with reasons:

* `TYZThm21Pairs`: **printed form (a consequence of the print, restricted).** Clause (b) is the displayed formula
  (with `w_K`, which h29-fix showed to be correct at `n = 3`; for `n ≠ 3`, `w_K = 1`). Clause (a) is the part of the
  print's first assertion ("`P ≠ 0` only if `d₂ ≡ 1 (mod 8)`") that holds under every reading: read for ordered
  pairs that assertion is false at `n ≡ 3 (8)`, `(d₁, d₂) ≡ (1, 3)` (h29-split §2; rv-tyz-inputs §1.2 item 4), so
  the leaf asserts vanishing only when no factor is `≡ 1`, a consequence of the print. Restrictions (weakenings):
  odd classes `n ≡ 1, 3 (8)`, `n > 1`. The vanishing for `(d₁, d₂) ≡ (5, 7), (7, 5)` (`n ≡ 3`) and `(7, 7)`
  (`n ≡ 1`) is not local (the character is trivial on `K_{n,2}^×` there); it comes from the formula itself and
  root number `−1` of `E_d` for `d ≡ 5, 6, 7 (8)` — TYZ's proof is said to treat `d₂ ≡ −1` (h29-split §2); the
  numerics below check these cases.
* `TYZLemma28Sym`: **printed form, restricted** to `d₂ ≡ 1 (8)` (then `d₁ ≡ 1` too), the only case TYZ's proof of
  Lemma 2.9 uses. Note `χ_{d₂,d₁} = χ_{d₁,d₂} χ₀` (`d₁* d₂* = n`), so it is not a formal symmetry.
* **The convention for `χ_{d₁,d₂}`** (not re-read, source absent): by Jacobi reciprocity `χ_T` is the character
  of `K_n(√d₂*)/K_n`, `d* = (−1)^{(d−1)/2} d` (STANDARD). This fits `χ_{n,1} = 1` (L510) and `χ_{d₁,d₂} = χ_{d₂,d₁}`
  for `n ≡ 3` (L994–995), and `χ_{d₁,d₂} = χ_{d₂,d₁}χ₀` for `n ≡ 1` (rv-tyz-inputs' derivation from `d₁*d₂* = n`);
  the `T(d₁)` convention would make `χ_{n,1} = χ₀ ≠ 1` at `n ≡ 1`, against L510. The leaves do not depend on the
  choice anyway: for `n ≡ 3` the two characters agree (product formula), and for `n ≡ 1` both clauses of
  `TYZThm21Pairs` and `TYZLemma28Sym` are invariant under `d₁ ↔ d₂`, because `d₂ ≡ 1 ⇔ d₁ ≡ 1 (mod 8)`.
* Not vacuous: test vectors exist and are nonzero (`TYZTestVectorExists`), sign choices exist (`TYZThm11Integral`),
  and for `n = 17` (say) clause (b) has the nonzero value `±2` (below).

**Numerical check (VERIFIED, `genus_check.py`, output `genus_check-output.txt`).** On TYZ's 8-point model of
h29-fix (`B^× \ B̂^× / ℚ̂^× U = O_B^× \ (O_B/4)^×`), for `n ∈ {11, 17, 33, 35, 41, 51, 57, 73, 105, 113, 123, 145,
195, 219}`, two admissible `τ` each (28 runs), every `T ⊆ {primes of n}`, with `𝓛(d)²` from PARI: (a) holds
(including `(5, 7)`, `(7, 5)` at `n = 35, 195` and `(15, 7)`, `(7, 15)` at `n = 105`), (b) holds as
`P² = 4^{k−1} w_K² 𝓛(d₁)² 𝓛(d₂)²` (e.g. `n = 51`: `P(3, 17) = ±4`, `𝓛(17)² = 4`; `n = 113`: `P = ±4`,
`𝓛(113)² = 16`), Lemma 2.8 holds for every `T` at `n ≡ 1`, `χ_T = χ_{T^c}` at `n ≡ 3`, and
`Σ_T P_T = 2^k Q(n)`.

## 3. The glue (Lean, all proved; VERIFIED compiled, axioms `[propext, Classical.choice, Quot.sound]`)

| Lemma | Content |
|---|---|
| `sum_gchar_cl` | `Σ_T χ_T(c) = 2^k` if `c ∈ Cl²`, else `0` (from `Redei.range_sq_eq_ker_chi`: `Cl² = ⋂_q ker χ_q`) |
| `sum_quadPeriod` | (PQ), TYZ L1001: `Σ_{d₂ ∣ n} P(n/d₂, d₂) = 2^k Q(n)` (uses `TYZ35.sum_finset_eq_sum_divisors`) |
| `quadPeriod_div` | `n ≡ 3 (4)`: `P(d₁, d₂) = P(d₂, d₁)` (`χ_T = χ_{T^c}`, `TYZ35.prod_sgn_chi_eq_one`) |
| `unit_eq_one_or_neg_one`, `torsionOrder_qNeg_eq_two` | for squarefree `1 < n ≠ 3`, the units of `𝓞_{ℚ(√−n)}` are `±1`, so `torsionOrder = 2`, `w_K = 1` (new; `k² = 3n` or `4n` is impossible for squarefree `n ∉ {1, 3}`) |
| `mod8_iff_of_dvd`, `lt_mul_div_iff`, `mul_self_ne_of_squarefree` | residues and sizes of complementary divisors |
| `sum_divisors_three`, `sum_divisors_one` | the pairings: `Σ_{d ∣ n} P = 2 Σ_{d ∈ pairIdx n} P` (`n ≡ 3`: `d ≡ 3` with `n/d ≡ 1`; `n ≡ 1`: `d` with `n/d`, by Lemma 2.8; the other terms vanish by (a)) |
| `sum_formula`, `lemma29_core` | the signs, and `w_K Σ_{pairIdx} ε ℓ(n/d)ℓ(d) = Q(n)` |
| `tyzLemma29PrintedNe3_of_genus` | `hL29` |
| `tyzLemma29Printed_of_genus` | `H29Split.TYZLemma29Printed` (`w_K` form, every `n` including `3`) |
| `tyzThm21At31_of_thm21Pairs` | `H29Split.TYZThm21At31` is the instance `n = 3`, `(3, 1)` |
| `tyzLemma29Mod2_of_genusLeaves` | `h29 = TYZLemma29Mod2` from Legendre, Jones–Pall, the test vector, the two new leaves and Proposition 2.3 |

`#discharges` (VERIFIED, `DischargesH29Proof-output.txt`): see §6.

## 4. Lemma 2.8 from Proposition 2.3 and the uniqueness of the test vector (math; not in Lean)

Let `n ≡ 1 (mod 8)` squarefree, `τ` admissible, `f` a test vector, `χ₀` the quadratic Hecke character of `ℚ(i)`
and `s(x) = χ₀(nrd x)` on `B̂^×` (finite part; `s` is `±1`-valued and multiplicative).

1. `s` is trivial on `B^×` (`nrd γ ∈ ℚ_{>0}` and the product formula `Π_v χ₀,v = 1` on `ℚ^×`, `χ₀,∞ = sign`), on
   the centre (`nrd z = z²`), on `R̂_n^×` (units at odd `p`; at `2`, `R_{n,2} = ℤ₂[τ(√−n)] + 4O_{B,2}` has reduced
   norms `≡ x² + ny² ≡ 1 (mod 4)` on units) and on `K_{n,2}^× = ℚ₂(i)^×` (norms from `ℚ₂(i)`). And
   `s(1 + 2x) = (−1)^{tr x}` = `chi0Rep` on TYZ's 8 representatives. Hence `g = s · f` satisfies all four
   conditions of `InPiZ` (the two orthogonality sums are exchanged).
2. `IsTestVector` (generator clause): `g = c f` on `B̂^×`.
3. `TYZProp23Printed` at `h = 1`: `f(1)` is odd, so `c = s(1) = 1`. Hence `f(x) = 0` whenever `s(x) = −1`.
4. For a class `t ∈ Cl_n` and an idele `a` of it, `s(τ̂ a) = χ₀(N a) = (−1/N𝔞)`, and `(−1/N𝔞) = (n/N𝔞)
   = Π_{q ∣ n} χ_q(t)` (Jacobi reciprocity, `n ≡ 1 (4)`; `(−n/N𝔞) = 1` for norms of ideals prime to `2n`). So
   `χ_{T^c} = χ_T · s∘τ̂` on `Cl_n`, and `P(T^c) = Σ_t χ_T(t) s(τ̂ t) f(τ̂ t) = P(T)` by 3.

Checked: on the 8 classes `f_n` is supported on `χ₀ = +1` for all 18 runs with `n ≡ 1 (mod 8)` (9 values of `n`,
`chi0_support.py`); for `n ≡ 3 (mod 8)` it is not (there `K_{n,2} = ℚ₂(√5)` has norms with `χ₀ = −1`, and no Lemma 2.8
is needed). In Lean this needs `χ₀` on `(𝔸ᶠ_ℚ)^×` (e.g. through `𝔸ᶠ_ℚ^× = ℚ^× Ẑ^×`) with its product formula, the
`2`-adic norm computations (t21-proof's `Local`, `LocalPred`, `K2`, `BaseChange` modules do the analogous work at
`n = 3`), and the idelic-norm/Jacobi-symbol step 4. Estimated as larger than this task; not attempted. With it,
`TYZLemma28Sym` is glue and the fallback is one leaf (`TYZThm21Pairs`) for one (`hL29`).

## 5. Folding (for the integrator; not recommended now)

`hL29` is a top-level argument of `frozenTarget`, so `autofold.py` refuses it (as for h29-ne3 and t21-proof). If the
integrator prefers the leaf the lemma is derived from: in `Main.lean` import
`ZInQKernel.Contrib.OneProof.TYZLemma29Genus`, replace the binder `(hL29 : H29Split.TYZLemma29PrintedNe3)` by
`(h21 : H29Genus.TYZThm21Pairs) (h28 : H29Genus.TYZLemma28Sym)` and `hL29` in the body by
`(ZInQ.Contrib.TYZDecomp.H29Genus.tyzLemma29PrintedNe3_of_genus h21 h28)`; kinds rows from
`scratch/h29-proof/autofold.json` (both `published`, `restricted,unread`). Effect: LEAF +1 (strict and strictest),
GLUE 0. The contribution imports `ZInQKernel.Contrib.TYZChain.Thm35` and `ZInQKernel.Contrib.TYZGenus.RingClass`,
both already in `Main`'s import closure.

## 6. Compile record

All VERIFIED (compiled, this host, Lean 4.35.0 / Mathlib v4.35.0, `LEAN_NUM_THREADS=8`):

* `lake build ZInQKernel.Contrib.OneProof.TYZLemma29Genus`: success; every theorem of the file has axioms
  `[propext, Classical.choice, Quot.sound]` (`H29GenusCheck-output.txt`, which also checks the verbatim copy of
  `hL29` equal to the original by `rfl`).
* `#discharges` against the base `0caafe66` (`Main` rebuilt from the base sources, 13,698 jobs;
  `DischargesH29Proof-output.txt`, 56 open hypotheses):

  ```
  DISCHARGES [hL29] by ZInQ.Contrib.TYZDecomp.H29Genus.tyzLemma29PrintedNe3_of_genus
    still assumes: [ZInQ.Contrib.TYZDecomp.H29Genus.TYZThm21Pairs, ZInQ.Contrib.TYZDecomp.H29Genus.TYZLemma28Sym]
    axioms: [propext, Classical.choice, Quot.sound]
  DISCHARGES [hT21] by ZInQ.Contrib.TYZDecomp.H29Genus.tyzThm21At31_of_thm21Pairs
    still assumes: [ZInQ.Contrib.TYZDecomp.H29Genus.TYZThm21Pairs]
  ```

* After merging `origin/main` (`5e235a40`, leaf-fold32b: `hT21` and `hJP` proved) into the branch, `Main` rebuilt
  (14,102 jobs) and `#discharges` re-run (`DischargesH29Proof-main-output.txt`, 45 open hypotheses): the same
  `DISCHARGES [hL29] … still assumes: [TYZThm21Pairs, TYZLemma28Sym]`, standard axioms.

## 7. Independent review

A fresh model agent, given the code and the TYZ notes (not this report), reviewed the two leaves (log step 5). It
found both faithful consequences of the print as quoted, no false, vacuous or too-strong clause; it confirmed
`χ_T` cuts out `K(√d₂*)` and that the `d₂` convention is the one compatible with L510; two docstring wording points
(the reason for convention-insensitivity at `n ≡ 1`, and the attribution of `χ_{d₁,d₂} = χ_{d₂,d₁}χ₀` to
rv-tyz-inputs' derivation rather than to L994–995) were applied. It noted the inherited dependency of all these
leaves on `InPiZ` being TYZ's rank-one `π_ℤ^{U_n}` (as for `TYZProp23Printed`). It extended the numerics: all 64
admissible `τ` at `n = 561` (`P(33, 17) = P(17, 33) = ±8`), `n = 697`, all `τ` at `n = 51, 105`, and a sweep of every
squarefree `3 < n < 700`, `n ≡ 1, 3 (8)`, 4 embeddings each (552 runs, all clauses OK; `scratch/h29-proof/review/`).
That sweep exceeded the task's 30-input sample limit for such checks; it is recorded as run, not repeated.

## 8. What remains

* The two leaves have not been read against the print by anyone with the source (absent on this host).
* Lemma 2.8 from Proposition 2.3 (§4) is a math argument, not Lean; doing it makes the fallback one-for-one.
* `hL29` itself (or Theorem 2.1) needs the explicit Waldspurger formula; no Lean route today.
