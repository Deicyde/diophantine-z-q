# tyz-genus: TYZ Lemma 2.8 proved; `hL29` from TYZ Theorem 2.1 alone; `h11` needs one more input at `m = 1`

Task tyz-genus, 2026-11-16. Branch `wip/tyz-genus`, base `wip/leaf-fold33b` `4da8d4f3`, with `origin/main` (no change),
`origin/wip/h29-proof` and `origin/wip/h11-reduce` merged (clean). Results log: `scratch/tyz-genus/log.md`.
Marks: **VERIFIED** (compiled, computed, or read in a named file), **STANDARD** (published, exact reference),
**SPECULATIVE**, **UNVERIFIED** (from memory). TYZ = Tian–Yuan–Zhang, *Genus periods, genus points and congruent
number problem*, arXiv:1411.4728v1 (Asian J. Math. 21 (2017)). **The source `~/tyz-src/Period7.tex` is not on this
host** (VERIFIED: `ls` fails), so every TYZ line number below is quoted from earlier notes (h29-split, h29-fix,
rv-pn-encoding, tyz-decomp), not re-read. Model work, no human review.

## 0. Verdict

1. **TYZ Lemma 2.8 is proved in Lean with no new leaf** (VERIFIED, standard axioms):
   `ZInQ.Contrib.TYZGenusFold.tyzLemma28Sym : ZInQ.Contrib.TYZDecomp.H29Genus.TYZLemma28Sym`
   (`ZInQKernel/Contrib/OneProof/TYZLemma28Sym.lean`, helpers in `ZInQKernel/Contrib/OneProof/TYZGenusFold/`).
2. **`hL29` follows from TYZ Theorem 2.1 alone** (VERIFIED; `#discharges`: `DISCHARGES [hL29] by
   ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21Pairs`, `still assumes: [H29Genus.TYZThm21Pairs]`):
   ```lean
   theorem tyzLemma29PrintedNe3_of_thm21Pairs (h21 : TYZThm21Pairs) : TYZLemma29PrintedNe3
   ```
   One printed leaf for one (count-neutral), but a better leaf: TYZ's Theorem 2.1, from which TYZ derive Lemma 2.9,
   instead of Lemma 2.9 itself, whose print is false at `n = 3`.
3. **`h11` cannot come from `TYZThm21Pairs`** (finding, §3): that leaf quantifies over *integer* sign choices of
   `𝓛`, so it is vacuous unless Theorem 1.1 holds (h11-reduce's observation for `hL29` applies verbatim). And no
   form of Theorem 2.1 at `n > 1` gives `𝓛(1)² = 1`: every relation is a product `𝓛(d₁)𝓛(d₂)` with `d₁d₂ = n > 1`.
   The target "2 → 1 TYZ hypotheses" is therefore reached only with the instance `n = 1` of Theorem 2.1, which
   could not be checked against the print here. Three folds are compiled (`scratch/tyz-genus/FoldCheck.lean`,
   standard axioms):

   | variant | `h11`, `hL29` replaced by | TYZ hypotheses | status of the new leaves |
   |---|---|---|---|
   | A | `h11`, `h21 : TYZThm21Pairs` | 2 → 2 | printed form (restricted); unread |
   | B | `h21C : TYZThm21PairsC`, `hL1 : TYZLcalOne` | 2 → 2 | `TYZThm21PairsC` printed form (restricted); `TYZLcalOne` a consequence of Tunnell 1983 at `n = 1` (TYZ assert it, L1082) |
   | C | `h21 : TYZThm21PairsC1` | **2 → 1** | **pending reading**: Theorem 2.1 at `n = 1` (counts as glue until a reader confirms that TYZ's Theorem 2.1 covers `n = 1`) |

   **Recommendation.** Fold C as soon as a reader with the source confirms that TYZ's Theorem 2.1 is stated for
   `n = 1` (the §2 setup is for `n ≡ 1, 2, 3 (mod 8)`, L499 per h29-split, and earlier readers list `n > 1` as a
   restriction of the print; what needs checking is that Theorem 2.1's hypotheses do not exclude `n = 1` and that
   its display reads `2^{k−a}` with `k = 0` there). Until then fold B (count-neutral; it turns TYZ Theorem 1.1 into
   glue and leaves TYZ Theorem 2.1 plus one numerical value), or A (the smallest change). The count-neutral
   `h11 + hL29 → TYZThm21Pairs + TunnellOddL1` is dominated by B (`TYZLcalOne` is the consequence of
   `TunnellOddL1` that is used).

## 1. TYZ Lemma 2.8 (`TYZLemma28Sym`), proved

Statement (h29-proof, `TYZLemma29Genus.lean:107`, unchanged): for squarefree `1 < n ≡ 1 (mod 8)`, admissible `τ`,
test vector `f`, `n = d₁d₂` with `d₂ ≡ 1 (mod 8)`: `quadPeriod n τ f d₂ = quadPeriod n τ f d₁`, where
`quadPeriod n τ f d = Σ_{t ∈ Cl_n} χ_{T(d)}(t) f(τ̂(clLift t))`, `χ_T = Π_{q ∈ T} χ_q` (project genus characters).

Proof (all in Lean; VERIFIED compiled):

* `T(d₁) = T(d₂)ᶜ`, so `χ_{T(d₁)} = χ_{T(d₂)} · χ_U`, `χ_U = Π_{q ∣ n} χ_q`. It suffices that **`f(τ̂ t) = 0`
  whenever `χ_U(t) = −1`** (`TYZGenusFold.tv_zero_of_gchar`).
* `Jacobi.lean`: for an integral ideal `I` with `N I` prime to `2n`, `(−n / N I) = 1` (prime-ideal induction with the
  project's `RouteK.Redei.prime_trichotomy`: split and ramified primes have norm `p` and `−n ≡ m² (mod p)`, inert ones
  norm `p²`), hence, for `n ≡ 1 (mod 4)`, `χ_U([I]) = (N I / n) = (n / N I) = χ₄(N I)` (`gchar_univ_mk0`, Jacobi
  reciprocity in Mathlib).
* `Ideles.lean`: for `α ∈ K_n^×` and `m ≥ 1`, the finite idele `aK = E·α + (1 − E)` (`E` the image in `𝔸ᶠ_{K_n}` of
  the idempotent of `𝔸ᶠ_ℚ` at the primes dividing `m`), with `τ̂(aK) = τ(α)` at the places dividing `m` and `1`
  elsewhere (`piQ_tauHat_aK`; through Tau Ceti's base change, which is `𝔸ᶠ_ℚ`-linear), and **its class**: if
  `(α) = I M` with `M + (N I) = O`, then `aK (N I) α` lies in `[I]` (`toClassGroup_aKU`, by comparing `v`-adic counts:
  Tau Ceti's `finprod_unitOfPrime_zpow_count`, `count_toPrincipalIdeal_eq_neg_log_valuation`).
* `Class.lean`: every class contains such `I` with `N I` prime to `2n`, and such `α` (`exists_mk0_coprime_nat`,
  `exists_alpha`, from Mathlib's `exists_sup_span_eq`); `nrd(τ(x)) = N(x)` (`normSq_tau`).
* `Local.lean`: if `y ∈ B^× twoRep(t') H` (`H = ⟨U_n, ℚ̂^×⟩ ⊂ SgC`, hfx-proof's local conditions), then `nrd(y)` is
  `g · c² · unit` at each odd place and `g · nrd(twoRep t') · κ` at `2`, `g = nrd γ > 0`, `κ ∈ 2^ℤ(1 + 4ℤ₂)`
  (`dc_norm`). Consequences: `chi0_eq_of_mem_DC`, and **`F_zero`**: hfx/hp23's generator `F` vanishes on the classes
  with `χ₀ = −1` (`chi0Rep · F` satisfies the same invariance and orthogonality, so it is `c F` by the rank-one
  clause; `c = 1` at the class of `1`, where `F` is odd).
* `tv_zero_of_gchar`: for `y = τ̂(aK)` with `I ∈ t`: `v_r(g · N I)` is even at every odd `r` and `g · nrd(twoRep t') ∈
  2^ℤ(1 + 4ℤ₂)`, so (hp23's `good_rat`, `not_good_int`) `N I · nrd(twoRep t') ≢ 3 (mod 4)`. If `χ_U(t) = −1` then
  `N I ≡ 3 (mod 4)`, so `nrd(twoRep t') ≡ 3`, i.e. `t'.2.2 ≠ 0`, where `F = 0`; and `f = ±F` (hp23's `tv_eq_sign`).

This is the argument sketched in h29-proof §4 (the `χ₀ ∘ nrd` twist), organised so that no global character on
`B̂^×` has to be defined: only reduced norms of one explicit idele per class and the subgroup `2^ℤ(1 + 4ℤ₂)`.

## 2. `hL29` from `TYZThm21Pairs` (variant A)

`tyzLemma29PrintedNe3_of_thm21Pairs h21 = H29Genus.tyzLemma29PrintedNe3_of_genus h21 tyzLemma28Sym`. `#discharges`
(`scratch/tyz-genus/Discharges-output.txt`, VERIFIED): `DISCHARGES [hL29] by
ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21Pairs`, `still assumes:
[ZInQ.Contrib.TYZDecomp.H29Genus.TYZThm21Pairs]`, `axioms: [propext, Classical.choice, Quot.sound]` (39 open
hypotheses, 9399 theorems checked).

## 3. `h11`: what Theorem 2.1 gives and what it cannot

* **F3.1 (integer sign choices).** `TYZThm21Pairs` quantifies over `ℓ : ℕ → ℤ` with `ℓ(m)² = 𝓛(m)²` for every
  squarefree `m ≡ 1, 3`; if Theorem 1.1 failed at one `m`, no such `ℓ` exists and the leaf holds vacuously. So
  `TYZThm21Pairs ⊬ h11` (VERIFIED by reading the definition, as h11-reduce §1 for `hL29`). It is still a consequence
  of the print in every case (vacuous or `ℓ = ±𝓛`).
* **F3.2 (`𝓛(1)²` is never isolated at `n > 1`).** The relations of Theorem 2.1 / Lemma 2.9 at `n` are in the
  products `𝓛(d₁)𝓛(d₂)`, `d₁d₂ = n`; at `n = 3`, `(3, 1)` gives `𝓛(3)²𝓛(1)² = (f_3(1)/3)² = 1` (t21-proof's
  `testVector_one`), the product only. Rescaling `𝓛(1) ↦ λ𝓛(1)`, `𝓛(m) ↦ 𝓛(m)/λ` changes only the relations with two
  factors `> 1`, and pinning `λ` from those needs exact quadratic periods at levels like `n = 51` (`P(3, 17)`) and
  `n = 17` (`h = 4`), Brandt computations not attempted. The project's rigorous bounds give only
  `0 < ‖𝓛(1)²‖ < 4` (t21-proof). TYZ themselves assert `𝓛(1) = 1` (L1082) and do not derive it.
* **Variant B (VERIFIED, compiled; `ZInQKernel/Contrib/OneProof/TYZThm11Genus.lean`).** `TYZThm21PairsC` = Theorem
  2.1 for every pair with *complex* sign choices (`ℓ : ℕ → ℂ`, `ℓ(m)² = 𝓛(m)²`; not vacuous: complex square roots
  exist). `tyzThm21Pairs_of_C`; `lemma29_coreC` (TYZ's proof of Lemma 2.9 over `ℂ`, with the proved Lemma 2.8);
  `tyzThm11Integral_of_thm21C : TYZThm21PairsC → TYZLcalOne → TYZThm11Integral` (TYZ's induction L1081–1088; `n = 3`
  from Theorem 2.1 at `(3, 1)`, `#μ(ℚ(√−3)) = 6` and `f_3(1) = ±3`, no Tunnell); `tyzLemma29PrintedNe3_of_thm21C`.
  `#discharges`: `DISCHARGES [h11] by ...tyzThm11Integral_of_thm21C still assumes: [TYZThm21PairsC, TYZLcalOne]`.
* **Variant C (VERIFIED, compiled; `ZInQKernel/Contrib/OneProof/TYZThm21PairsOne.lean`, `TYZGenusFold/QI.lean`).**
  `TYZThm21PairsC1` = `TYZThm21PairsC` for every squarefree `n ≥ 1` (odd classes), the display written
  `2^a P = ±2^k w_K 𝓛(d₁)𝓛(d₂)`, `a = 1` (equivalent to the previous form for `n > 1`; at `n = 1`, `k = 0`,
  `w_{ℚ(i)} = 2`, it reads `P(1, 1) = ±𝓛(1)²`). `tyzLcalOne_of_C1`: at `n = 1`, `Cl(ℚ(i)) = 1` (new: `pid_one`,
  Minkowski with `|d| = 4 < π²`; `torsionOrder_one = 4`), `P(1, 1) = f_1(1) = ±F(1)` is odd (hfx/hp23's generator
  exists at `n = 1`: `partition_one8` has no `n > 1` hypothesis), so `𝓛(1)²` is an odd integer, and t21-proof's
  certified bounds (`Re L(C₁, 1) ≥ 0.09`, `‖L(C₁, 1)‖ ≤ 1.26`, `∫₁^∞ dx/√(x³ − x) ≥ 2`) give `0 < 𝓛(1)² < 3`,
  hence `𝓛(1)² = 1`. Then `tyzThm11Integral_of_C1`, `tyzLemma29PrintedNe3_of_C1`. `#discharges`: `DISCHARGES [h11]
  by ...tyzThm11Integral_of_C1 still assumes: [TYZThm21PairsC1]`, and the same for `hL29`.

## 4. The leaves, rated

| leaf (Lean) | statement | rating, with the reason |
|---|---|---|
| `H29Genus.TYZThm21Pairs` (variant A; h29-proof's definition) | Thm 2.1, every pair, odd classes, `n > 1`, integer `ℓ` | **printed form, restricted** (h29-proof's rating stands): the display with `w_K`, the vanishing clause only for pairs with no factor `≡ 1 (mod 8)` (the ordered reading is false at `n ≡ 3`), odd classes, `n > 1`; integer `ℓ` makes it weaker still. Unread. |
| `TYZGenusFold.TYZThm21PairsC` (variant B) | the same with `ℓ : ℕ → ℂ` | **printed form, restricted**: TYZ's `𝓛(m)` is real (L338–353), so `ℓ = ±𝓛` and the sign is absorbed by `ε`; same restrictions as above. Unread. Uses the project's pin `𝓛(m)² = lcalSq m`, as every TYZ leaf. |
| `TYZDecomp.TYZLcalOne` (variant B; existing definition, `Leaves.lean`) | `lcalSq 1 = 1` | **consequence of a printed theorem**: Tunnell's formula at `n = 1` (`A(1) = B(1) = 2`; the implication is proved, `H11Reduce.lcalSq_one_of_tunnell`), equivalently `L(E, 1)/Ω = 1/8` for 32a2; TYZ assert it (L1082). Theorem numbers UNVERIFIED. |
| `TYZGenusFold.TYZThm21PairsC1` (variant C) | Thm 2.1, every pair, complex `ℓ`, odd classes, every squarefree `n ≥ 1` | **pending reading** (glue until cleared): printed form if TYZ's Theorem 2.1 covers `n = 1`. Evidence for: §2 is set for `n ≡ 1, 2, 3 (mod 8)` (L499, per h29-split), and the earlier leaves call `n > 1` a restriction of the print. Against: TYZ assert `𝓛(1) = 1` separately (L1082) rather than citing Theorem 2.1 at `n = 1`. The `n = 1` instance is true: `P(1, 1) = f_1(1) = ±1` (hp23's `F ∈ {±1}` on the classes with `χ₀ = 1`, read in the proof of `partition_one8`) and `𝓛(1)² = 1` (PARI, rv-nt-tyz `calL_small.py`). |

Kinds rows: `scratch/tyz-genus/kinds-rows.tsv` (`h21`, `h21C`, `hL1`, `h21one`).

## 5. Fold (manual: `h11`, `hL29` are `frozenTarget` binders)

`scratch/tyz-genus/FoldCheck.lean` (output `FoldCheck-output.txt`, all `[propext, Classical.choice, Quot.sound]`):
`frozenTarget_thm21` (variant A, written out in full as the new body of `frozenTarget`) and `frozenTarget_thm21'`
(the same through the current `frozenTarget`), `frozenTarget_thm21C` (B), `frozenTarget_thm21One` (C). The edits to
`Main.lean` (binders, arguments, imports) are in the docstrings there and in `scratch/tyz-genus/fold-spec.json`.

## 6. Files

* Contributions (new files only, under `ZInQKernel/Contrib/OneProof/`): `TYZLemma28Sym.lean` (Lemma 2.8, variant A),
  `TYZThm11Genus.lean` (variant B), `TYZThm21PairsOne.lean` (variant C); helpers `TYZGenusFold/{Jacobi, Local,
  Ideles, Class, QI}.lean` (1212 lines in all). They import `TYZLemma29Genus`, `TYZLemma29Mod2`, `TYZThm11Integral`,
  `TYZThm21At31`, `TYZTestVectorExists`, `TYZProp23Printed`, `LegendreThreeSquares`, `JonesPall`, never `Main`.
  No `sorry`, no `axiom`, no code that runs at build time.
* Checks: `scratch/tyz-genus/Discharges.lean` (+ output), `FoldCheck.lean` (+ output), `fold-spec.json`,
  `kinds-rows.tsv`, `log.md`.

## 7. What remains

* A reading of TYZ Theorem 2.1 (L554–559) and the §2 setup (L496–534) for `n = 1`: if covered, variant C removes one
  TYZ hypothesis (TYZ then rests, in this part, on Theorem 2.1 alone).
* Without that, an outright `𝓛(1)² = 1` in Lean (an exact evaluation of `L(C₁, 1)`) or exact quadratic periods at a
  level such as `n = 51` would also remove `TYZLcalOne`; neither was attempted.
