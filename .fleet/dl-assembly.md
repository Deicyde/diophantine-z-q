# dl-assembly: Route K finished in Lean (DL, CR₃ ⇒ PC, main theorem on H_min, CR₃, 22P)

Branch `wip/dl-assembly`. It starts from `wip/pole-switch` and merges `wip/dl-system` and `wip/dl-slots`.
- The merges had no conflict: `ZInQKernel.lean` already received both import lines.
- The specification is `docs/research/slot-k.md` §2.5 (steps 0–6) and §4.1–4.2, `docs/research/rv-route-k.md` §4.2, and `rv-slot-k-proof.md` §8–9 (branch `wip/rv-slot-k-proof`).
- New modules are in `ZInQKernel/RouteK/Assembly/`. The root module is `ZInQKernel/RouteK/Assembly.lean`, imported from `ZInQKernel.lean`. The hypothesis is in `ZInQKernel/Hypotheses/CertifiedRank.lean`.

Checks:
- **Build.** `lake build ZInQKernel` succeeds. There is no `sorry`, no `native_decide` and no axiom, and my modules emit no warnings.
- **`python3 scripts/check_target.py`:** `FrozenTarget matches lean/Frozen/BoundedIntegerPolynomial.lean`.
- **`#print axioms`** gives `[propext, Classical.choice, Quot.sound]` for each of:
  - the main theorem and its variants `_of_sixContactEstimate`, `_of_twoSlopePattern`, `_of_addMulBound`, `_of_nodeCheck` and `_of_poleCompleteness`;
  - `poleCompleteness_of_certifiedRank`, `RouteK.descent_lemma` and `RouteK.poleSoluble_of_points`.
- **Finite checks.** No finite-check hypothesis is introduced. The only `decide` calls are on a few bits of `ZMod 2` / `ZMod 8`.

## Leaves

| # | article (slot-k) | Lean name | module | status |
| --- | --- | --- | --- | --- |
| 1 | §2.1 configuration of an odd squarefree `d` (L5) | `RouteK.primeCfg`, `RouteK.natConfig`, `RouteK.natClass`, `RouteK.SelmerCertified`, `RouteK.selmerCertified_of_primeCfg` | `Assembly/Realize.lean` | proved |
| 1 | §2.5 steps 1–4 (first curve `|n|`) | `RouteK.Slots.selmerCertified_d₁` (and `partners₁`, `gluingS`, `glueS_*`, `cfg₁_card`, `sigmaS`, `sigma₁`) | `Assembly/FirstCurve.lean` | proved |
| 1 | §2.5 steps 5–6 (second curve `|nθ|`) | `RouteK.Slots.selmerCertified_d₂` (and `gluing₂`, `isoS`, `cfg₂_card`, `sigma₂`) | `Assembly/SecondCurve.lean` | proved |
| 2 | §1.3 DL | `RouteK.descent_lemma` | `Assembly/DL.lean` | proved |
| 3 | §4.1 CR₃ | `ZInQ.CertifiedRank` (def, hypothesis) | `Hypotheses/CertifiedRank.lean` | statement (hypothesis by design) |
| 4 | §4.2 L6 (points ⇒ `PoleSoluble`) | `RouteK.poleSoluble_of_points` | `Assembly/Points.lean` | proved |
| 5 | §4.2 chain | `ZInQ.poleCompleteness_of_certifiedRank` | `Assembly/PoleCompleteness.lean` | proved |
| 6 | main theorem | `ZInQ.exists_bounded_integer_polynomial_defining_integers_of` with `(hH : SixContactMin) (hCR : CertifiedRank) (h22 : FixedPrimePattern)`; the same change in `_of_sixContactEstimate`, `_of_twoSlopePattern`, `_of_addMulBound`, `_of_nodeCheck`; new `_of_poleCompleteness` (takes `PoleCompleteness`) | `Main.lean` | proved |
| 7 | checks | build, `check_target.py`, `#print axioms` | — | done |

## How the statements read

**Configuration of `d`.** `natConfig d (hd : Odd d) : Config d.primeFactors` has:
- class `p mod 8`;
- bit `[y/x] = legBit x y`, following dl-system's convention `bit y x = [y/x]`;
- reciprocity from `legBit_reciprocity` together with `lam8_natCast_eq_lamBit`.

It is the instance `f = Subtype.val` of `primeCfg f`, the configuration of any injective family `f : κ → ℕ` of odd primes. All intermediate configurations are `primeCfg` on the abstract index types of Lemmas 1 and 2. As a result, `restrictLeft` and the reindexings hold by `rfl`.

**Class of `a`.** `natClass d a = (signBit a, 0, fun p => [p ∣ a])`.

**`SelmerCertified d a`** is `∃ hd : Odd d, (natConfig d hd).sols.card = 8 ∧ ∃ σ ∈ sols, σ.first = natClass d a`.

**DL** (`descent_lemma`). For admissible `B` there exist `m n : ℤ` with:
- `m ∣ 2730`, `β ∣ n`, `|n| % 8 = 5`, `|β| % 8 = 7`;
- `Squarefree n`, `Squarefree (nθ)`, `|nθ| % 8 = 5`;
- `SelmerCertified |n| β` and `SelmerCertified |nθ| β`.

Here `β = betaOf B m` and `θ = thetaOf B m`.

**CR₃** (`CertifiedRank`). This is the task's wording:

```
∀ (d : ℕ) (a : ℤ) (hd : d % 8 = 5), Squarefree d → Squarefree a → a ∣ (d : ℤ) → a.natAbs % 8 = 7 →
  (natConfig d _).sols.card = 8 → (∃ σ ∈ (natConfig d _).sols, σ.first = natClass d a) →
  ∃ x y : ℚ, y ^ 2 = x ^ 3 - (d : ℚ) ^ 2 * x ∧ x ≠ 0 ∧ IsSquare (x / a)
```

- The oddness proof `_` is `RouteK.odd_of_mod_eight_eq_five hd`.
- The docstring is the trust statement. It cites Proposition 0, Kriz Thm 10.13 with the corank lemma (Poonen–Stoll), or TYZ Thm 3.5(2) §3.3 with GZK (`docs/research/tyz-5b.md`), and RK9.
- It also explains why the point is non-torsion: the torsion classes are `±1, ±d`, and `|a| ≡ 7`, `d ≡ 5 (mod 8)`.

**L6** (`poleSoluble_of_points`). Assume:
- `B ≠ 0`, `m ∣ 2730`, `(m : ℚ) ≠ B`, and a nonzero rational `N`;
- `y₁² = x₁³ − N²x₁` and `y₂² = x₂³ − (Nθ)²x₂`;
- `x₁, x₂ ≠ 0`, and `x₁/β`, `x₂/β` are squares.

Then `PoleSoluble B`. This holds for the Route K `polePoly` (`A ± e`, `Az² ± eH`).

## Statement corrections and precisions

1. **The integer `n`.** The note takes `n = β q₀ Π r_p Π r_ℓ`; the Lean proof takes `n = d₁ = |β| q₀ Π r_p Π r_ℓ > 0`. The two have the same `|n|`, and the curves only see `|n|`.
   - DL keeps the task's form (`β ∣ n`, `|n|`, `|nθ|`).
   - DL adds `Squarefree n`, `Squarefree (nθ)` and `|nθ| % 8 = 5`: CR₃ needs them, and its hypotheses `Squarefree d`, `d ≡ 5` are stated on `d = |n|`, `|nθ|`.
2. **CR₃ conventions.** `d` is a natural number, using `C_d = C_{−d}`. `a` is signed. "`x ∈ aℚ*²`" is written `x ≠ 0 ∧ IsSquare (x / a)`.
   - The class of `a` has `a₁ = 0`. This is faithful because `a ∣ d` and `d` is odd.
   - The narrowing `d ≡ 5`, `|a| ≡ 7 (mod 8)` is the task's. It matches what DL produces.
   - No other adjustment was needed.
3. **L6 is more general than needed.** It holds for every nonzero rational `N` and every signed divisor `m ≠ B`; admissibility is not used.
   - The multiplier bits come from `exists_multiplier_bits`, by the factorization `|m| = gcd(|m|,2)·gcd(|m|,3)·gcd(|m|,5)·gcd(|m|,7)·gcd(|m|,13)`. No search is needed.
   - `PoleCompleteness` uses only `B` admissible ⇒ `(m : ℚ) ≠ B`, since `0 < B < 1/2`.
4. **`[q₀/ℓ] = 0` is unused**, as the three referees found. The field `Slots.q₀_sym_T` is referenced nowhere in `Assembly/`. In step 5 those symbols lie inside the glued set.
5. **Step 5 without Jacobi symbols**, as rv-slot-k-proof §9.6 suggests. Take `p ∈ P`:
   - `Σ_{ℓ∈T} [ℓ/p] = [θ/p] = 0`, by (θ4) and `legBit_prod`, with `θ = Π_{ℓ∈T} ℓ` (θ is positive and squarefree);
   - `Σ_{ℓ∈T} [p/ℓ] = [θ/p] + λ_p Σ λ_ℓ = 0`, by `legBit_reciprocity` prime by prime and `Σ λ_ℓ = λ(θ mod 8) = 0` (`lam8_prod`).
6. **Value of `v_{q₀}` in step 4.** The lifted class has `v_{q₀} = s + x + 1 = 0`, since `x = s + 1`. Step 6 then reads `u_{r_ℓ} = [|β|/ℓ] + λ_ℓ s = (sλ_ℓ + [β/ℓ]) + sλ_ℓ = 0` (`legBit_natAbs`, (θ3)). This agrees with the note.

## Lemmas added beyond the leaves

I grepped `ZInQKernel/` before choosing these names; no clashes.

- **`Realize.lean`:** `natCast_zmod8_of_mod`, `natCast_mem_oddClasses`, `lam8_natCast_eq_lamBit`, `primeCfg_cls`, `primeCfg_bit`, `primeCfg_lam`, `squarefree_prod_primes`, `primeFactors_prod_primes`, `odd_prod_primes`, `prime_ne_two_of_mem_primeFactors`, `odd_of_mod_eight_eq_five`.
- **`Data.lean`:**
  - Structure `Inputs β θ p₀`: β odd, squarefree, `|β| ≡ 7`, `p₀ ∈ P`; `θ > 0`, `θ ≡ 1`, θ squarefree; coprime; (θ3) and (θ4) in bits.
  - Its lemmas: `Inputs.β_ne_zero`, `θ_ne_zero`, `odd_θ`, `mem_P`, `mem_T`, `disjoint`, `not_mem_of_not_dvd`, `prod_P`, `prod_T`, `θ_natAbs_mod`.
  - Types `GP β p₀ = {p // p ∈ P ∖ {p₀}}` and `TP θ`.
  - Index maps `Slots.pP`, `rPv`, `rTv`, `qT`, `fS`, `f₁`, `f₂`, with primality (`*_prime`), distinctness (`q₀_not_mem`, `rPv_not_mem`, `rTv_not_mem`) and injectivity (`pP_injective`, `rPv_injective`, `rTv_injective`, `qT_injective`, `fS_injective`, `f₁_injective`, `f₂_injective`).
- **`FirstCurve.lean`:** `prime_dvd_β_iff`, `prod_pP`, `sum_pP_q₀`, `restrict₁`, `glueS_card`, `cfgS_card`, `tau₀`, `tau₀_mem`, `sigmaS_*`, `sigma₁_mem`, `sigma₁_u`, `d₁`, `d₁_eq`, `d₁_eq'`, `β_dvd_d₁`, `squarefree_d₁`, `prod_rPv_zmod`, `prod_rTv_zmod`, `d₁_zmod`, `d₁_mod`.
- **`SecondCurve.lean`:** `unitSumEquivOption`, `legBit_natAbs`, `sum_pP`, `prod_qT`, `sum_qT`, `θ_eq_prod`, `sum_T_legBit_P`, `sum_T_lamBit`, `sum_T_legBit_P'`, `glue₂_cls_none`, `sum_T_S'`, `isoS`, `tau₂`, `tau₂_mem`, `sigma₂`, `sigma₂_mem`, `sigma₂_u_R`, `sigma₂_u`, `d₂`, `d₂_eq`, `squarefree_d₂`.
- **`DL.lean`:** `sqf_zero`, `inputs_of_admissible`.
- **`Points.lean`:** `gcd_prime_bit`, `exists_multiplier_bits`.
- **`PoleCompleteness.lean`:** `ZInQ.natAbs_cast_sq`.

## Files edited outside `RouteK/Assembly/`

- **`ZInQKernel/Main.lean`:**
  - imports `Hypotheses.CertifiedRank` and `RouteK.Assembly.PoleCompleteness`;
  - the five theorems now take `hCR : CertifiedRank`;
  - new `_of_poleCompleteness`;
  - rewritten module docstring (H_min, CR₃, 22P; PC, MW and CAT are theorems).
- **`ZInQKernel/Hypotheses/Pole.lean`:** docstrings only. The module doc and `PoleCompleteness` now say that PC (Route K) is the theorem `poleCompleteness_of_certifiedRank`, not a hypothesis of the main theorem. The definitions are unchanged.
- **`KERNEL_PLAN.md`:**
  - the PC row of the table;
  - the statement block (`hCR : CertifiedRank`);
  - a new paragraph on CR₃ and its justification;
  - the status line (H_min, CR₃, 22P).
- **`README.md`:** the hypothesis sentence of the fork notice. It said "pole completeness"; it now says CR₃, with PC proved from it. This edit was not requested, but the old sentence had become false.
- **`ZInQKernel.lean`:** `import ZInQKernel.RouteK.Assembly`.

## Problems

None blocking. Total Lean time was small: about 5 min per full build and a few seconds per module.

## Suggestions for the next agent / the lead

- **Blueprint.** Add articles for L5 (`natConfig`, `SelmerCertified`), the two curves, DL, L6, CR₃ and `poleCompleteness_of_certifiedRank`, with the `lean:` names above. Update the main-theorem article: its `lean:` list should add `_of_poleCompleteness`, and its hypotheses now read H_min, CR₃, 22P. Mark PC as a theorem from CR₃.
- **Missing reference.** The CR₃ docstring and KERNEL_PLAN cite `docs/research/tyz-5b.md`, which is on `wip/tyz-5b` and not merged into this branch. Merge it, or adjust the citation.
- **Stale cross-checks.** As pole-switch noted, `construction/` and upstream `lean/ZInQ/PolePolynomial.lean` still encode `x + 3ℓ`.
- **Possible narrowing of CR₃.** CR₃ could be narrowed further, to the configurations of slot-k §2.4 shape. The note advises against it, and I did not do it.
- **Lean-facing improvement.** State Proposition 0 itself, as `Σ(𝒞_d)` ≅ an explicit set of pairs of square classes cut out by local conditions. That would let a future CR₃ mention genuine Selmer groups. Out of scope here.
