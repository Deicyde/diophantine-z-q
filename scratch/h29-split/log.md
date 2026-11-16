# h29-split results log

## Setup (2026-11-15 02:17 PST)
- Base 6edf020d (wip/h29-split). Build: `cp -r ~/dzq-check2/.lake/build` and `lean/.lake/build`
  (dzq-check2 at the same commit 6edf020d).
- **TYZ source absent**: `~/tyz-src/Period7.tex` does not exist; `find / -xdev` and `find ~ /tmp /data /var/tmp
  -maxdepth 6` for `*period7*`, `*1411.4728*` found nothing (VERIFIED). No network allowed. So every TYZ line
  number and statement below is quoted from earlier notes that read the source: `docs/research/nt-tyz.md` §1.2
  (states "VERIFIED against the source"), `rv-nt-tyz.md` (I2 row, B1), `rv-tyz-inputs.md` §1.2 and
  `scratch/rv-tyz-inputs/log.md` Step 1 (read L496–1162). Marked QUOTED below, not re-read.

## Target
- `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2` (ZInQKernel/Contrib/TYZDecomp/Leaves.lean:273):
  `∀ ℓ, (∀ m sqfree, m%8∈{1,3} → (ℓ m:ℂ)² = lcalSq m) → PropN.LemmaTwoEight ℓ`.

## Statements QUOTED (not re-read; source absent)
- Lemma 2.9 (L1062–1066), from nt-tyz §1.2: `Σ_{n=d₁d₂} ε(d₁,d₂)𝓛(d₁)𝓛(d₂) = Q(n)`, `ε = ±1`, non-ordered
  decompositions, `d₁, d₂ > 0`, `d₂ ≡ 1 (mod 8)`; setting of §2: `n ≡ 1, 2, 3 (mod 8)` positive squarefree (L499).
- Proposition 2.3 (L580–586), from nt-tyz §1.2: `f_n((B̂^×)²) ⊂ 1 + 2ℤ`; therefore `Q(n) ≡ g(n) (mod 2)`.
- `Q(n)`: genus period `Σ_{t∈2Cl_n} f_n(t)`, `f_n` TYZ's test vector (§2.2, Thms 2.4/2.6), left `K^×`-, right
  `Ô_K^×`-invariant on `K̂^×` (scratch/rv-tyz-inputs/log.md Step 1, Prop 2.3 proof L1134–1160 as read there;
  character formula `Σ' P(d₁,d₂) = 2^{h₂}Q(n)`, L1001).
- B1 (rv-nt-tyz, confirmed by rv-tyz-inputs §1.2): TYZ's proof gives `w_K Σ ε𝓛𝓛 = Q(n)`; `w_K = 3` at `n = 3`,
  `1` for other odd `n > 1`. Undecided whether Lemma 2.9 or Thm 2.1 is misprinted.

## Checks of the target against the quoted print (each VERIFIED by reading the Lean and the quotations)
- C1 classes: target covers squarefree `m ≡ 1, 3 (mod 8)`; §2 covers `n ≡ 1, 2, 3` positive squarefree (L499). Subset. OK.
- C2 `m = 1` excluded in clause 1 (`1 < m`); `m ≡ 3` implies `m ≥ 3`. Lemma at `n = 1` not used. OK (weaker).
- C3 index, `m ≡ 3`: non-ordered `{d₁, d₂}` with `d₂ ≡ 1` ↔ divisors `d ≡ 1` (the other factor is `≡ 3`, so each
  pair once). Lean: `m.divisors.filter (· % 8 = 1)`, term `L(m/d)·L(d)`. OK.
- C4 index, `m ≡ 1`: both factors `≡ 1`, `d ≠ m/d` (squarefree, `m > 1`), each pair once through `d² < m`. Lean:
  filter `d % 8 = 1 ∧ d*d < m`, term `L(d)·L(m/d)`. OK. Non-ordered is forced by TYZ's halving by the
  symmetry Lemma 2.8 (L1068–1077, quoted rv-nt-tyz I2).
- C5 signs: `ε = ±1` vanish mod 2. OK. Sign choice of `𝓛`: universal `ℓ` with `ℓ² = lcalSq`; a sign change of
  `ℓ(d)` flips the term, absorbed by `ε`. OK.
- C6 `w_K`: odd (1 or 3), vanishes mod 2. OK under either resolution of B1.
- C7 `g(m) = #2Cl(ℚ(√−m))` (TYZ L363, quoted nt-tyz); Lean `gNat m = gCl m = Nat.card (range (powMonoidHom 2))`
  on `ClassGroup (𝓞 (QNeg m))`. OK.
- C8 normalization of `𝓛`: inherited pin `lcalSq` (TYZDecomp §2, L338–353 as transcribed by earlier tasks); not
  re-checked here (source absent). UNCHECKED here.

## Lean: scratch/h29-split/H29Split.lean (compiled 02:45, 0 errors, no sorry; output H29Split.out)
- §1 printed forms with the genus period as parameter: `Lemma29Printed Q` (w ∈ {1, 3 at m=3}),
  `Prop23Cong Q`, `ClFun`, `sqClasses`, `genusPeriod f`, `Prop23Odd f`.
- §2 glue: `card_sqClasses : (sqClasses n).card = gCl n`; `genusPeriod_mod_two` (the "therefore" of Prop 2.3);
  `tyzLemma29Mod2_of_printed : Lemma29Printed Q → Prop23Cong Q → TYZLemma29Mod2`;
  `tyzLemma29Mod2_of_printedF : Lemma29Printed (genusPeriod f) → Prop23Odd f → TYZLemma29Mod2`.
- §3 inertness: `exists_printedQ_iff : (∃ Q, Lemma29Printed Q ∧ Prop23Cong Q) ↔ TYZLemma29Mod2`;
  `exists_printedF_iff : (∃ f, Lemma29Printed (genusPeriod f) ∧ Prop23Odd f) ↔ TYZLemma29Mod2`.
- §4 `thm11Mod2_iff (h11 : TYZThm11Integral) : TYZThm11Mod2 ↔ TYZLemma29Mod2`.
- Axioms of all five: [propext, Classical.choice, Quot.sound] (VERIFIED).

## Run 2 (2026-11-15 02:38 PST): source now present, genuine definitions
- `~/tyz-src/Period7.tex` now exists (3357 lines, read-only, dated 11-14 06:37). All checks below are
  re-done against it: **VERIFIED (read in the source)**. Nothing copied into the repository.
- Build: the run-1 build tree is gone; copied `~/dzq-check-w49/.lake/build` (78b9171f, ancestor of the base; only 4
  ZInQKernel files differ, none imported here), built `TYZChain.Lcal` (54 s). For `#discharges`, copied
  `~/dzq-wt/yu-prune-base/.lake/build` (c2ad4181 = base + TailZ32/Main change only) and built Main.

### Numbering (VERIFIED: `\newtheorem{thm}{Theorem}[section]`, lem/prop/cor/defn share the counter, L244–252)
- Section 2 environments: Thm 2.1 L554 (`thm2.1`), Thm 2.2 L571 (`LQ`), **Prop 2.3 L580** (`odd`), Thm 2.4 L613,
  Lemma 2.5 L646, **Thm 2.6 L809** (label `thm2.3`), Def 2.7 L842, **Lemma 2.8 L1009** (label `lem2.6`, symmetry),
  **Lemma 2.9 L1062** (unlabelled). No remark/example environments in L496–1163.

### Statement checks (each VERIFIED by reading the line range)
- S0 setting (L499): §2 assumes `n ≡ 1, 2, 3 (mod 8)` positive squarefree. Leaves restrict to `1, 3`: weaker. OK.
- S1 Lemma 2.9 (L1062–1066): `Σ ε(d₁,d₂)𝓛(d₁)𝓛(d₂) = Q(n)`, `ε = ±1`, non-ordered `n = d₁d₂`, `d₁, d₂ > 0`,
  `d₂ ≡ 1 (mod 8)`. Matches `Lemma29At` / `pairIdx` (C3, C4 of run 1 rechecked). OK.
- S2 the factor `w_K` (B1): proof of Lemma 2.9 (L1068–1077): non-ordered form of (PQ) is
  `Σ P = 2^{h₂−δ}Q`, `δ = 1` iff `n ≡ 1 (8)`; Thm 2.1 (L554–560): `P = ±2^{k−a} w_K 𝓛𝓛`, `a = 1` for odd `n`,
  `2w_K = #μ(K)`. With `h₂ + 1 = #(primes | disc)` (L993): `n ≡ 1 (8)`: disc `−4n`, `h₂ = k`, `2^{k−1}w_KΣ = 2^{k−1}Q`;
  `n ≡ 3 (8)`: disc `−n`, `h₂ = k − 1`, `2^{k−1}w_KΣ = 2^{k−1}Q`. So the proof gives `w_K Σ ε𝓛𝓛 = Q(n)`;
  `w_K = 3` for `ℚ(√−3)`, `1` for odd `n > 3` (and `2` for `n = 1`, excluded). B1 CONFIRMED. The leaf admits
  `w ∈ {1; 3 at n = 3}`: implied by the print and by the corrected statement. OK.
- S3 Prop 2.3 (L580–586): `f_n((B̂^×)²) ⊂ 1 + 2ℤ`; "Therefore" `Q(n) ≡ g(n) (mod 2)`. Leaf
  `TYZProp23Printed` = first assertion (all `h ∈ B̂^×`), restricted to `n ≡ 1, 3`. OK. The "therefore" is glue
  (`genusPeriod_mod_two` + `odd_on_sqClasses`), proved.
- S4 `Q(n)` (L566–568): `Q(n) = Σ_{t ∈ 2Cl_n} f_n(t)`, "well-defined up to signs". `genusPeriodTV`: sum over
  `sqClasses n` (= `2Cl_n`, written multiplicatively) of `f(τ̂(x_t))`, `x_t` a finite idele of class `t`. Independent
  of `x_t` by the invariances (that is `odd_on_sqClasses`'s argument). Leaves quantify over every generator `f`
  (both signs). OK.
- S5 `B`, `O_B` (L520–525): `B` ramified at `2, ∞` = Hamilton `ℚ + ℚi + ℚj + ℚk`, `i² = j² = −1`, `ij = k = −ji`
  (= Mathlib `ℍ[ℚ] = ℍ[ℚ,−1,0,−1]`); `O_B = O_B' + ℤζ`, `ζ = (−1+i+j+k)/2` (= `IsHurwitz`). OK.
- S6 `τ` (L527–534): `τ(O_{K_n}) ⊂ O_B`; for `n ≡ 1 (8)`, `τ(√−n) = ai + bj + ck`, `n = a²+b²+c²`, `a,b,c ∈ ℤ`,
  `4 | c`; Legendre, [JP, Thm 5] = Jones–Pall, Acta Math. 70 (1939) 165–191 (bib L3290–3292). `AdmissibleTau`
  matches; leaves are `∀ τ` admissible (TYZ: "Fix an embedding"), which is the printed content. OK.
- S7 `π`, `π_ℤ`, `U_n`, `R_n`, `f_n` (L536–550): `π` = JL of `f_E ∈ S₂(Γ₀(32))`, in `C^∞(B^×\B̂^×/Q̂^×)`;
  `π_ℤ` = integer-valued elements; `U_n = R̂_n^× · K_{n,2}^×`, `R_n = O_{K_n} + 4O_B` (conductor 32);
  `π_ℤ^{U_n}` free of rank 1 "as the special case χ = 1 in Theorem 2.6"; `f_n` a `ℤ`-generator, up to `±1`.
  `InPiZ`: left `B^×`, right `U_n` (generated subgroup) and `𝔸ᶠ_ℚ^×` invariance, integer values, and `π` pinned
  by `T_p`-eigenvalues `a_p(E)` at odd `p` (identification STANDARD: strong multiplicity one for GL₂ + JL
  injectivity + multiplicity one for `B^×`; one-dimensional constituents have eigenvalue `p + 1 ≠ a_p`).
- S8 Thm 2.6 (L809–840) at `χ = 1`: hypotheses root number `+1` of `L(E_K, s) = L(E,s)L(E_n,s)` (true for
  `n ≡ 1,2,3`), `O_K ⊂ O_B`; `π^{U,χ₂}` one-dimensional, `π_ℤ^{U,χ₂} = ℤf`. With `U₂ = ℤ₂^×(1+4O_{B,2})` (L603–605):
  `R_{n,2}^× = O_{K,2}^×(1+4O_{B,2})`, so `U_n = U·K₂^×` and `π^{U_n} = π^{U,1}`. Cases: `n ≡ 3`: `K₂ = ℚ₂(√−3)`;
  `n ≡ 1`: `K₂ = ℚ₂(√−1)`, `χ₂(ϖ) = 1`. `TYZTestVectorExists` (existence of a generator) is a consequence. OK.
- S9 Hecke normalization (computed, `checks.py`): `#hurwitzNorm p = 24(p+1)` for `p = 3, 5, 7, 11, 13`
  (VERIFIED); every norm-`p` Hurwitz `α` lies in `O_{B,p}^× ϖ O_{B,p}^×`; `α, α'` give the same right coset iff
  `α' ∈ αO_B^×` (`|O_B^×| = 24`, L674), so the sum is `24·T_p`. `apE p = p + 1 − #E(𝔽_p)` for `p ≤ 13`
  (VERIFIED; `a₅ = −2`, `a₁₃ = 6`).
- S10 Remark (not used): Thm 2.1's "P ≠ 0 only if d₂ ≡ 1 (mod 8)" read literally for `n ≡ 3 (8)` with
  `(d₁, d₂) ≡ (1, 3)` contradicts `χ_{d₁,d₂} = χ_{d₂,d₁}` (L994–995); its proof (L983–984) only shows the case
  `d₂ ≡ −1`. Lemma 2.9's sum (one factor `≡ 1`) is unaffected. Recorded, not pursued.
- S11 Prop 2.3's proof (L1134–1160) uses `χ₀(g) = 1` from Lemma 2.8's proof (needs `4 | c`): included in
  `AdmissibleTau`. OK.

### Lean (run 2)
- `scratch/h29-split/H29Split.lean` §5 (compiled 02:54, 0 errors): `qι`, `IsHurwitz`, `hurwitzHat`, `sqrtNeg`,
  `AdmissibleTau`, `tauHat` (+ `tauHat_algebraMap`), `tauHatU`, `RnHat`, `RnUnits`, `IsPlaceTwo`, `K2Units`, `Un`,
  `eAt`, `ιAt`, `apE`, `hurwitzNorm`, `quatOf`, `InPiZ`, `IsTestVector`, `clLift`, `genusPeriodTV`; leaves
  `TYZTauExists`, `TYZTestVectorExists`, `TYZLemma29Printed`, `TYZProp23Printed`; glue `tauHatU_mem_Un`,
  `odd_on_sqClasses`, `tvFun`, **`tyzLemma29Mod2_of_printedLeaves`**: axioms [propext, Classical.choice, Quot.sound].
- `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` (§1, §2, §5 of the scratch file; compiled 02:56, 0 errors).
- Build for the discharge check: `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges
  ZInQKernel.Contrib.OneProof.TYZLemma29Mod2` on the copied tree: success (12937 jobs; TailZ27–TailZ31, Main built);
  `ZInQ.OneProof.frozenTarget` axioms [propext, Classical.choice, Quot.sound].
- `#discharges` (`scratch/h29-split/DischargesH29.lean`, output `DischargesH29-output.txt`, VERIFIED 02:58):
  `DISCHARGES [h29] by ZInQ.Contrib.TYZDecomp.H29Split.tyzLemma29Mod2_of_printedLeaves`, still assumes
  `[TYZTauExists, TYZTestVectorExists, TYZLemma29Printed, TYZProp23Printed]`, axioms [propext, Classical.choice,
  Quot.sound]; `66 open hypotheses, 1255 theorems checked, 4 discharge one` (the other three are folded contributions).
- autofold: `scratch/h29-split/autofold.json` written; `autofold.py --dry-run` answers `not a field of the current
  bundles: ['h29']` (VERIFIED): autofold.py folds bundle fields only, and `h29` is a plain argument of
  `frozenTarget` (kinds.tsv row `frozenTarget h29 composite`). The fold is by hand (see the report).

### `TYZTauExists` reduced (run 2, 03:05–03:10)
- `scratch/h29-split/Tau.lean` (compiled, 0 errors): `LegendreJonesPall` (leaf: squarefree `n ≡ 1, 3 (mod 8)` is
  `a²+b²+c²`, `4 ∣ c` if `n ≡ 1`), `pq`, `pq_mul_self`, `tauOf` (Mathlib `QuadraticAlgebra.lift`), `tauOf_apply`,
  `trace_norm_int`, `int_of_sqfree_mul_sq`, `parity_one`, `parity_three`, `odd_of_three`, `admissible_tauOf`,
  **`tyzTauExists_of_legendreJonesPall`**: axioms [propext, Classical.choice, Quot.sound] (VERIFIED).
- Copied into the contribution file and the scratch file, with
  `tyzLemma29Mod2_of_printedLeaves_threeSquares (hL : LegendreJonesPall) hfx h29 h23 : TYZLemma29Mod2`.
- `checks.py`: `LegendreJonesPall` holds on 30 random squarefree `n ≡ 1, 3 (mod 8)`, `n < 10⁵` (VERIFIED, computed).
- `#discharges` rerun (VERIFIED 03:07): two lines `DISCHARGES [h29]`, by `tyzLemma29Mod2_of_printedLeaves`
  (assumes TYZTauExists, TYZTestVectorExists, TYZLemma29Printed, TYZProp23Printed) and by
  `tyzLemma29Mod2_of_printedLeaves_threeSquares` (assumes LegendreJonesPall, TYZTestVectorExists,
  TYZLemma29Printed, TYZProp23Printed); standard axioms; `66 open hypotheses, 1279 theorems checked, 5 discharge one`.
- autofold spec switched to the three-square theorem; dry run again `not a field of the current bundles: ['h29']`.

### Independent model review (03:10)
- A fresh agent read §5 and the four leaves against L496–1160 (code and source only): no false, vacuous or
  too-strong leaf found. Notes: (1) the Hecke-eigenvalue pin of `π^{U_n}` is a standard but unprinted bridge
  (docstring now says so); (2) TYZ's Legendre/Jones–Pall citation covers `n ≡ 1 (8)`; for `n ≡ 3` the leaf uses
  plain Legendre and the glue proves `a, b, c` odd (docstring updated); (3) `lcalSq` is inherited (C8, unchanged).
