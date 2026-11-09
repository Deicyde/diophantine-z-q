# cr3-check: does `ZInQ.CertifiedRank` (CR₃) say what its docstring claims?

Branch `wip/cr3-check`, based on `wip/dl-assembly` (020b71f). Nothing under `ZInQKernel/`, `blueprint/` or
`docs/` was changed. All new files are in `scratch/cr3-check/`, which `ZInQKernel` does not import.
`lake build ZInQKernel` succeeds on this branch (9584 jobs).

**Verdict: CR₃ is faithful.**
- The Lean system `Σ(𝒞_d)` of `ZInQ.RouteK.natConfig d` is, element for element, the 2-Selmer group
  `Sel₂(C_d)` in the coordinates of Proposition 0, with Kummer map `P ↦ (x, x − d)`.
- `natClass d a` is the class of `a` in the first coordinate, which is the class of the abscissa `x`.
- No convention slip was found, either by comparing symbol by symbol or by evaluation:
  - 40 values of `d` (2 to 5 primes, primes in every class mod 8), plus 12 slot configurations
    with primes of up to 34 digits;
  - 0 mismatches against two independent exact descents and against PARI.
- On every curve where a point was found, the class predicted by the Lean hypothesis carries a
  rational point with `x ∈ aℚ*²`. That point is CR₃'s conclusion.

## 1. Conventions, symbol by symbol

Sources: slot-k §2.1 (S), descent-alt §4.1 (A), and Lean (L): `RouteK/System/Config.lean`, `Selmer.lean`,
`Slots/Symbols.lean`, `Slots/Construction.lean` (`signBit`), `Assembly/Realize.lean`, `Hypotheses/CertifiedRank.lean`.

| item | S / A | Lean | agrees |
|---|---|---|---|
| curve, Kummer map | `C_d: y² = x³ − d²x`; `P ↦ (x, x − d)`, `(0,0) ↦ (−1,−d)`, `(d,0) ↦ (d,2)`, `(−d,0) ↦ (−d,−2d)` | not in Lean, except the conclusion `y² = x³ − d²x` | yes |
| residue bit | `[x/p] = 0` iff `x` is a square mod `p` | `legBit p x = if IsSquare (x : ZMod p) then 0 else 1` | yes |
| matrix entry | S: `L_{xy} = [y/x]`; A: `L_ij = [p_j/p_i]` | `Config.bit y x = [y/x]`; `natConfig`: `bit a b = legBit b a` (= `[a/b]`) | yes |
| Monsky `K` | S: `(Ku)_x = Σ_{y≠x}[y/x](u_y+u_x)`; A: `A = L + diag(L𝟏)` | `monsky u x = Σ_{y ≠ x} bit y x * (u y + u x)` | yes; A and S are the same matrix |
| `λ`, `μ` | `λ = [c ≡ 3 (4)] = [−1/p]`, `μ = [c ≡ 3,5 (8)] = [2/p]` | `lam8 c = [c = 3 ∨ c = 7]`, `mu8 c = [c = 3 ∨ c = 5]` on `ZMod 8` | yes; `μ_p = [2/p]` by the second supplement |
| classes | `c_p = p mod 8`, `c(𝒞) = Π c_p = d mod 8` | `cls p = (p : ZMod 8)`, `prodClass = ∏ cls` | yes |
| E1 | `(Ku)_x + λ_x v_x = a₀λ_x + a₁μ_x` (A: `Au + D_λ v = a₀λ + a₁μ`) | `E1` | yes |
| E2 | `μ_x u_x + (Kv)_x + λ_x v_x = b₀λ_x + b₁μ_x` (A: `D_μ u + (A + D_λ)v = …`) | `E2` | yes |
| real place | `a₀ = b₀` (`d > 0`) | third conjunct of `IsSol` | yes |
| 2-adic row, `c = 5` | `a₁ = 0, b₁ = μ·u, λ·v = λ·u` | `twoAdicRows 5 … ↔ a1 = 0 ∧ b1 = mu ∧ lv = lu` (`twoAdicRows_five`) | yes |
| other 2-adic rows (`c = 1, 3, 7`) | as in the table of S and A | `twoAdicRows` | yes (CR₃ uses only `c = 5`) |
| class of a solution | `a = (−1)^{a₀}2^{a₁}Πp^{u_p}`, `b = (−1)^{b₀}2^{b₁}Πp^{v_p}` | `Unknowns.first = (a0, a1, u)` | yes |
| class of `a ∣ d` | — | `natClass d a = (signBit a, 0, p ↦ [p ∣ a])`, `signBit a = [a < 0]` | yes |
| hypothesis "dim 3" | `dim Sel₂ = 3` | `sols.card = 8` (the solutions form a subspace) | yes |
| conclusion | a point with `x ∈ aℚ*²` | `∃ x y : ℚ, y² = x³ − d²x ∧ x ≠ 0 ∧ IsSquare (x / a)` (`a ≠ 0` since `a ∣ d > 0`) | yes |

**By hand.** I re-derived the odd-place rows from the local image `⟨(d,2), (−1,−d)⟩` at `p ∣ d`:
- The residue bit of the unit part of `a` is `a₀λ_p + a₁μ_p + Σ_{q≠p} u_q[q/p]`. Setting it equal to
  `u_p[d_p/p] + v_p[−1/p]` gives exactly E1_p.
- The bit of `b` is `b₀λ_p + b₁μ_p + Σ_{q≠p} v_q[q/p]`. Setting it equal to `u_p[2/p] + v_p[−d_p/p]`
  gives exactly E2_p.
- All four valuation patterns `(u_p, v_p)` check against the torsion images `1`, `(d,2)`, `(−1,−d)`
  and `(−d,−2d)`.

The 2-adic row for `c = 5` was not checked by hand. It is checked numerically: the independent
descent computes the image at 2 afresh for every `d`, from genuine 2-adic points.

**Remarks.**
- In CR₃ the hypothesis `Squarefree a` follows from `a ∣ d` and `Squarefree d`. It is redundant but
  harmless.
- The oddness proof in `natConfig d _` is a `Prop`, so the choice of proof does not matter.

## 2. How the Lean values were obtained (`scratch/cr3-check/Eval.lean`)

`natConfig` cannot be evaluated directly: its bits use a classical `if IsSquare`. `Eval.lean` (namespace
`ZInQ.RouteK.CR3Check`, no `sorry`) therefore defines computable mirrors and proves that they have the
same values:

- **The bit.** `legBitC p a` is Euler's criterion via `Nat.powMod`. `legBit_eq_legBitC` proves
  `legBit p a = legBitC p a` for a prime `p` and `a ≢ 0`, using `ZMod.euler_criterion`.
- **Factored `d`.** `natConfigC d hd` keeps the same classes and has bits `legBitC` off the diagonal.
  - `natConfig_sols_eq : (natConfig d hd).sols = (natConfigC d hd).sols`, an equality of Finsets.
  - `report d` returns the number of solutions and, for every signed divisor `a` with `|a| ≡ 7 (8)`, the
    decision of `∃ σ ∈ sols, σ.first = natClass d a`.
  - `report_spec`: `report d = some ((natConfig d hd).sols.card, …decide (∃ σ ∈ (natConfig d hd).sols, σ.first = natClass d a)…)`.
  - `solPairs d` lists all solutions as pairs of signed integers `(a, b)`, for an element-by-element
    comparison.
- **Unfactored `d`** (slot primes of about 30 digits; `Nat.primeFactors` would need trial division).
  - `evalList l as` evaluates `primeCfg (i ↦ l[i])` from a bit table computed once.
  - `natConfig_prod_card` and `natConfig_prod_first` transport the result along
    `Fin l.length ≃ l.prod.primeFactors`.
  - `evalList_spec`: if `l` is a list of distinct odd primes and `evalList l as = some r`, then `r` is
    the number of solutions of `Σ(𝒞_{l.prod})` together with the decisions for `natClass l.prod a`.
  - The primality of the entries is a hypothesis of `evalList_spec`. It was checked outside Lean,
    with PARI `isprime`, which gives a proof.
- **Trust.** The bridging theorems are kernel-checked. The numbers come from `#eval`, which runs
  compiled code with GMP, not the kernel.
- **Output files.** The `#eval` lines are at the end of `Eval.lean` (3 min 20 s in total). The
  output is in `out_lean_40.txt` and `out_lean_slot5.txt`.

## 3. Independent computations

1. **`sel2_indep.py`**, written for this task from the definition of `Sel₂` and nothing else. Its
   method:
   - It does not use the system, nor the other scratch descents.
   - Every local image (`∞`, `2` and each odd `p ∣ d`) is computed as the span of the Kummer images
     of genuine local points: the 2-torsion points, plus points found by testing whether
     `x(x−d)(x+d)` is a square in `ℚ_v`.
   - A span is accepted only when it reaches the known dimension `dim E(ℚ_v)/2E(ℚ_v)`: 2 at odd `p`,
     3 at `v = 2`, 1 at `v = ∞`.
   - `Sel₂` is the kernel of the localization map on `⟨−1, 2, p | d⟩²`.
2. **`sel2.py`** from `origin/wip/rv-slot-k-proof`. It assumes that the torsion images span the odd
   local images; its image at 2 also comes from 2-adic points.
3. **PARI/GP 2.17** (`cypari2`):
   - `ellrank`: `dim Sel₂ = 2 + r₂ + s` (the 2-torsion rank is `T = 2`);
   - `ellanalyticrank`, `ellheegner`, `ellrank` with effort, for the points.
4. **`slotk.certified`** (`sel2cong.py` of rv-route-k) for the slot configurations, as
   `slotk.py` itself uses it.

## 4. Comparison table (step 2 and step 3; `compare.py`, `out_compare40.txt`, `cmp40.json`)

The test set is `pick.py`, seed 20261109: 40 squarefree `d ≡ 5 (mod 8)` with 2, 3, 4 and 5 primes below 200
(10 of each), and primes in all four classes mod 8.

The column "Sel₂ sets equal" means three things:
- the full sets of pairs `(a, b)` from Lean (`solPairs`), `sel2_indep` and rv `sel2.py` are equal;
- for every signed divisor `a` with `|a| ≡ 7`, the Lean decision `∃ σ, σ.first = natClass d a` equals
  "`a ∈ π₁(Sel₂)`" by `sel2_indep`;
- PARI's dimension equals the others.

The last column covers the CR₃ cases: "found" means a point `(x, y)` with `x ≠ 0` and `x/a` a square,
checked with exact rational arithmetic.

| d | primes (class mod 8) | Lean #sols | dim Sel₂: Lean / indep / rv sel2.py / PARI | Sel₂ sets equal | a with \|a\| ≡ 7 and Lean σ.first = natClass d a | CR₃ hyp. | point with x ∈ aℚ*² (a > 0 / a < 0) |
|---|---|---|---|---|---|---|---|
| 2413 | 19 (3) 127 (7) | 8 | 3 / 3 / 3 / 3 | yes | ±127 | yes | found (ellrank(effort=0)) / found (ellrank(effort=0)) |
| 5549 | 31 (7) 179 (3) | 8 | 3 / 3 / 3 / 3 | yes | ±31 | yes | found (ellrank(effort=0)) / found (ellrank(effort=0)) |
| 1133 | 11 (3) 103 (7) | 8 | 3 / 3 / 3 / 3 | yes | ±103 | yes | found (ellrank(effort=0)) / found (ellrank(effort=0)) |
| 13493 | 103 (7) 131 (3) | 8 | 3 / 3 / 3 / 3 | yes | ±103 | yes | not found / not found |
| 14141 | 79 (7) 179 (3) | 8 | 3 / 3 / 3 / 3 | yes | ±79 | yes | found (ellrank(effort=0)) / found (ellrank(effort=0)) |
| 3781 | 19 (3) 199 (7) | 8 | 3 / 3 / 3 / 3 | yes | ±199 | yes | found (ellrank(effort=0)) / found (ellrank(effort=0)) |
| 13973 | 89 (1) 157 (5) | 32 | 5 / 5 / 5 / 5 | yes | — | no | — |
| 2501 | 41 (1) 61 (5) | 32 | 5 / 5 / 5 / 5 | yes | — | no | — |
| 4181 | 37 (5) 113 (1) | 8 | 3 / 3 / 3 / 3 | yes | — | no | — |
| 11461 | 73 (1) 157 (5) | 8 | 3 / 3 / 3 / 3 | yes | — | no | — |
| 106997 | 11 (3) 71 (7) 137 (1) | 8 | 3 / 3 / 3 / 3 | yes | ±9727 | yes | not found / not found |
| 280789 | 17 (1) 83 (3) 199 (7) | 8 | 3 / 3 / 3 / 3 | yes | ±3383 | yes | found (ellrank(effort=0)) / found (ellrank(effort=0)) |
| 731573 | 61 (5) 67 (3) 179 (3) | 8 | 3 / 3 / 3 / 3 | yes | ±4087 | yes | not found / not found |
| 1214501 | 73 (1) 127 (7) 131 (3) | 8 | 3 / 3 / 3 / 3 | yes | ±127 | yes | not found / not found |
| 518629 | 37 (5) 107 (3) 131 (3) | 8 | 3 / 3 / 3 / 3 | yes | ±4847 | yes | not found / not found |
| 11077 | 11 (3) 19 (3) 53 (5) | 8 | 3 / 3 / 3 / 3 | yes | ±1007 | yes | found (ellrank(effort=0)) / found (ellrank(effort=0)) |
| 433493 | 41 (1) 97 (1) 109 (5) | 8 | 3 / 3 / 3 / 3 | yes | — | no | — |
| 1427077 | 73 (1) 113 (1) 173 (5) | 32 | 5 / 5 / 5 / 5 | yes | — | no | — |
| 527669 | 47 (7) 103 (7) 109 (5) | 8 | 3 / 3 / 3 / 3 | yes | — | no | — |
| 74269 | 13 (5) 29 (5) 197 (5) | 32 | 5 / 5 / 5 / 5 | yes | — | no | — |
| 22212173 | 29 (5) 37 (5) 127 (7) 163 (3) | 8 | 3 / 3 / 3 / 3 | yes | ±4727 | yes | not found / not found |
| 303405 | 3 (3) 5 (5) 113 (1) 179 (3) | 8 | 3 / 3 / 3 / 3 | yes | ±895 | yes | found (ellrank(effort=0)) / found (ellrank(effort=0)) |
| 138165 | 3 (3) 5 (5) 61 (5) 151 (7) | 8 | 3 / 3 / 3 / 3 | yes | ±15 | yes | found (ellrank(effort=4)) / found (ellrank(effort=4)) |
| 5671693 | 17 (1) 37 (5) 71 (7) 127 (7) | 8 | 3 / 3 / 3 / 3 | yes | ±127 | yes | not found / not found |
| 19886717 | 31 (7) 59 (3) 83 (3) 131 (3) | 8 | 3 / 3 / 3 / 3 | yes | ±31 | yes | not found / not found |
| 64057229 | 43 (3) 79 (7) 109 (5) 173 (5) | 8 | 3 / 3 / 3 / 3 | yes | ±1489703 | yes | not found / not found |
| 86948237 | 19 (3) 131 (3) 181 (5) 193 (1) | 8 | 3 / 3 / 3 / 3 | yes | — | no | — |
| 1981293 | 3 (3) 73 (1) 83 (3) 109 (5) | 8 | 3 / 3 / 3 / 3 | yes | — | no | — |
| 38820013 | 43 (3) 73 (1) 83 (3) 149 (5) | 32 | 5 / 5 / 5 / 5 | yes | — | no | — |
| 3896269 | 13 (5) 23 (7) 83 (3) 157 (5) | 8 | 3 / 3 / 3 / 3 | yes | — | no | — |
| 41594005133 | 101 (5) 113 (1) 139 (3) 157 (5) 167 (7) | 8 | 3 / 3 / 3 / 3 | yes | ±2465999 | yes | not found / not found |
| 5361627277 | 41 (1) 73 (1) 83 (3) 113 (1) 191 (7) | 8 | 3 / 3 / 3 / 3 | yes | ±571663 | yes | not found / not found |
| 4584527461 | 19 (3) 67 (3) 101 (5) 181 (5) 197 (5) | 8 | 3 / 3 / 3 / 3 | yes | ±3439 | yes | not found / not found |
| 3741938677 | 41 (1) 61 (5) 67 (3) 137 (1) 163 (3) | 8 | 3 / 3 / 3 / 3 | yes | ±559919 | yes | not found / not found |
| 15335133 | 3 (3) 11 (3) 43 (3) 101 (5) 107 (3) | 8 | 3 / 3 / 3 / 3 | yes | ±356631 | yes | not found / not found |
| 252336837 | 3 (3) 41 (1) 73 (1) 157 (5) 179 (3) | 8 | 3 / 3 / 3 / 3 | yes | ±28103 | yes | not found / not found |
| 57049269 | 3 (3) 23 (7) 31 (7) 149 (5) 179 (3) | 32 | 5 / 5 / 5 / 5 | yes | ±31, ±12351, ±26671, ±318711 | no | — |
| 365904845 | 5 (5) 43 (3) 53 (5) 163 (3) 197 (5) | 8 | 3 / 3 / 3 / 3 | yes | — | no | — |
| 71760581861 | 97 (1) 113 (1) 167 (7) 197 (5) 199 (7) | 32 | 5 / 5 / 5 / 5 | yes | ±18871, ±2181239 | no | — |
| 1320054901 | 11 (3) 41 (1) 103 (7) 157 (5) 181 (5) | 8 | 3 / 3 / 3 / 3 | yes | — | no | — |

**Result: 0 mismatches in 40.**
- Every Lean count is a power of 2, 8 or 32, and equals the true `2^{dim Sel₂}`.
- The 2-Selmer groups agree element for element, so the comparison covers the second coordinates too.
- 24 of the 40 `d` satisfy CR₃'s hypothesis for some `a`, always for both signs `±a`.
- Where `dim Sel₂ = 5`, PARI reports `s = 2`: `Ш[2] ≠ 0` and rank 1. CR₃ correctly excludes these cases,
  because its hypothesis requires 8 solutions.

## 5. CR₃'s conclusion on examples (step 4; `points.py`, `points2.py`, `out_points*.txt`, `points40_*.json`, `points2_*.json`)

There are 24 CR₃-hypothesis curves and 48 pairs `(d, ±a)`. Each found point was rechecked with exact
`Fraction` arithmetic: `y² = x³ − d²x`, `x ≠ 0` and `x/a` a square.

- **Found: 9 curves, 18 pairs** (both signs on each). The curves are `d = 1133, 2413, 3781, 5549, 11077, 14141, 138165, 280789, 303405`.
  - `P = G + T`, with `G` the point returned by `ellrank` (effort 0, or 4 for 138165) and `T ∈ C_d[2]`.
  - The point `G + T` whose class is the Lean class `a` has `x/a` a square, for `a` and for `−a`.
    This confirms that Lean's "first coordinate" is the class of the abscissa `x`.
  - Example: `d = 5549 = 31·179`, `a = 31`, `x = 963204499900/171636201`, `y = 141133134585568490/2248605869301`.
  - The full `x, y` are in `points40_*.json`.
- **Not found within the limits: 15 curves.** The curves are `13493, 106997, 518629, 731573, 1214501, 5671693, 15335133, 19886717,
  22212173, 64057229, 252336837, 3741938677, 4584527461, 5361627277, 41594005133`. Three searches were run:
  - `ellrank` with effort 0, 4, 8 and 12 (`points.py`), then 20 and 30 (`points2.py`, 30 min alarm each);
  - `ellheegner` for `d < 2·10⁶`. It returned no point: in `points2.py` the call ended without a
    point under a 60 min alarm, and a separate 20 min try on `d = 106997` hit its alarm;
  - a direct search on the quartic `w² = a(s⁴ − e²)`, `e = d/a`. Every point with `x ∈ aℚ*²` comes from
    one of its points, with `x = as²`. Searched with `hyperellratpoints` up to naive height `10⁷`
    (`quartic.py`, `quartic_found.txt`).
- **Why they were not found.** The BSD-predicted generator heights, assuming `#Ш = 1`
  (`out_heights.txt`), are:
  - 94.5 for `d = 13493`, 77.7 for 106997, 150 for 518629, 356 for 731573 and 515 for 1214501;
  - against 49.2 and 23.5 for the found `d = 2413` and 1133, whose `x` have 45 and 22 digits.

  The generators of the curves not found therefore have coordinates of roughly 90 to 500 digits.
  That is beyond `ellrank`'s search and beyond a height-`10⁷` quartic search; only a 4-descent or a
  completed Heegner computation would reach them. This is a search limit, not evidence against
  CR₃: on these curves the Lean system still equals the exact `Sel₂`, and the analytic rank is 1
  wherever it could be computed.
- **No counterexample was seen.** No pair `(d, a)` had the Lean hypothesis true together with evidence
  against the conclusion.

**Analytic ranks** (`anrank.py`, `out_anrank.txt`). These are the 12 CR₃-hypothesis curves with
`d < 2·10⁶`. For all of them the root number is −1, the analytic rank is 1 and `L'(C_d, 1) ≠ 0`
(between 2.0 and 21.7). This is consistent with the rank-one input of the trust statement (TYZ or
Kriz). It is a numerical check only.

## 6. The descent construction end to end (step 5; `slot5.py`, `slot5.json`, `out_slot5.txt`, `out_lean_slot5.txt`)

`slot5.py` searches for admissible `B = N/D²` with prescribed `ω(β), ω(θ)`, where
`N = 2⁴3⁴5⁴7⁴13⁴·u`. It runs `slotk.choose_m` and `slotk.construct` from `scratch/slot-k/slotk.py`, with
PARI's `kronecker` as `JAC`, as in `run_dl.py`. B5 and B6 force `m = −1`, to test `β < 0` (`signBit β = 1`).
The primes of `|n| = |β| q₀ Π r_p Π r_ℓ` and `|nθ|` are checked by PARI `isprime` and then evaluated by
`evalList` with the classes of `β`, `−β` and `q₀`.

| input | `m` | `β` | `ω(θ)` | primes of `|n|` / `|nθ|` (max digits) | `|n|`, `|nθ|` mod 8 | Lean #sols `|n|` / `|nθ|` | Lean `β`, `−β` ∈ π₁ | Lean `q₀` ∈ π₁ | exact descent (sel2cong; sel2_indep) |
|---|---|---|---|---|---|---|---|---|---|
| B1 = 20385278656470000/4053582059946008209 | 1 | 367 | 1 | 3 / 4 (29) | 5, 5 | 8 / 8 | yes, yes | no | selmer3, selmer3; dim 3, β ∈ π₁, q₀ ∉ π₁ |
| B2 = 12386695205430000/52317496006603732969 | 1 | 223 | 2 | 4 / 6 (29) | 5, 5 | 8 / 8 | yes, yes | no | same |
| B3 = 2276874543344310000/9104841785587522355161 | 1 | 40991 = 179·229 | 1 | 5 / 6 (34) | 5, 5 | 8 / 8 | yes, yes | no | same |
| B4 = 4105883959148790000/3424171711678166701561 | 1 | 73919 = 193·383 | 2 | 6 / 8 (34) | 5, 5 | 8 / 8 | yes, yes | no | same |
| B5 = 10609232216310000/22192219624171963129 | −1 | −191 | 1 | 3 / 4 (29) | 5, 5 | 8 / 8 | yes, yes | no | same |
| B6 = 241235055054630000/150783664286323600009 | −1 | −4343 = −43·101 | 2 | 6 / 8 (31) | 5, 5 | 8 / 8 | yes, yes | no | same |

All 12 slot curves therefore have:
- 8 solutions in Lean;
- the Lean class of `β` in π₁, matching the exact descent (`selmer3`, `dim 3`, `β ∈ π₁`).

These are exactly the instances of `SelmerCertified |n| β` and `SelmerCertified |nθ| β` that
`descent_lemma` feeds to CR₃. The class of `q₀` lies outside π₁ (Lean and descent agree), so the Lean
decision is not trivially true. The slot primes are ~30 digits here, not the ~70 digits of
`out_B123.txt`: the search picks `B` with small `β, θ` so that the configurations stay at most 8 primes.

## 7. Table of the task's deliverables

| item | file / Lean name | status |
|---|---|---|
| conventions (step 1) | §1 above | done: no discrepancy |
| Lean evaluation (step 2) | `scratch/cr3-check/Eval.lean`: `legBitC`, `legBit_eq_legBitC`, `cast_prime_ne_zero`, `natConfigC`, `natConfig_sols_eq`, `cardOf`(`_spec`), `divs7`, `report`(`_spec`), `solPairs`, `primeEquiv`(`_val`), `natConfig_prod_card`, `natConfig_prod_first`, `Valid`, `tblCfg`, `evalList`(`_spec`) | proved, no `sorry`; 40 + 12 evaluations |
| independent descent (step 3) | `sel2_indep.py`, `compare.py` | done: 0 mismatches in 40 |
| points (step 4) | `points.py`, `points2.py`, `quartic.py`, `anrank.py` | points found on 9 of the 24 CR₃-hypothesis curves (18 pairs); none found on 15 within the limits (large generators, §5); no contradiction |
| slot construction (step 5) | `slot5.py`, `Eval.lean` (`evalList`) | done: 12 of 12 configurations agree |

These lemmas are additions beyond the brief. They are in scratch only and are not imported by
`ZInQKernel`: all the declarations listed in the table above, in namespace `ZInQ.RouteK.CR3Check`.

## 8. Problems

- **Points with large height.** Some CR₃-hypothesis curves have generators beyond PARI's search
  within the limits used (§5). The BSD-predicted heights of the hardest ones are 350–520, so their
  coordinates have hundreds of digits. This is a search limitation, not a counterexample:
  - the Lean data agree with the exact Selmer group on these curves too;
  - the analytic rank is 1 where it could be computed.
- **`Eval.lean` warns** about the deprecated `if_pos`/`if_neg` in Lean 4.35. These are warnings only.
- **`#eval` is not kernel evaluation.** The numbers come from compiled code. The bridging theorems
  (`*_spec`) are kernel-checked. A kernel `decide` on `natConfig` itself is impossible: its bits are
  classical.

## 9. Suggestions for the next agent

- **Reuse `Eval.lean`.** It is the right tool to test any future change to `RouteK/System` or `natConfig`.
  - Run it with `lake env lean scratch/cr3-check/Eval.lean` after building `ZInQKernel.RouteK.Assembly.Realize`.
  - Use `report d` for factorable `d` and `evalList primes as` for large primes.
  - Keep configurations to at most 8 primes: there are `2^{4+2k}` unknowns, and 8 primes take about
    a minute.
- **Bridge to the main argument.** If CR₃ is ever narrowed to the slot configurations, `evalList_spec`
  shows how to connect a list of primes to `natConfig l.prod`.
- **Docstring wording.** CR₃'s docstring and slot-k §4.1 could say explicitly that "first coordinate"
  means the class of `x` under `P ↦ (x, x − d)`. It is implicit in Proposition 0's Kummer map. §5
  confirms it numerically: the Lean class `a` is the class of `x`, not of `x − d`.
