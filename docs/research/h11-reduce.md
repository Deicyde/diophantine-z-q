# h11-reduce: TYZ Theorem 1.1 (integrality) from Lemma 2.9 and Tunnell's formula

Task h11-reduce, 2026-11-16. Branch `wip/h11-reduce` (base origin/main `0caafe66`, w80). Lean:
`ZInQKernel/Contrib/OneProof/TYZThm11Integral.lean` (new file; namespace `ZInQ.Contrib.TYZDecomp.H11Reduce`).
Scratch: `scratch/h11-reduce/` (results log `log.md`, numerics `tunnell_check.py`, manual fold `MainEdit.lean`,
discharge check `DischargesH11.lean` with its output, autofold-format spec `autofold.json`, proposed kinds rows
`kinds-rows.tsv`).

Marks: **VERIFIED** = read in a source named here, computed, or compiled; **STANDARD** = published with an exact
reference; **SPECULATIVE** = an assessment; **UNVERIFIED** = a locator or theorem number not read here. TYZ is
Tian–Yuan–Zhang, arXiv:1411.4728v1 (Asian J. Math. 21 (2017)). Its source `Period7.tex` is **not on this host**
(`~/tyz-src` does not exist; searched the home directories), so every TYZ line number here is quoted from earlier
notes (`h29-fix.md`, `h29-ne3.md`, `rv-pn-encoding.md`, `tyz-decomp.md`).

## 0. Main result

**`h11` is removed.** The top hypothesis `h11 = ZInQ.Contrib.TYZDecomp.TYZThm11Integral` is proved from two
published leaves plus three leaves that are already open (VERIFIED: compiled, standard axioms only):

```lean
theorem tyzThm11Integral_of_leaves (hL : LegendreThreeSquares) (hJ : JonesPallX2Y2Z16)
    (hfx : TYZTestVectorExists) (hL29 : TYZLemma29PrintedNe3R) (hT : TunnellOddL1) :
    TYZThm11Integral
```

The same leaves also give `h29` without TYZ Theorem 2.1 at `(3, 1)`:

```lean
theorem tyzLemma29Mod2_of_tunnellR (hL : LegendreThreeSquares) (hJ : JonesPallX2Y2Z16)
    (hfx : TYZTestVectorExists) (hL29 : TYZLemma29PrintedNe3R) (h23 : TYZProp23Printed)
    (hT : TunnellOddL1) : TYZLemma29Mod2
```

The new leaf `TYZLemma29PrintedNe3R` implies the open leaf `hL29` (`tyzLemma29PrintedNe3_of_R`). So in
`frozenTarget`:

| removed | added |
| --- | --- |
| `h11 : TYZThm11Integral` (TYZ Thm 1.1, LEAF) | `hL29R : TYZLemma29PrintedNe3R` (TYZ Lemma 2.9, real `𝓛`; LEAF, printed) |
| `hL29 : TYZLemma29PrintedNe3` (TYZ Lemma 2.9, integer `𝓛`; LEAF) | `hTun : TunnellOddL1` (Tunnell 1983; LEAF, printed) |
| `hT21 : TYZThm21At31` (TYZ Thm 2.1 at (3,1); LEAF) | |

**Net −1 hypothesis, −1 LEAF, no GLUE added** (strict and strictest: every row is LEAF in both columns). Reading A
then rests on eight statements instead of nine. The new theorem is `h11reduce_frozenTarget`
(`scratch/h11-reduce/MainEdit.lean`). The hypothesis `hL29` is replaced by its real form `hL29R`, which is the print,
not by something stronger (§2). These are frozenTarget arguments, so the fold is by hand, as for h29-ne3 (§4).

## 1. Why the open leaves alone cannot give `h11` (finding)

VERIFIED (read in `Leaves.lean`, `TYZLemma29Mod2.lean`): the open TYZ leaves `TYZLemma29PrintedNe3` and
`TYZThm21At31` quantify over **integer** sign choices `ℓ : ℕ → ℤ` with `ℓ(m)² = lcalSq m` for **every**
squarefree `m ≡ 1, 3 (mod 8)` (`IsLcalSign`). If `h11` failed at a single `m`, no such `ℓ` would exist and both
leaves would hold vacuously. So no derivation of `h11` from them is possible: their content presupposes Theorem 1.1.
They are not false, and as consequences of the print given Theorem 1.1 they are fine. But for `h11` the statement
needed is Lemma 2.9 for TYZ's real `𝓛`. That is the leaf `TYZLemma29PrintedNe3R` below.

TYZ's own argument for integrality (Theorem 1.1, L1081–1088 per `rv-pn-encoding.md`) is an induction on divisors
through Lemma 2.9. It has two gaps (both recorded earlier, rv-pn-encoding finding i2, h29-fix):
* at `n = 3`, the printed Lemma 2.9 is false (`Q(3) = ±3`, `𝓛(3) = ±1`; Theorem 2.1's factor `w_K = 3`), and the
  correct form only gives `3𝓛(3) ∈ ℤ`;
* the base case uses `𝓛(1) = 1` (L1082), which is asserted, not proved.
Both values come here from Tunnell's formula.

## 2. The new leaves (each rated)

### `TunnellOddL1`: printed (published, refereed); theorem number UNVERIFIED

```lean
def tunnellA (n : ℕ) : ℕ :=
  Nat.card {v : ℤ × ℤ × ℤ // 2 * v.1 ^ 2 + v.2.1 ^ 2 + 8 * v.2.2 ^ 2 = (n : ℤ)}
def tunnellB (n : ℕ) : ℕ :=
  Nat.card {v : ℤ × ℤ × ℤ // 2 * v.1 ^ 2 + v.2.1 ^ 2 + 32 * v.2.2 ^ 2 = (n : ℤ)}
def TunnellOddL1 : Prop :=
  ∀ n : ℕ, Odd n → Squarefree n →
    lValOne n = (omegaInt : ℂ) * ((tunnellA n : ℂ) - 2 * (tunnellB n : ℂ)) ^ 2 /
      (16 * (Real.sqrt n : ℂ))
```

* Source: J. B. Tunnell, *A classical Diophantine problem and modular forms of weight 3/2*, Invent. Math. 72
  (1983), 323–334: the formula for `L(E_n, 1)`, `E_n : y² = x³ − n²x`, `n` odd squarefree (STANDARD as a result;
  theorem number UNVERIFIED, no network). It is also in Koblitz, *Introduction to elliptic curves and modular forms*,
  GTM 97, Ch. IV (locator UNVERIFIED). Equivalent printed presentations are `β(B − A/2)²/(4√n)`, and `β a(n)²/(4√n)`
  with `a(n)` the coefficients of `η(8z)η(16z)θ(2z)`. Which of these is the printed display is UNVERIFIED, so the
  row is flagged unread.
* Over genuine definitions: `lValOne n` is the value at `1` of the (unique) continuation of Mathlib's `L(C_n, s)`
  (`Leaves.lean`; it exists, `ZInQ.Contrib.heckeContinuation`), `omegaInt = ∫₁^∞ dx/√(x³ − x)` (Tunnell's `β`,
  proved positive and integrable in `Leaves.lean`), and `A`, `B` are `Nat.card` of sets of integer triples.
* Not stronger than the print: it is the printed formula for every odd squarefree `n`. VERIFIED numerically on 30
  odd squarefree `n ≤ 187` of every class mod 8 (`tunnell_check.py`: PARI `lfun` at 38 digits, largest
  `|L − RHS| = 2·10⁻¹⁹`; on the classes `5, 7` both sides vanish). The same run confirms that the formula is TYZ's
  normalization: `lcalSq n = ((A − 2B)/2^{k+1})²` on the sample (`1, 1, 4, 1, …`, `16` at `n = 113`).
* Use: only `n = 1` (`A = B = 2`) and `n = 3` (`A = B = 4`), counted in Lean (`tunnellA_one`, …), giving
  `lcalSq 1 = lcalSq 3 = 1` (`lcalSq_one_of_tunnell`, `lcalSq_three_of_tunnell`). The leaf therefore also replaces
  TYZ's asserted `𝓛(1) = 1` (L1082). An integrator who prefers a narrower leaf could restrict it to `n ∈ {1, 3}`, a
  consequence of the print, and the glue would be unchanged.

### `TYZLemma29PrintedNe3R`: printed (TYZ Lemma 2.9, L1062–1066)

The open leaf `H29Split.TYZLemma29PrintedNe3` verbatim (same `τ`, `f_n`, `Q(n)`, `pairIdx`, same restrictions
`1 < n ≡ 1, 3 (mod 8)`, `n ≠ 3`), except that it quantifies over `ℓ : ℕ → ℝ` with `(ℓ m : ℂ)² = lcalSq m`
(`IsLcalSignR`) instead of `ℓ : ℕ → ℤ`. TYZ's `𝓛(m)` is a real number, a square root of
`L(E_m, 1)/(2^{2k−2−a}Ω_m)` (L338–353). A real `ℓ` with `ℓ(m)² = 𝓛(m)²` is `±𝓛(m)`, and the sign is absorbed by
`ε` (as in the integer form). So the real form is the printed statement. If some `lcalSq m` were not a nonnegative
real (it always is), no real `ℓ` would exist and the leaf would be vacuous, so it is never stronger than the print.
It implies the integer form (`tyzLemma29PrintedNe3_of_R`). Flag: as `hL29` (restricted, unread).

## 3. Glue (all proved in Lean)

| Lean | content |
| --- | --- |
| `tyzLemma29PrintedNe3_of_R` | the real form gives the open integer form (cast) |
| `card_eq_of_iff`, `tunnellA_one`, `tunnellB_one`, `tunnellA_three`, `tunnellB_three` | `A(1) = B(1) = 2`, `A(3) = B(3) = 4` (bounding + `interval_cases`) |
| `lcalSq_eq_of_tunnell` | for odd squarefree `m`: `lcalSq m = ((A − 2B)/2^{k+1})²` (TYZ's normalization `2^{2k−3}Ω_m`, `Ω_m = 2β/√m`) |
| `ellR`, `isLcalSignR_ellR` | Tunnell's sign choice `ℓ(m) = (A − 2B)/2^{k+1}` is a real sign choice of `𝓛` |
| `ellR_one`, `ellR_three`, `lcalSq_one_of_tunnell`, `lcalSq_three_of_tunnell` | `ℓ(1) = ℓ(3) = −1`, `𝓛(1)² = 𝓛(3)² = 1` |
| `exists_int_sum`, `one_mem_pairIdx` | helpers |
| `ellR_int` | TYZ's induction (L1081–1088): for `m ≠ 1, 3`, Lemma 2.9 at `m` with `τ` (Legendre, Jones–Pall) and `f_m` (`hfx`) reads `±ℓ(m)ℓ(1) + Σ_{d ≠ 1} ±ℓ(m/d)ℓ(d) = Q(m) ∈ ℤ`. The other pairs have `d, m/d < m` in the classes `1, 3`, so they are integers by strong induction |
| `tyzThm11Integral_of_leaves` | `h11` |
| `int_sq_one`, `qTun`, `tyzLemma29Mod2_of_tunnell(R)` | `h29` through the existing mod-2 glue `tyzLemma29Mod2_of_printed` with the genus period corrected at `n = 3` to `Q(3) := 3`. There `w_K · ε · 𝓛(3)𝓛(1) = 3` with `ε := 𝓛(3)𝓛(1) = ±1` (Tunnell), and `3 ≡ g(3) = 1` (`gNat_three`). For `n ≠ 3` the proof is the existing one (h29-fix/h29-ne3). `TYZThm21At31` is not used |

## 4. Compile outcomes and the fold

* `lake env lean ZInQKernel/Contrib/OneProof/TYZThm11Integral.lean`: no errors, no warnings, no `sorry`
  (VERIFIED). `#print axioms` of `tyzThm11Integral_of_leaves`, `tyzLemma29Mod2_of_tunnellR`,
  `tyzLemma29PrintedNe3_of_R`: `[propext, Classical.choice, Quot.sound]` (`scratch/h11-reduce/Axioms-output.txt`).
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.TYZThm11Integral`:
  success (13,699 jobs, 12 min, partial rebuild over a copied build tree). `MainEdit.lean` compiles;
  `#print axioms h11reduce_frozenTarget`: `[propext, Classical.choice, Quot.sound]` (VERIFIED,
  `MainEdit-output.txt`).
* Fold (by hand; `h11`, `hL29`, `hT21` are frozenTarget arguments, which `autofold.py` does not fold):
  1. add `import ZInQKernel.Contrib.OneProof.TYZThm11Integral` to `Main.lean`;
  2. in `frozenTarget`, replace the binders `(h11 : TYZThm11Integral)`, `(hL29 : H29Split.TYZLemma29PrintedNe3)`,
     `(hT21 : H29Split.TYZThm21At31)` by `(hL29R : H11Reduce.TYZLemma29PrintedNe3R)` and
     `(hTun : H11Reduce.TunnellOddL1)`, and the body's `h11` and
     `H29Split.tyzLemma29Mod2_of_sixLeaves hL3s hJP hfx hL29 hT21 hP23` by
     `H11Reduce.tyzThm11Integral_of_leaves hL3s hJP hfx hL29R hTun` and
     `H11Reduce.tyzLemma29Mod2_of_tunnellR hL3s hJP hfx hL29R hP23 hTun` (exactly `h11reduce_frozenTarget`);
  3. kinds.tsv: delete the frozenTarget rows `h11`, `hL29`, `hT21`, add `scratch/h11-reduce/kinds-rows.tsv`; a row in
     `locators.md` for Tunnell 1983.
  `scratch/h11-reduce/autofold.json` records the same in the autofold spec format (field, proof, leaves with kind and
  flag), with a `manual_fold` note.

## 5. Discharge check

`scratch/h11-reduce/DischargesH11.lean` (imports `Main`, `Discharges` and the new file), output
`DischargesH11-output.txt` (VERIFIED), the two lines for this file:

```
DISCHARGES [hL29] by ZInQ.Contrib.TYZDecomp.H11Reduce.tyzLemma29PrintedNe3_of_R
  still assumes: [ZInQ.Contrib.TYZDecomp.H11Reduce.TYZLemma29PrintedNe3R]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [h11] by ZInQ.Contrib.TYZDecomp.H11Reduce.tyzThm11Integral_of_leaves
  still assumes: [ZInQ.Contrib.TYZDecomp.H29Split.LegendreThreeSquares,
 ZInQ.Contrib.TYZDecomp.H29Split.JonesPallX2Y2Z16,
 ZInQ.Contrib.TYZDecomp.H29Split.TYZTestVectorExists,
 ZInQ.Contrib.TYZDecomp.H11Reduce.TYZLemma29PrintedNe3R,
 ZInQ.Contrib.TYZDecomp.H11Reduce.TunnellOddL1]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 56 open hypotheses, 2915 theorems checked, 9 discharge one
```

(`hT21` is not discharged by a theorem of its type; it drops because the new `h29` glue,
`tyzLemma29Mod2_of_tunnellR`, does not read it, as `h11reduce_frozenTarget` shows. The other seven lines of the output are the
contributions already in the tree.)

## 6. What remains

* Human reading of Tunnell 1983: the theorem number and which equivalent display is printed (flagged unread).
* The status of TYZ Lemma 2.9 itself is unchanged (open leaf `hL29R`, as `hL29` was).
* `hT21` leaves the list but stays true and printed. Nothing else in the tree reads it
  (`TYZLemma29Mod2.lean`'s `tyzLemma29Mod2_of_sixLeaves` remains as an alternative route).
