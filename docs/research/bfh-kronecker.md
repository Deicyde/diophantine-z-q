# bfh-kronecker: Bump–Friedberg–Hoffstein clause (ii) stated over the Kronecker symbol

Status: research note (task bfh-kronecker, 2026-11-16). Branch `wip/bfh-kronecker` (base `wip/bfh-leaf` 516c2abe).
Lean (new files only):

* `ZInQKernel/Contrib/OneProof/BFHPrinted/Kronecker.lean` (Mathlib plus fh-printed's Mathlib-only
  `FHPrinted/LocalNorm.lean`): the Kronecker symbol `(D / n)` and the bridge to `FHPrinted.idelicChar`;
* `ZInQKernel/Contrib/OneProof/BFHKronecker.lean`: the contributor file (the leaf `BFHClauseIIKronecker`, the
  bridge to the consumers' characters, the equivalence with bfh-leaf's leaf, the use at `B = 4`, the assembly).

Scratch: `scratch/bfh-kronecker/` (`FoldCheck.lean` + `FoldCheck-output.txt`; `Discharges.lean` +
`Discharges-output.txt`; `autofold.json`; `Statement-copy.lean.txt`: verbatim copies of every statement involved;
`kronecker_check.py` + output; `*.lean.txt`: copies of the two new files; `log.md`).

Marks. **VERIFIED**: compiled, computed, or read in a file named here. **STANDARD**: published, with reference.
**SPECULATIVE**: an assessment. **UNVERIFIED**: a theorem or definition number given from memory (no network, no
copy of Bump–Friedberg–Hoffstein on this host).

---

## 0. Main result

**The leaf is now stated with BFH's own character, and the hFH discharge is rebuilt on it, using the leaf once
at `B = 4`.** The restated leaf `ZInQ.BFHPrinted.BFHClauseIIKronecker` is bfh-leaf's `BFHClauseII` with two
changes. `χ_D(n)` is the Kronecker symbol `(D / n)`, newly defined over Mathlib's `jacobiSym` and `ZMod.χ₈`, where
bfh-leaf used fh-printed's `idelicChar`. And `S` contains the primes dividing `N`, as printed, where bfh-leaf had
`2N`. All glue is proved, with standard axioms (VERIFIED). So the top hypothesis `hFH` of
`ZInQ.OneProof.frozenTarget` can be replaced by `hBFH : BFHClauseIIKronecker`, a leaf in printed form: **−1 GLUE**
in both columns (flag: unread, §3).

```lean
-- BFHPrinted/Kronecker.lean
noncomputable def kroneckerPrime (D : ℤ) (p : ℕ) : ℤ :=
  if p = 2 then ZMod.χ₈ (D : ZMod 8) else jacobiSym D p
noncomputable def kroneckerSym (D : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then (if D.natAbs = 1 then 1 else 0)
  else n.factorization.prod fun p k => kroneckerPrime D p ^ k

-- BFHKronecker.lean
noncomputable def kroneckerTwistCoeff {N : ℕ} [NeZero N] (f : Newform N 2) (D : ℤ) (n : ℕ) : ℂ :=
  coeff f n * (kroneckerSym D n : ℂ)
def KroneckerCentralValueNeZero {N : ℕ} [NeZero N] (f : Newform N 2) (D : ℤ) : Prop :=
  ∀ G : ℂ → ℂ, IsEntireCont (kroneckerTwistCoeff f D) 2 G → G 1 ≠ 0
def BFHClauseIIKronecker : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
  ∀ ε : ℤ, IsFESign f ε →
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → p ∣ N → p ∈ S) →
    ∃ D : ℤ, Int.IsFundamentalDiscr D ∧ D ≠ 1 ∧ 0 < ε * D ∧ SplitsInQuadratic D S ∧
      KroneckerCentralValueNeZero f D

theorem bfhClauseIIKronecker_iff : BFHClauseIIKronecker ↔ BFHClauseII
theorem exists_heegnerDisc_of_bfhClauseIIKronecker (h : BFHClauseIIKronecker) {N : ℕ} [NeZero N]
    (f : Newform N 2) (hχ : f.χ = 1) (hw : rootNumber f hχ = -1) :
    ∃ D : ℤ, D < -4 ∧ IsOddImagFundDisc D ∧ HeegnerHyp N D ∧
      ∀ G : ℂ → ℂ, IsEntireCont (twistCoeff f D) 2 G → G 1 ≠ 0
theorem grossZagierCd_of_bfhClauseIIKronecker (hL1 : HeckeThetaNewform) (hBFH : BFHClauseIIKronecker)
    (hL3 : GrossZagierHeegner) : GrossZagierCd
theorem frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhKronecker (hH : SixContactMin)
    (hA : ZInQ.Literature.TYZThm35ReadingA) (hL1 : HeckeThetaNewform)
    (hBFH : BFHClauseIIKronecker) (hL3 : GrossZagierHeegner) : FrozenTarget
theorem fhNonvanishing_of_bfhClauseIIKronecker (h : BFHClauseIIKronecker) : FHNonvanishing
-- scratch/bfh-kronecker/FoldCheck.lean
theorem ZInQ.Contrib.TYZChain.frozenTarget_bfhKronecker (r …) (t …) (l …) (g …) (h11 …) (h29 …) (hCM …) (h33 …)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIKronecker) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) : ZInQ.FrozenTarget
```

Every declaration compiles with no warnings. Lake's only note is that `Kronecker.lean` imports Mathlib modules
without the `module` keyword, as fh-printed's `LocalNorm.lean` does. All have axioms
`[propext, Classical.choice, Quot.sound]` (VERIFIED: `Discharges-output.txt`, 14 theorems; `FoldCheck-output.txt`).

---

## 1. The Kronecker symbol and the bridge (all proved; VERIFIED)

**Definition.** For `n ≥ 1`, `(D / n) = ∏_{p^k ∥ n} (D / p)^k`, with `(D / 2) = χ₈(D)` and `(D / p)` the Legendre
symbol for odd `p` (Mathlib's `jacobiSym D p`). Here `χ₈(D)` is `0` for even `D`, `1` for `D ≡ ±1`, and `−1` for
`D ≡ ±3 (mod 8)`. The value at `n = 0` is `(D / 0) = 1` if `|D| = 1` and `0` otherwise. This is the textbook
definition (H. Cohen, *A Course in Computational Algebraic Number Theory*, Def. 1.4.8, UNVERIFIED number). The
value at `n = 0` never enters, since the L-series ignores `n = 0`. Mathlib v4.35 has no Kronecker symbol (VERIFIED,
grep of `Mathlib/NumberTheory`). It has `jacobiSym` (odd modulus) and `ZMod.χ₄`, `ZMod.χ₈`, `ZMod.χ₈'`, which fit
the odd part and the factor at `2`.

**Sanity check** (VERIFIED, computed; `kronecker_check.py`). PARI and sympy are not installed on this host. The
check compares a transcription of the Lean definition with an independent binary Kronecker algorithm (Cohen
Alg. 1.4.10, UNVERIFIED number), and with `J(n | |D|)` for `D ≡ 1 (mod 4)`. On 30 random pairs (`D` a fundamental
discriminant in `[−200, 200]`, `0 ≤ n ≤ 400`) there were 0 mismatches.

**Theorems** (`BFHPrinted/Kronecker.lean`). These are the Kronecker-symbol forms of the Compat lemmas
`GZStatements.chiD_mul`, `chiD_prime` and `chiD_two`:

| theorem | statement |
| --- | --- |
| `kroneckerSym_mul` | `(D / mn) = (D / m)(D / n)` for `m, n ≠ 0` (completely multiplicative; cf. `chiD_mul`) |
| `kroneckerSym_prime` | `(D / p) = legendreSym p D` for odd primes `p`, any `D` (cf. `chiD_prime`) |
| `kroneckerSym_two`, `kroneckerSym_two_of_one_mod_four` | `(D / 2) = χ₈(D)`; for `D ≡ 1 (4)`: `1` if `D ≡ 1 (8)`, else `−1` (cf. `chiD_two`) |
| `charAtPrime_odd` | `charAtPrime d p = legendreSym p d` for odd `p` with `p² ∤ d` (ramified and unramified cases) |
| `charAtPrime_two_of_one_mod_four` | `charAtPrime d 2 = χ₈(d)` for `d ≡ 1 (mod 4)` |
| `charAtPrime_four_mul` | `charAtPrime (4m) p = charAtPrime m p` (norms from `ℚ_p(√4m)` and `ℚ_p(√m)` agree) |
| `charAtPrime_eq_kroneckerPrime` | for **every** fundamental discriminant `d` and prime `p` |
| `idelicChar_eq_kroneckerSym` | `idelicChar d n = (d / n)`, every fundamental `d` (odd or even), `n ≠ 0` |
| `kroneckerSym_eq_jacobiSym` | `(d / n) = J(n | |d|)` for `d ≡ 1 (4)` squarefree, `n ≠ 0` (gz-decomp's `chiD`) |

The bridge to the consumers is in `BFHKronecker.lean`:

* `chiD_eq_kroneckerSym`: `chiD D n = (D / n)` for `D ≡ 1 (mod 4)` squarefree and `n ≠ 0`.
* `kroneckerTwistCoeff_eq_printedTwistCoeff`: for every fundamental `D`.
* `kroneckerTwistCoeff_eq_twistCoeff`: for odd `D`.
* `kroneckerCentralValueNeZero_iff`: `KroneckerCentralValueNeZero f D ↔ CentralValueNeZero f D` for every
  fundamental `D`.

The even case of `idelicChar_eq_kroneckerSym` (`D = 4m`) is not used by the proof. It is proved so that the leaf's
`χ_D` is the same character as fh-printed's for every `D` the leaf can return. That gives the equivalence of the
two leaves below.

---

## 2. The leaf and its rating: printed form (flag: unread)

`BFHClauseIIKronecker`, clause by clause, against the print. The printed statement is as the theorem-application
audit read it (A025), and the bfh-leaf statement review confirmed it clause by clause: `ε D > 0`; every prime of
`S` splits in `ℚ(√D)`; `L(k/2, f, χ_D) ≠ 0` in the analytic normalization, which is `L(k, f, χ_D)` here; `D`
fundamental; `χ_D(n) = (D / n)`; no CM exclusion; no level condition.

| Print | Leaf | Rating |
| --- | --- | --- |
| `f` cuspidal newform, even weight `2k`, trivial character, `Γ₀(N)` | `f : Newform N 2`, `f.χ = 1` (Tau Ceti) | instance `k = 1`; see the newform-dictionary note below |
| `ε` the sign of the functional equation of `L(s, f)` | `IsFESign f ε` (bfh-leaf) | the definition written as the functional equation at level `N`; `isFESign_iff` proves `ε = rootNumber f` |
| `S` finite, primes, containing the primes dividing `N` | `S : Finset ℕ`, `∀ p ∈ S, p.Prime`, `p ∣ N → p ∈ S` | **literal** (bfh-leaf had `2N`) |
| `D` a fundamental discriminant of a quadratic field | `Int.IsFundamentalDiscr D ∧ D ≠ 1` | literal (Mathlib) |
| `ε D > 0` | `0 < ε * D` | literal |
| every `p ∈ S` split in `ℚ(√D)` | `SplitsInQuadratic D S` (bfh-leaf) | literal (two distinct primes of `𝓞 K` above `p`, `K ∋ √D` quadratic) |
| `L(k, f, χ_D) ≠ 0`, `χ_D(n) = (D / n)`, `L(s, f, χ_D) = ∑ aₙ χ_D(n) n^{−s}` | `KroneckerCentralValueNeZero f D` | **literal**: the print's series with the print's character (the Kronecker symbol, by its textbook definition), its entire continuation at the centre `s = 1 = k` |

**Rating: printed form**, a direct instance at `k = 1`. Every clause is the print's notion over a genuine
Mathlib, Tau Ceti or kernel definition. The only departures are the specialization `k = 1` and writing "the field
`ℚ(√D)`" as `∃ K`. The second only weakens the conclusion, since splitting does not depend on the choice of `K`.
The leaf is not stronger than the print. It is also equivalent in Lean to bfh-leaf's leaf
(`bfhClauseIIKronecker_iff`, VERIFIED), so it inherits the nonvacuity checks there (`splitsInQuadratic_witness`,
`isFESign_iff`, `exists_isEntireCont_printedTwistCoeff`). The remaining change from bfh-leaf's rating is that
`χ_D` is now the print's own character, not one that equals it through `idelicChar_eq_jacobiSym`. **Flag:
unread.** The print was read by the audit from page images, not by this task. The bfh-leaf review closed the
three checks of bfh-leaf §4 (CM, level, wording) as reported in the task statement.

**Newform dictionary (remaining step: definitional, not a Lean step).** newform-dict (branch `wip/newform-dict`,
`NewformDict.isNewform_iff`) proved that the kernel's coefficient-level `IsNewform f χ` is equivalent to Tau Ceti's
`Newform N k` with `g.χ = MulChar.toUnitHom χ`. Tau Ceti's new space is the Petersson complement of the old space,
which is the printed (Atkin–Lehner) notion. So `Newform N 2` is the printed newform, and no restatement over
`IsNewform` is needed. The one identification left is that a newform on `Γ₁(N)` with trivial nebentypus is the
classical newform on `Γ₀(N)`: `S₂(Γ₁(N), 1) = S₂(Γ₀(N))`, and the new subspaces correspond (Diamond–Shurman §5.2
and §5.6–5.8, UNVERIFIED numbers). gz-decomp §2 rated this "no defect", and this task leaves that unchanged. It is a
reading of the print's "on `Γ₀(N)`" in Tau Ceti's framework, not a theorem the proof applies. Stating the leaf over
`IsNewform f 1` instead would add only `isNewform_iff` at `χ = 1` (`MulChar.toUnitHom 1 = 1`). That file is not on
this base, so it was not done.

---

## 3. The use and the fold (all proved; VERIFIED)

**One application, at `B = 4`.** The only consumer of `FHNonvanishing`, `GZDecomp.grossZagierCd_of_leaves`,
applies it at `B = 4`, as gz-statements recorded (`Weak.lean`). `exists_heegnerDisc_of_bfhClauseIIKronecker` applies
the leaf once, with `S` exactly the primes dividing `2N` and `ε = rootNumber f = −1`:

1. `ε D > 0` gives `D < 0`.
2. `2` splits, so `D ≡ 1 (mod 8)` (`mod_eight_of_splitsIn_two`). Hence `D` is squarefree and `≡ 1 (mod 4)`, and
   `D ≤ −7 < −4` (omega). No prime outside `2N` has to split, unlike bfh-leaf's every-`B` glue.
3. Each odd `p ∣ N` splits, so `D` is a nonzero square mod `p` (`zmod_isSquare_of_splitsIn`). This gives
   `HeegnerHyp N D` (`heegnerHyp_iff_split`).
4. The central value transfers by `kroneckerTwistCoeff_eq_twistCoeff`.

`grossZagierCd_of_bfhClauseIIKronecker` is `grossZagierCd_of_leaves` with `signOfSimpleZero`, copied with
`hL2 N f hχ hw 4` replaced by step 1–4. `frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhKronecker` is
`frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` with `hL2 : FHNonvanishing` replaced by `hBFH`.

**Fold** (hand fold: `hFH` is a top-level binder, not a bundle field, so `autofold.py` does not parse it; spec in
`scratch/bfh-kronecker/autofold.json`).

* `Main.lean`: add `import ZInQKernel.Contrib.OneProof.BFHKronecker`. Replace the binder
  `(hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE)` by `(hBFH : ZInQ.BFHPrinted.BFHClauseIIKronecker)`. Replace the call
  `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves A B H (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH) hL3`
  by `ZInQ.BFHPrinted.frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhKronecker A B H hBFH hL3`, with `A`, `B`
  and `H` verbatim. This was checked without editing Main: `frozenTarget_bfhKronecker` in `FoldCheck.lean`,
  standard axioms (VERIFIED).
* Alternative drop-in, covering every `B`: replace only the argument by
  `ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIKronecker hBFH` (`frozenTarget_bfhKronecker_allB`, VERIFIED).
* kinds.tsv: replace the row `(frozenTarget, hFH; consequence; GLUE GLUE)` by `(frozenTarget, hBFH)`, with kind
  `published`, strict `LEAF`, strictest `LEAF` and flag_class `unread`. That is **−1 GLUE** in both columns. If
  bfh-leaf's fold is made first, swapping its leaf for this one leaves the counts unchanged, by
  `bfhClauseIIKronecker_iff`.
* locators.md (proposed row, not edited): "Bump–Friedberg–Hoffstein 1990, clause (ii) (BFHClauseIIKronecker) |
  Invent. Math. 102 (1990) 543–618, opening theorem pp. 543–544, clause (ii), `χ_D(n) = (D/n)` | read from page
  images by the theorem-application audit (A025); clause-by-clause review (bfh-leaf)".

**`#discharges`** (VERIFIED, `Discharges-output.txt`): `62 open hypotheses, 2301 theorems checked, 8 discharge
one`. None of the discharges comes from this task's file. That is expected: no theorem has `hFH`'s type
`FriedbergHoffsteinB_FE`. The `hFH` line in the output is fh-printed's `friedbergHoffsteinB_FE_of_printed`, imported
transitively.

Build: `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.BFHKronecker`
succeeded (13004 jobs, on a build tree copied from fh-printed; VERIFIED).

---

## 4. What remains

* The hand fold (Main.lean, kinds.tsv, locators.md, OPEN.md regeneration). It was not done here, because the rules
  forbid edits under `ZInQKernel/` other than the new files.
* Clearing the *unread* flag by a reading of BFH pp. 543–544. This task had no copy of the paper.
* Optionally, stating the leaf over the kernel's `IsNewform f 1` through newform-dict's `isNewform_iff` (§2), once
  that branch is merged.
