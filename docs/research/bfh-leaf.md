# bfh-leaf: `hFH` replaced by Bump–Friedberg–Hoffstein 1990, clause (ii)

Status: research note (task bfh-leaf, 2026-11-15/16). Branch `wip/bfh-leaf` (base 862bd440, leaf-fold-hx, with
origin/wip/fh-printed 8d0b9b64 merged). Lean (new files only):

* `ZInQKernel/Contrib/OneProof/BFHNonvanishing.lean`: the contributor file (the leaf `BFHClauseII`, the glue
  `fhNonvanishing_of_bfhClauseII`, `isFESign_iff`, `splitsInQuadratic_witness`);
* `ZInQKernel/Contrib/OneProof/BFHPrinted/Split.lean` (Mathlib only): split primes in quadratic fields;
* `ZInQKernel/Contrib/OneProof/BFHPrinted/Witness.lean` (Mathlib only): `7` splits in `ℚ(√−3)`.

Scratch: `scratch/bfh-leaf/` (`FoldCheck.lean` + `FoldCheck-output.txt`: the fold of `frozenTarget`;
`Discharges.lean` + `Discharges-output.txt`; `autofold.json`; `Statement-copy.lean.txt`: verbatim copies of the
statements involved; `Split.lean`, `Witness.lean`, `BFHNonvanishing.lean.txt`: copies; `log.md`).

Marks. **VERIFIED**: compiled, or read in a file named here. **STANDARD**: published, with reference.
**SPECULATIVE**: an assessment. No copy of Bump–Friedberg–Hoffstein is on this host and there is no network; the
statement of clause (ii) is the theorem-application audit's reading of the page images (docs/theorem-application-audit,
A025), **not read by this task**.

---

## 0. Main result

**`ZInQ.GZDecomp.FHNonvanishing` is proved from one new leaf, clause (ii) of the opening theorem of
Bump–Friedberg–Hoffstein (Invent. Math. 102 (1990) 543–618), stated over genuine objects, with all glue proved.**
So the top hypothesis `hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE` of `ZInQ.OneProof.frozenTarget` (GLUE since the
11-15 statement review rated it a consequence) can be replaced by `hBFH : ZInQ.BFHPrinted.BFHClauseII`, a leaf in
printed form: **−1 GLUE** in both columns once the fold is made (flag: unread, three checks, §4).

```lean
theorem ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseII (h : ZInQ.BFHPrinted.BFHClauseII) :
    ZInQ.GZDecomp.FHNonvanishing
theorem ZInQ.BFHPrinted.isFESign_iff {N : ℕ} [NeZero N] (f : Newform N 2) (hχ : f.χ = 1) (ε : ℤ) :
    IsFESign f ε ↔ (ε : ℂ) = rootNumber f hχ
theorem ZInQ.BFHPrinted.splitsInQuadratic_witness :
    Int.IsFundamentalDiscr (-3) ∧ (-3 : ℤ) ≠ 1 ∧ SplitsInQuadratic (-3) {7}
theorem ZInQ.Contrib.TYZChain.frozenTarget_bfh   -- scratch/bfh-leaf/FoldCheck.lean
    (r …) (t …) (l …) (g …) (h11 …) (h29 …) (hCM …) (h33 …)
    (hBFH : ZInQ.BFHPrinted.BFHClauseII) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) : ZInQ.FrozenTarget
```

All compile with no warnings other than Lake's notes that the Mathlib-only helpers import Mathlib modules without
the `module` keyword (as fh-printed's `LocalNorm.lean`); each has axioms `[propext, Classical.choice, Quot.sound]` (VERIFIED,
`scratch/bfh-leaf/Discharges-output.txt`, `FoldCheck-output.txt`). `frozenTarget_bfh` is the body of
`ZInQ.OneProof.frozenTarget` (Main.lean at 862bd440) copied verbatim with `hFH` replaced by `hBFH` and
`ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH` replaced by
`ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseII hBFH` (the only use of `hFH`).

No twisted root number, no auxiliary discriminant `D₀`, no Dirichlet theorem and no local dictionary through
`ℚ_p` are needed: BFH (ii) prescribes the sign of `d` through the root number of `f` itself and the Heegner
conditions as splitting.

---

## 1. The leaf (verbatim from `BFHNonvanishing.lean`; docstrings shortened)

```lean
-- BFHPrinted/Split.lean
/-- `p` splits in `K`: there are two distinct prime ideals of `𝓞 K` above `p`. -/
def SplitsIn (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  ∃ P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
    ∃ Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K), P ≠ Q

-- BFHNonvanishing.lean
/-- `ε` is the sign of the functional equation of `L(s, f)`: `Λ_N(2 − s) = ε Λ_N(s)` on `0 < Re s < 2`,
`Λ_N(s) = N^{s/2} (2π)^{−s} Γ(s) G(s)`, `G` the entire continuation of `∑ aₙ(f) n^{−s}`. -/
def IsFESign {N : ℕ} [NeZero N] (f : Newform N 2) (ε : ℤ) : Prop :=
  ∃ G : ℂ → ℂ, IsEntireCont (coeff f) 2 G ∧ ∀ s : ℂ, 0 < s.re → s.re < 2 →
    ZInQ.Literature.completedL N G (2 - s) = (ε : ℂ) * ZInQ.Literature.completedL N G s

/-- Every prime of `S` splits in `ℚ(√d)`. -/
def SplitsInQuadratic (d : ℤ) (S : Finset ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K), Module.finrank ℚ K = 2 ∧
    (∃ δ : K, δ ^ 2 = (d : K)) ∧ ∀ p ∈ S, SplitsIn K p

/-- Bump–Friedberg–Hoffstein 1990, opening theorem, clause (ii), at weight 2 and trivial character. -/
def BFHClauseII : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
  ∀ ε : ℤ, IsFESign f ε →
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → p ∣ 2 * N → p ∈ S) →
    ∃ d : ℤ, Int.IsFundamentalDiscr d ∧ d ≠ 1 ∧ 0 < ε * d ∧ SplitsInQuadratic d S ∧
      CentralValueNeZero f d
```

Objects. `Newform`, `f.χ` (Tau Ceti); `coeff`, `IsEntireCont` (gz-decomp); `ZInQ.Literature.completedL` (kernel);
`CentralValueNeZero f d` (fh-printed: `∀ G, IsEntireCont (printedTwistCoeff f d) 2 G → G 1 ≠ 0`, with
`printedTwistCoeff f d n = coeff f n * idelicChar d n`, `idelicChar d` the Dirichlet coefficients of the quadratic
character of `ℚ(√d)` built from its local components: `χ_d(p) = 1, −1, 0` as `p` splits, is inert, ramifies);
`Int.IsFundamentalDiscr`, `NumberField`, `𝓞 K`, `Ideal.primesOver`, `Module.finrank` (Mathlib). New: `SplitsIn`,
`SplitsInQuadratic`, `IsFESign`, all `def … : Prop` over these.

**The printed statement** (theorem-application audit, evidence/theta-upstream.md §1, read from page images of
pp. 543–544; INVENTORY.md A025): for `f` a cuspidal newform of even weight `2k` and trivial character on `Γ₀(N)`,
`ε` the sign of the functional equation of `L(s, f)`, and `S` any finite set of primes containing the primes
dividing `N`, there is a fundamental discriminant `d` of a quadratic field with `ε d > 0`, every `p ∈ S` split in
`ℚ(√d)`, and `L(k, f, χ_d) ≠ 0`, where `L(s, f, χ_d) = ∑ aₙ χ_d(n) n^{−s}` with centre `s = k`. (Clause (i), not
used: `ε d < 0`, same splitting, and a simple zero at the centre.)

---

## 2. Rating of the leaf: printed form (a direct instance), flagged unread

Clause by clause (every Lean claim VERIFIED by compilation):

| Print | Leaf | Rating |
| --- | --- | --- |
| `f` cuspidal newform, even weight `2k`, trivial character, `Γ₀(N)` | `f : Newform N 2`, `f.χ = 1` | instance `k = 1`; Tau Ceti's newform with trivial nebentypus is the classical newform on `Γ₀(N)` (gz-decomp §2, "no defect") |
| `ε` the sign of the functional equation of `L(s, f)` | `IsFESign f ε`: `Λ_N(2 − s) = ε Λ_N(s)` for the completed `Λ_N(s) = N^{s/2}(2π)^{−s}Γ(s)L(s, f)` | the definition itself, written as the functional equation (no conductor theorem: the level `N` is the print's); `isFESign_iff` proves `ε` is unique and equals `rootNumber f hχ`, so the conventions `Λ(s) = εΛ(2−s)` and `Λ(2−s) = εΛ(s)` agree (`ε = ±1`) |
| `S` any finite set of primes containing the primes dividing `N` | `S : Finset ℕ` of primes containing the primes dividing `2N` | instance (narrower: `2 ∈ S` added) |
| `d` a fundamental discriminant of a quadratic field | `Int.IsFundamentalDiscr d ∧ d ≠ 1` | literal (Mathlib's notion; `d = 1` is the only fundamental discriminant not of a quadratic field) |
| `ε d > 0` | `0 < ε * d` | literal |
| every `p ∈ S` split in `ℚ(√d)` | `SplitsInQuadratic d S`: a quadratic number field `K ∋ √d` in which every `p ∈ S` has two distinct primes of `𝓞 K` above it | literal: `K ≅ ℚ(√d)` (`d` not a square) and "`p` splits" in a quadratic field is "two distinct primes above `p`" (equivalently `p𝓞_K = 𝔭𝔭'`, `𝔭 ≠ 𝔭'`); `∃ K` only weakens (splitting does not depend on the choice of `K`) |
| `L(k, f, χ_d) ≠ 0`, `L(s, f, χ_d) = ∑ aₙ χ_d(n) n^{−s}` | `CentralValueNeZero f d` (fh-printed) | literal for this classical paper: the series is the print's, the value is that of its entire continuation at `s = 1 = k`; `χ_d` is the quadratic character of `ℚ(√d)`, given by its local components (`idelicChar`); for odd `d` it is proved equal to `(·/|d|)` (`idelicChar_eq_jacobiSym`, fh-printed) |

**Rating: printed form**, by the definition in docs/one-proof/OPEN.md ("the printed form or a direct instance of
it"): each clause is the print's notion over a genuine Mathlib/kernel definition, and the only changes are the
specialization `k = 1`, `2 ∈ S`, and `∃ K` for "the field `ℚ(√d)`". It is not stronger than the print (each change
narrows the hypotheses or weakens the conclusion). Not vacuous: `splitsInQuadratic_witness` shows the splitting
clause is satisfiable (`7` splits in `ℚ(√−3)`, compiled), `isFESign_iff` shows `IsFESign f ε` holds for exactly one
`ε`, and the central-value clause is fh-printed's (whose continuation exists for odd `d`,
`exists_isEntireCont_printedTwistCoeff`). **Flag: unread** (the print was read by the theorem-application audit from
page images, not by this task), with the three checks of §4.

This is the only leaf the proof uses; everything else is Mathlib, Tau Ceti (`Newform.frickeCompletedL_sub_eq`) and
glue already proved in `ZInQKernel/Contrib/` (`completedL_newform_sub`, `exists_isEntireCont_twist`,
`printedTwistCoeff_eq`, `heegnerHyp_iff_split`, `mem_primeFactors_two_mul`).

---

## 3. The glue (all proved; VERIFIED)

`fhNonvanishing_of_bfhClauseII`: given `f` with `rootNumber f hχ = −1` and a bound `B`,

1. `ε = −1`: `isFESign_of_rootNumber` (Tau Ceti's functional equation, through gz-fh's `completedL_newform_sub`;
   the continuation of `L(s, f)` is the twist by `χ_1`, `exists_isEntireCont_twist`);
2. `S` = the primes dividing `2N` together with the primes `≤ B`; BFH (ii) gives `d`;
3. `2` splits ⇒ `d ≡ 1 (mod 8)` (`mod_eight_of_splitsIn_two`), so `d` is squarefree `≡ 1 (mod 4)`; `ε d > 0` ⇒ `d < 0`;
4. `p ∈ S` odd splits ⇒ `d` is a nonzero square mod `p` (`zmod_isSquare_of_splitsIn`); with step 3 this is
   `HeegnerHyp N d` (`heegnerHyp_iff_split`);
5. every prime `≤ B` splits, so does not divide `d` (step 3 for `2`, step 4 for odd primes); `d ≠ −1`
   (`d ≡ 1 mod 8`), so `|d|`'s least prime factor exceeds `B` and `d < −B`;
6. `G(1) ≠ 0` for the twist by `chiD d`: `printedTwistCoeff_eq` (fh-printed) identifies the two coefficient
   sequences for odd fundamental `d`.

The algebraic number theory (`BFHPrinted/Split.lean`, Mathlib only, no deprecated API):

* `ef_eq_one`: if `p` splits in a quadratic `K`, a prime `P` above `p` has `e = f = 1`. From Mathlib's fundamental
  identity `Ideal.sum_ramification_inertia_eq_finrank` (`∑ e f = finrank ℤ 𝓞K = [K : ℚ] = 2`), positivity of `e`
  (`ramificationIdx_pos_of_isDedekindDomain'`) and `f` (`inertiaDeg_pos`);
* `exists_int_sub_mem` (`f = 1`, via `inertiaDeg_eq_of_isMaximal` and `finrank_eq_one_iff_of_nonzero'`): every
  `x ∈ 𝓞 K` is `≡ n (mod P)` for some `n ∈ ℤ`;
* `natCast_not_mem_sq` (`e = 1`, via `ramificationIdx'_eq_ramificationIdx`): `p ∉ P²`;
* `zmod_isSquare_of_splitsIn`: `√d ∈ 𝓞 K` reduces to a square root of `d` mod `P`, so mod `p`; if `p ∣ d` with
  `p² ∤ d`, then `√d ∈ P` and `p = a·(√d)² + b·p² ∈ P²` (Bézout), contradicting `e = 1`;
* `mod_eight_of_splitsIn_two`: for `d ≡ 1 (4)`, `ω = (1 + √d)/2 ∈ 𝓞 K` has `ω² − ω = (d − 1)/4`, and `x² ≡ x mod P`
  (`f = 1`), so `2 ∣ (d − 1)/4`; for `d = 4m`, `m ≡ 2, 3 (4)`, `s = √d/2 ∈ 𝓞 K` gives `2 ∈ P²` (from `s² = m` resp.
  `(s − 1)² + 2(s − 1) = m − 1`), contradicting `e = 1`.

---

## 4. The three checks for the reading (unread leaf)

The leaf rests on the audit's reading of pp. 543–544. Three points must be checked against the print before the
flag is cleared:

1. **No CM exclusion.** The use applies clause (ii) to the CM newform of `C_d` (theta series of a Hecke character
   of `ℚ(i)`). The audit's own application (theta-upstream.md §7) is to a non-CM family, so it had no reason to
   record a CM exclusion. If the theorem excludes CM forms, the print does not cover the use (the leaf would be
   stronger than the print; replace by Friedberg–Hoffstein 1995 or Waldspurger).
2. **No condition on the level.** The use has `N = 32 d²`, even and not squarefree. gz-decomp §2.4 and
   cr3-trust §2.4 item 3 already asked whether BFH restricts the level; locators.md row "Auxiliary imaginary
   quadratic nonvanishing" says the application to `N = 32d²` was not checked from BFH. The audit says the
   trivial-character, even-weight condition and the arbitrary finite splitting set were read directly, and
   reports no level condition (SPECULATIVE that none exists).
3. **The wording of clause (ii).** (a) "fundamental discriminant" or "squarefree `d`": if squarefree, the leaf
   follows by a short glue (squarefree `d` with `2` split is `≡ 1 mod 4`, hence fundamental), so it would rate
   consequence, not printed form; (b) "every `p ∈ S` split in `ℚ(√d)`" or a congruence condition such as
   `d ≡ ν² (mod 4N)`: with a congruence the splitting at the primes `≤ B` used in step 5 is not available from the
   print as such (another dictionary, and possibly a different route to `|d| > B`: BFH may state infinitely many
   `d`).

If check 1 or 2 fails the leaf must be flagged *pending reading* (GLUE until cleared); if check 3 changes the
wording the leaf rates consequence. Locators (all UNVERIFIED by this task): Invent. Math. 102 (1990), 543–618,
opening theorem, pp. 543–544, clause (ii); doi 10.1007/BF01233440.

---

## 5. Fold

`hFH` is a top-level hypothesis of `frozenTarget`, not a bundle field, and no theorem of this task has its type
`FriedbergHoffsteinB_FE` (that statement prescribes arbitrary local data at an auxiliary `D₀`, which BFH (ii) does
not give). So `#discharges` does not list the new file, and the fold is by hand:

* `Main.lean`: add `import ZInQKernel.Contrib.OneProof.BFHNonvanishing`; replace the binder
  `(hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE)` by `(hBFH : ZInQ.BFHPrinted.BFHClauseII)`; pass
  `(ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseII hBFH)` where
  `(ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH)` was passed. Checked without editing Main:
  `frozenTarget_bfh`, scratch/bfh-leaf/FoldCheck.lean, standard axioms (VERIFIED).
* kinds.tsv: replace row `(frozenTarget, hFH; consequence; GLUE GLUE)` by `(frozenTarget, hBFH)` with kind
  `published`, strict `LEAF`, strictest `LEAF`, flag_class `unread`, flag and source as in
  `scratch/bfh-leaf/autofold.json`: **−1 GLUE** in both columns.
* locators.md (proposed row, not edited): "Bump–Friedberg–Hoffstein 1990, clause (ii) (BFHClauseII) | Invent. Math.
  102 (1990) 543–618, opening theorem pp. 543–544, clause (ii) | read from page images by the theorem-application
  audit (A025); checks: CM, level, wording (bfh-leaf §4)".
* The fh-printed leaf `FriedbergHoffsteinB_Printed` (Friedberg–Hoffstein 1995) becomes unnecessary for the proof if
  this fold is made; it remains the fallback if check 1 or 2 fails.

`#discharges` (scratch/bfh-leaf/Discharges.lean, output recorded, VERIFIED): 62 open hypotheses, 2260 theorems
checked, 8 discharge one; none from this task's file (expected, above). The `hFH` line in the output is fh-printed's
`friedbergHoffsteinB_FE_of_printed`, imported transitively.

---

## 6. What remains

* The three checks of §4 against the print (human or page-image reading).
* The hand fold (Main.lean, kinds.tsv, locators.md, OPEN.md regeneration): not done here (rules: no edits under
  ZInQKernel/ except the new files).
