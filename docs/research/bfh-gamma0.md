# bfh-gamma0: Bump–Friedberg–Hoffstein clause (ii) over the classical newform on `Γ₀(N)`

Status: research note (task bfh-gamma0, 2026-11-16). Branch `wip/bfh-gamma0`: base `wip/bfh-kronecker`
c282ffab, with origin/main 2880fef1e merged in.

New Lean files, all under `ZInQKernel/Contrib/OneProof/`:

* `BFHPrinted/Gamma0Newform.lean` imports only Tau Ceti. It defines the new subspace, the Hecke action and
  the classical newform on `Γ₀(N)`, and proves the dictionary with Tau Ceti's `Γ₁(N)`-newforms of trivial
  nebentypus in both directions.
* `BFHGamma0.lean` is the contributor file. It holds the leaf `BFHClauseIIGamma0`, the equivalence with
  bfh-kronecker's leaf, and the assembly.
* `BFHKronecker.lean` (bfh-kronecker's file, on this branch): only the docstring of `BFHClauseIIKronecker`
  changed. It now gives weight `k`, the central value `L(k/2)`, cites the statement-check read and points
  to `BFHClauseIIGamma0`. The statement itself is unchanged.

Scratch is in `scratch/bfh-gamma0/`:

* `FoldCheck.lean` with `FoldCheck-output.txt`;
* `Discharges.lean` with `Discharges-output.txt`;
* `autofold.json`;
* `Statement-copy.lean.txt`, verbatim copies of the 22 statements and definitions involved;
* `*.lean.txt`, copies of the three files;
* `Gamma0New.lean`, the first compiled draft;
* `log.md`.

Marks. **VERIFIED**: compiled, or read in a file named here. **STANDARD**: published, with reference.
**SPECULATIVE**: an assessment. **UNVERIFIED**: a theorem or section number given from memory. There is no
network and no copy of BFH on this host.

---

## 0. Main result

**The last gap in `BFHClauseIIKronecker` is closed.** The review had rated every clause as printed except
one identification: a Tau Ceti `Γ₁(N)`-newform with trivial character is a classical `Γ₀(N)` newform.
This task proves that identification in Lean, in both directions. It then states the leaf over the
classical `Γ₀(N)` newform, as BFH print it, and proves that leaf equivalent to bfh-kronecker's.

```lean
-- BFHPrinted/Gamma0Newform.lean
def IsGamma0New [NeZero N] (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) : Prop :=
  ∀ (M d : ℕ) (h : d * M ∣ N), M ≠ N → ∀ g : CuspForm ((Gamma0 M).map (mapGL ℝ)) k,
    haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h)
    CuspForm.peterssonInnerCosets
      (TauCeti.CuspForm.levelRaise d (Gamma0_map_le_conjAct_scaleGL_of_dvd h) g) F = 0
noncomputable def heckeGamma0 [NeZero N] :
    𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ →ₗ[ℤ] Module.End ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  Finsupp.linearCombination ℤ fun D ↦ heckeSlashGamma0CuspFormEnd k D
noncomputable def coeffGamma0 (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (n : ℕ) : ℂ :=
  (qExpansion 1 F).coeff n
structure IsGamma0Newform [NeZero N] (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) : Prop where
  isEigen : ∀ n : ℕ, 0 < n → n.Coprime N → ∃ c : ℂ, heckeGamma0 N k (heckeTCompositeGamma0 N n) F = c • F
  isNew : IsGamma0New F
  isNorm : coeffGamma0 F 1 = 1

theorem isGamma0New_toCuspFormGamma0 (f : Newform N k) (hχ : f.χ = 1) : IsGamma0New (f.toCuspFormGamma0 hχ)
theorem isGamma0Newform_toCuspFormGamma0 (f : Newform N k) (hχ : f.χ = 1) :
    IsGamma0Newform (f.toCuspFormGamma0 hχ)
theorem restrict_mem_cuspFormsNew_of_isGamma0New (hF : IsGamma0New F) :
    CuspForm.restrict (Gamma1_map_le_Gamma0_map N) F ∈ cuspFormsNew N k
noncomputable def IsGamma0Newform.toNewform (hF : IsGamma0Newform F) : Newform N k   -- χ = 1

-- BFHGamma0.lean
def BFHClauseIIGamma0 : Prop :=
  ∀ (N : ℕ) [NeZero N] (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2), IsGamma0Newform F →
  ∀ ε : ℤ, IsFESignGamma0 F ε →
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → p ∣ N → p ∈ S) →
    ∃ D : ℤ, Int.IsFundamentalDiscr D ∧ D ≠ 1 ∧ 0 < ε * D ∧ SplitsInQuadratic D S ∧
      KroneckerCentralValueNeZeroGamma0 F D
theorem bfhClauseIIGamma0_iff : BFHClauseIIGamma0 ↔ BFHClauseIIKronecker
theorem bfhClauseIIGamma0_iff_bfhClauseII : BFHClauseIIGamma0 ↔ BFHClauseII
theorem frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhGamma0 (hH : SixContactMin)
    (hA : ZInQ.Literature.TYZThm35ReadingA) (hL1 : HeckeThetaNewform)
    (hBFH : BFHClauseIIGamma0) (hL3 : GrossZagierHeegner) : FrozenTarget
theorem fhNonvanishing_of_bfhClauseIIGamma0 (h : BFHClauseIIGamma0) : FHNonvanishing
```

`IsFESignGamma0`, `kroneckerTwistCoeffGamma0` and `KroneckerCentralValueNeZeroGamma0` are bfh-leaf's
`IsFESign` and bfh-kronecker's `kroneckerTwistCoeff` and `KroneckerCentralValueNeZero`, with `coeff f`
replaced by `coeffGamma0 F`.

**Fold result: `hFH` is replaced by a printed leaf, −1 GLUE on main** (§4). The fold was checked against
the body of main's `ZInQ.OneProof.frozenTarget` (2880fef1e) without editing `Main`. All declarations
compile, and the 23 theorems checked have axioms `[propext, Classical.choice, Quot.sound]` and no
`sorryAx` (VERIFIED: `Discharges-output.txt`, `FoldCheck-output.txt`).

---

## 1. `Γ₁(N)`-new with trivial character ⇒ `Γ₀(N)`-new (VERIFIED)

`isGamma0New_toCuspFormGamma0` follows the route the task named. Fix `g ∈ S_k(Γ₀(M))` with `dM ∣ N` and
`M ≠ N`, and write `F = f.toCuspFormGamma0 hχ`.

1. `restrict_levelRaise_gamma0`: restricting from `Γ₀` to `Γ₁` commutes with `V_d`. Both sides are
   `τ ↦ g(dτ)`.
2. `CuspForm.peterssonInnerCosets_restrict_restrict` (Tau Ceti) gives
   `⟪V_d g|Γ₁(N), F|Γ₁(N)⟫ = [Γ₀(N)·{±1} : Γ₁(N)·{±1}] · ⟪V_d g, F⟫`.
3. `Newform.restrict_toCuspFormGamma0` gives `F|Γ₁(N) = f`.
4. By (1), the left side is `⟪V_d (g|Γ₁(M)), f⟫`, which is `0` by `TauCeti.mem_cuspFormsNew_iff`.
5. The index is nonzero (`relIndex_gamma1_gamma0_ne_zero`), so `⟪V_d g, F⟫ = 0`.

**The Hecke condition.** Tau Ceti has untwisted double-coset operators on `S_k(Γ₀(N))`
(`heckeSlashGamma0CuspFormEnd`), but no Hecke-ring action there. `heckeGamma0` is their `ℤ`-linear
extension to `𝕋(Δ₀(N), Γ₀(N))`, built the same way Tau Ceti builds `twistedHeckeSlashCuspFormCharLinearMap`.
`coe_heckeGamma0` proves that on functions, `heckeGamma0 T F` is Tau Ceti's nebentypus action
`heckeRingHomCuspCharSpace k 1 T` applied to `F|Γ₁(N)`. The proof is by induction on `T`
(`HeckeCosetModule.induction_linear`), using `twistedHeckeSlashSum_eq_heckeSlashSum`: at the trivial
character, every coset weight is `1`. A newform's eigenvalue equations therefore transfer
(`isGamma0Newform_toCuspFormGamma0`), as do `a₁ = 1` and the coefficients
(`coeffGamma0_toCuspFormGamma0`), because `toCuspFormGamma0` re-reads the same function.

## 2. The converse: classical `Γ₀(N)` newform ⇒ Tau Ceti newform with `χ = 1` (VERIFIED)

The task did not ask for this direction. It is proved so that the new leaf is no stronger than
bfh-kronecker's.

* `isGamma0New_iff`: `IsGamma0New F` is equivalent to `F` lying in the Petersson complement of
  `cuspFormsOldGamma0`, the span of the `V_d S_k(Γ₀(M))`.
* `cuspFormsOld_le_comap_trace`: the trace from `Γ₁(N)` to `Γ₀(N)` maps the `Γ₁(N)`-old subspace into
  the `Γ₀(N)`-old subspace. The argument:
  * Take `g ∈ S_k(Γ₁(M))`. The diamond sum `∑_{u ∈ (ℤ/N)ˣ} ⟨u mod M⟩ g` has trivial nebentypus
    (`sum_diamondOpCusp_mem_cuspFormCharSpace_one`, since `ZMod.unitsMap` is surjective).
  * So that sum is the restriction of some `g₀ ∈ S_k(Γ₀(M))` (`cuspFormCharSpace_one_eq_range` at
    level `M`).
  * Then `trace (V_d g) = V_d g₀` (`cuspFormTraceGamma0_levelRaise`).
* `restrict_mem_cuspFormsNew_of_isGamma0New`: by `mem_cuspFormsNew_iff_of_mem_cuspFormCharSpace`, it
  suffices to test against old forms `G` of trivial nebentypus.
  * Such a `G` is the restriction of some `G₀` on `Γ₀(N)`.
  * Its trace `#(ℤ/N)ˣ · G₀` is `Γ₀(N)`-old (`cuspFormTraceGamma0_restrict`), so `G₀` is `Γ₀(N)`-old.
  * Hence `⟪G, F|Γ₁⟫ = index · ⟪G₀, F⟫ = 0`.
* `IsGamma0Newform.toNewform` is the restriction, as a Tau Ceti `Newform N k` with `χ = 1`. Its
  eigenvalues come from `coe_heckeGamma0`. It is nonzero because `a₁ = 1` and the q-expansion of `0` is
  `0`. Converting back recovers `F` (`toCuspFormGamma0_toNewform`).
* `bfhClauseIIGamma0_iff : BFHClauseIIGamma0 ↔ BFHClauseIIKronecker`. Combined with bfh-kronecker's
  `bfhClauseIIKronecker_iff`, this gives `bfhClauseIIGamma0_iff_bfhClauseII`.

So the dictionary between "Tau Ceti `Γ₁(N)`-newform with `χ = 1`" and "classical `Γ₀(N)` newform" is now
a pair of Lean theorems: `isGamma0Newform_toCuspFormGamma0` and `IsGamma0Newform.toNewform`. It is no
longer a definitional reading.

## 3. The leaf and its rating: printed form

Printed statement: the statement-check read of BFH, Invent. Math. 102 (1990), opening theorem,
pp. 543–544, as reported in the task brief. Its record is not on this host: a grep of `docs/` and of
every origin branch's `docs/one-proof/STATEMENT-CHECKS.md` and `reviews.tsv` found no BFH entry. The
brief reports that the check rates every clause printed except the newform identification. Paraphrase
(not a quotation): `f` a newform of even weight `k` and trivial character on `Γ₀(N)`; `ε` the sign of
the functional equation of `L(s, f)`; `S` a finite set of primes containing the primes dividing `N`. Then
some fundamental discriminant `D` has `ε D > 0`, every `p ∈ S` split in `ℚ(√D)`, and
`L(k/2, f, χ_D) ≠ 0` with `χ_D(n) = (D / n)`.

| Print | Leaf | Rating |
| --- | --- | --- |
| `f` newform, even weight `k`, trivial character, on `Γ₀(N)` | `F : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2`, `IsGamma0Newform F` | instance `k = 2`; the classical definition (below) |
| `ε` the sign of the functional equation of `L(s, f)` | `IsFESignGamma0 F ε` | the definition, written as the functional equation of the completed `L(s, F)` at level `N` |
| `S` finite, primes, containing the primes dividing `N` | `S : Finset ℕ`, `∀ p ∈ S, p.Prime`, `p ∣ N → p ∈ S` | literal |
| `D` the fundamental discriminant of a quadratic field | `Int.IsFundamentalDiscr D ∧ D ≠ 1` | literal (Mathlib) |
| `ε D > 0` | `0 < ε * D` | literal |
| every `p ∈ S` split in `ℚ(√D)` | `SplitsInQuadratic D S` | literal (bfh-leaf) |
| `L(k/2, f, χ_D) ≠ 0`, `χ_D(n) = (D / n)` | `KroneckerCentralValueNeZeroGamma0 F D` | literal: the series `∑ aₙ(F)(D/n) n^{−s}`, its entire continuation at the centre `s = 1 = k/2` |

**`IsGamma0Newform` is the classical newform (primitive form) on `Γ₀(N)`.** It requires:

* an eigenvector of `T_n` for `(n, N) = 1`;
* in the Atkin–Lehner new subspace (the Petersson complement of the span of `g(dτ)`, `g ∈ S_k(Γ₀(M))`,
  `dM ∣ N`, `M < N`);
* `a₁ = 1`.

References: Atkin–Lehner, Math. Ann. 185 (1970); Miyake, *Modular forms*, §4.6; Diamond–Shurman, §5.8
(UNVERIFIED section numbers). Definitions that also demand eigenvalues at `p ∣ N` describe the same
class, by multiplicity one (STANDARD, Atkin–Lehner 1970). Two Tau Ceti inputs enter, the same two that
Tau Ceti's own `Newform` uses:

* `T_n` is Tau Ceti's Hecke-ring element `heckeTCompositeGamma0 N n`;
* the double-coset operators carry Tau Ceti's slash normalization, a nonzero scalar times the classical
  one, which does not affect the eigenvector condition.

**Rating: printed form**, a direct instance at `k = 2`. Every clause is the print's notion over a genuine
Mathlib, Tau Ceti or kernel definition. The leaf is not stronger than the print, and it is equivalent in
Lean to bfh-kronecker's and bfh-leaf's leaves (§2). The one point the review had left open is now closed
in Lean, not by reading. **Flag:** the leaf has been read (the statement-check read of pp. 543–544,
reported in the brief). If the integrator cannot find that read in the repository, flag the row unread,
as bfh-kronecker did.

**Docstring fix.** `BFHClauseIIKronecker` (and the new leaf) now say:

* weight `k`;
* central value `L(k/2, f, χ_D)`, with centre `s = k/2 = 1` at weight 2;
* source: the statement-check read of BFH, Invent. Math. 102, pp. 543–544.

The earlier text said "even weight `2k`, `L(k)`" and cited the earlier review.

## 4. The use and the fold (VERIFIED)

`frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhGamma0` composes `bfhClauseIIKronecker_of_bfhClauseIIGamma0`
with bfh-kronecker's assembly. The leaf is used once, at `B = 4`, with `S` the primes dividing `2N`
(`exists_heegnerDisc_of_bfhClauseIIKronecker`).

**Hand fold on main** (`hFH` is a top-level binder, so `autofold.py`, which parses only bundle binders,
does not apply; the spec is in `scratch/bfh-gamma0/autofold.json`):

* `Main.lean`: add `import ZInQKernel.Contrib.OneProof.BFHGamma0`. Replace the binder
  `(hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE)` by `(hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)`. Replace the
  call `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves A B H
  (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH) hL3` by
  `ZInQ.BFHPrinted.frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhGamma0 A B H hBFH hL3`, with `A`
  (`sixContactMin_of_open35 r t l g`), `B` (`ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.… ) hCM h33`)
  and `H` verbatim.
  * Checked without editing `Main`: `frozenTarget_bfhGamma0` in `scratch/bfh-gamma0/FoldCheck.lean`,
    with main's 15 binders (`OpenResearchLeaves26`, `OpenTextbookLeaves12`, `OpenAddedLeaves17`,
    `OpenGlue8`, the six H29Split leaves), axioms standard.
  * Drop-in alternative for every `B`: replace only the argument by
    `fhNonvanishing_of_bfhClauseIIGamma0 hBFH` (`frozenTarget_bfhGamma0_allB`).
* kinds.tsv: replace the row `(frozenTarget, hFH; consequence; GLUE GLUE)` by `(frozenTarget, hBFH)`,
  with kind `published`, strict `LEAF`, strictest `LEAF`. That is **−1 GLUE in both columns**.
* The fold needs bfh-kronecker's `BFHKronecker.lean` and `BFHPrinted/Kronecker.lean`, which are on this
  branch.

**`#discharges`** (VERIFIED, `Discharges-output.txt`): `56 open hypotheses, 3109 theorems checked,
8 discharge one`. None comes from this task, which is expected: no theorem has `hFH`'s type. The one
`hFH` line is fh-printed's `friedbergHoffsteinB_FE_of_printed`, imported transitively.

Build: on a build tree copied from `~/dzq-check2` (origin/main 2880fef1e),
`lake build ZInQKernel.Contrib.OneProof.BFHGamma0` and `ZInQKernel.OneProof.Discharges` succeeded
(10130 jobs). The new files raise no warnings beyond the standard note that they import modules without
the `module` keyword.

## 5. What remains

* The hand fold itself (Main.lean, kinds.tsv, locators.md, regeneration of OPEN.md). The rules forbid
  editing those files here.
* Recording the statement-check read of BFH pp. 543–544 in the repository, if it is not there. This host
  has no record of it.
