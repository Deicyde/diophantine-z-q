# cox-lattice: the textbook leaf `CMBranch.CoxProperLattice`, proved

Task cox-lattice (2026-11-17). Base: `origin/wip/cm-branch2` 120fa22b (cm-branch2's CM-branch fold, with its
`CoxCore.lean`), `origin/main` d435851d merged (clean). Results log: `scratch/cox-lattice/log.md`. Marks: VERIFIED
(compiled, or read in the tree / in diophantine_zq.tex), STANDARD (published, exact reference), UNVERIFIED (theorem
numbers from memory; no network on this host), SPECULATIVE.

## 1. Result

**`HDec.CMBranch.CoxProperLattice` is proved in Lean from Mathlib alone, with its statement unchanged and no extra
hypothesis.** VERIFIED (compiled; `#print axioms` = `propext, Classical.choice, Quot.sound`):

```lean
theorem HDec.CMBranch.CoxLattice.coxProperLattice_proof : HDec.CMBranch.CoxProperLattice
theorem HDec.CMBranch.reducedCMPeriod_of_leaves_cox (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hcorr : HomUnify.HomLatticeCorr) (h11b : ZInQ.LeafPush2.T11b_Rigidity) : ReducedCMPeriod
```

(`ZInQKernel/Contrib/OneProof/CoxProperLattice.lean`, importing `CMBranch.PeriodLattice`, which imports the module that
declares the statement, `CMBranch.ReducedPeriod`). So the manuscript's uncited step L598-599 (`ReducedCMPeriod`) now
rests only on the chain's textbook fields `t35`, `homLatticeCorr`, `t11b`, and the CM branch no longer uses Cox (which
is not in the manuscript's bibliography): the DEPARTURE is removed.

**Overlap with cm-branch2.** While this task ran, cm-branch2 proved the same leaf independently
(`HDec.CMBranch.coxProperLattice_proof`, `CMBranch/CoxProof.lean`, pushed at 295488eb, after this task's scratch proof
compiled at 12:05) and moved its fold to `CMInputs3` and the next generation `Open73`. Merged here
(origin/wip/cm-branch2 75e3c1d8, clean). To avoid a duplicate name this task's theorem lives in the sub-namespace
`CoxLattice`; the two proofs are independent (same outline: Cox 7.5's computation + cm-branch2's `discr_order`).
The integrator may use either.

**Fold.** The CM-branch inputs shrink from cm-branch2's `CMInputs2` (6 statements) to `CMInputs3` (5: the glue
`CMFibreSplit`, the leaves `FowlerProp27`, `CMjDegree`, `CMPotentialGood`, `CMHeight62`; the structure is cm-branch2's).
Dry run with this task's proof: `HDec.HSyn.sixContactMin_of_open72_coxlattice (r : OpenResearchLeaves53)
(t : OpenTextbookLeaves18) (l : OpenAddedLeaves27) (c : CMBranch.CMInputs3) : ZInQ.SixContactMin`
(`ZInQKernel/Contrib/OneProof/CoxProperLattice/Fold.lean`). Spec `scratch/cox-lattice/autofold.json` (= cm-branch2's
updated spec, with this proof as alternative provider). **Net change against cm-branch2's fold at this task's start
(120fa22b): GLUE column 0** (CoxProperLattice was a leaf, not GLUE); **strict count −1** (under the kit's rule a new leaf
pending review counts as GLUE: +5 becomes +4); leaves −1. Against cm-branch2's updated spec (75e3c1d8): 0 (identical).

**Manuscript check (L598-600).** Correct as written; no missing hypothesis (§4).

## 2. The proof

Statement (verbatim, `CMBranch/ReducedPeriod.lean` L65): for an order `R` of an imaginary quadratic field `k`
(`IsImagQuadOrder`: totally complex, `[k:ℚ] = 2`, `R ⊆ 𝓞_k`, `f = [𝓞_k : R] ≠ 0`) and `Λ = c(ℤ + ℤτ) ⊂ ℂ¹`, `c ≠ 0`,
`Im τ > 0`, with a ring isomorphism `φ : R ≃ {α ∈ ℂ | αΛ ⊆ Λ}`, there is a primitive `(a, b, c')`, `a > 0`, with
`aτ² + bτ + c' = 0` and `b² − 4ac' = orderDisc R = f² d_k`.

| step | Lean | label |
|---|---|---|
| 1. `R` contains `f·ω ∉ ℤ`, for `ω ∈ 𝓞_k \ ℚ` (an integral multiple of any `x ∉ ℚ`, which exists as `[k:ℚ] = 2`; `f·g ∈ H` for `g ∈ G`, `f = [G:H]`) | `exists_nonint` (`IsAlgebraic.exists_integral_multiple`, `AddSubgroup.nsmul_relIndex_mem`) | on-the-spot |
| 2. `α := φ(fω)` is a multiplier `∉ ℤ` (`φ` fixes `ℤ`); `α = p + qτ`, `q ≠ 0`, `ατ ∈ ℤ + ℤτ`, so `qτ² + (p − q')τ − p' = 0` | `mem_mult_iff` (the factor `c` cancels) | on-the-spot |
| 3. divide by the gcd and fix the sign: a primitive `(a, b, c')`, `a > 0`, with `aτ² + bτ + c' = 0` | `exists_prim_form` | on-the-spot |
| 4. the multipliers of `c(ℤ + ℤτ)` are exactly `ℤ + ℤ·aτ` | `mem_mult_iff_order`, `dvd_of_mul_tau`, `dvd_of_prim` | on-the-spot (Cox Lemma 7.5's computation, UNVERIFIED number) |
| 5. `θ := φ⁻¹(aτ)`: `R = ℤ + ℤθ`, `θ² + bθ + ac' = 0`; `b² − 4ac' < 0`, so `θ ∉ ℚ` and `1, θ` are `ℚ`-independent | `disc_neg`, in `coxProperLattice_proof` | on-the-spot |
| 6. `disc(ℤ + ℤθ) = [𝓞_k : ℤ + ℤθ]² d_k`, and `disc(1, θ) = b² − 4ac'`; hence `b² − 4ac' = f² d_k` | `discr_pair`, `discr_order` (cm-branch2's `CoxCore`, copied; `AddSubgroup.relIndex_eq_abs_det`, `Algebra.discr_of_matrix_vecMul`) | on-the-spot (Cox Lemma 7.2 / (7.3), UNVERIFIED numbers) |

Proof sketches of the on-the-spot steps (each is the Lean proof in prose):

* *Step 4 (Cox 7.5, elementary half).* `β` is a multiplier iff `β·1, β·τ ∈ ℤ + ℤτ`. Write `β = m + nτ`. Using
  `aτ² = −bτ − c'`, `a(m + nτ)τ = (am − nb)τ − nc'`; if this is `a(p + qτ)`, comparing coefficients (`τ ∉ ℝ`) gives
  `a | nb` and `a | nc'`; with `a | na` and `gcd(a, b, c') = 1` (Bézout twice), `a | n`. Conversely `aτ·τ = −bτ − c'`, so
  `ℤ + ℤaτ` consists of multipliers.
* *Step 6 (discriminant of an order).* `(1, θ)` and an integral basis are `ℚ`-bases of `k`; the change-of-basis
  determinant `δ` has `|δ| = [𝓞_k : ℤ + ℤθ]` (index of lattices) and `disc(1, θ) = δ² disc(𝓞_k)`; the trace form of
  `(1, θ)` is `[[2, −b], [−b, b² − 2ac']]`, with determinant `b² − 4ac'`.
* *Why no isomorphism invariance of discriminants is needed.* The ring isomorphism `φ` is used only to transport the
  generator `aτ` and its quadratic equation into `R ⊆ k`; the discriminant is then computed for `R ⊆ k` itself. The
  route suggested in the task (`Algebra.discr_eq_discr_of_algEquiv`) is not needed.

The hypothesis `IsTotallyComplex k` of `IsImagQuadOrder` is not used (it follows from `b² − 4ac' < 0` anyway).

## 3. Files

| file | content |
|---|---|
| `ZInQKernel/Contrib/OneProof/CoxProperLattice.lean` | `CoxLattice.*` (the lemmas above, `CoxLattice.coxProperLattice_proof`), `reducedCMPeriod_of_leaves_cox` |
| `ZInQKernel/Contrib/OneProof/CoxProperLattice/Fold.lean` | `sixContactMin_of_open72_coxlattice` (fold dry run over cm-branch2's `CMInputs3`) |
| `scratch/cox-lattice/Cox.lean` | the same proof over `import Mathlib`, with verbatim copies of the statement and its definitions |
| `scratch/cox-lattice/autofold.json` | cm-branch2's hand-fold spec with the leaf removed |
| `scratch/cox-lattice/Discharges.lean`, `discharges.txt` | `#discharges` |

## 4. Manuscript check: L598-600

The sentence (diophantine_zq.tex L598-599, in the paragraph "CM fibers"): for a reduced CM period `τ = x + iy`,
`√3/2 ≤ y ≤ √|Δ|/2`, where `Δ < 0` is "the discriminant of the full geometric endomorphism order of `E`" (L585-586).
No citation. Label: **ELLIOT (uncited manuscript step)**.

**Verdict: correct as written; no unstated hypothesis is needed.** VERIFIED in Lean, as `CMBranch.ReducedCMPeriod`
(cm-branch's form: for every `σ : K → ℂ` there is a period `τ` of `E^σ` with both bounds), from the chain's textbook
fields only (`reducedCMPeriod_of_leaves_cox`). The two implicit conventions, which the Lean proof makes explicit:

1. *Which order.* The period lattice `Λ_σ` of `E^σ(ℂ)` has multiplier ring `End(E^σ_ℂ)`, and `Δ` is the discriminant
   of `End(E_{L̄})`. These are isomorphic rings for every `σ` (rigidity; `CMPeriodLattice`, proved from T35,
   `HomLatticeCorr`, T11b). The isomorphism is enough: the discriminant is recovered from the multiplier ring
   (Step 6), so `σ` does not matter.
2. *Lattice normalisation.* "Period" means `Λ_σ = c(ℤ + ℤτ)`, `Im τ > 0`; "reduced" means `τ` in the closed fundamental
   domain `|x| ≤ 1/2`, `|τ| ≥ 1` (Mathlib's `ModularGroup.fd`). The bounds are homothety invariant. The lower bound
   holds for every `τ` in that domain; the upper bound `y = √|Δ|/(2a) ≤ √|Δ|/2` holds for every period `τ` of `Λ_σ`
   in the upper half plane (reducedness is not needed for it), since `a ≥ 1`.

Every reduced period satisfies both bounds (not only some), so the manuscript's "a reduced CM period" is unambiguous.

## 5. Labels, on-the-spot steps, Known issues

* **ELLIOT (uncited manuscript step)**: L598-599, the reduced-period bounds (§4).
* **On-the-spot**: Steps 1-6 of §2 (sketches there). Cox, *Primes of the form x² + ny²*, Lemma 7.5, Lemma 7.2 and (7.3)
  (UNVERIFIED numbers) is where they are classically found; Cox is not cited by the manuscript, and after this task it
  is not used as a leaf either.
* **Known issues**: none. The statement of `CoxProperLattice` is true as stated (proved), not vacuous (its hypotheses
  are met by the period lattice of every CM curve, `CMPeriodLattice`), and not inert (it is read by
  `reducedCMPeriod_of`). No Gross–Zagier or Tian–Yuan–Zhang argument is used; no consumer's statement is changed; no
  file outside `ZInQKernel/Contrib/OneProof/CoxProperLattice*` is edited.

## 6. The fold and `#discharges`

See §1 and `scratch/cox-lattice/autofold.json`: replace `HDec.HSyn.sixContactMin_of_open72 r t l` in `frozenTarget` by
cm-branch2's `sixContactMin_of_open73_cm r t l` (next generation `OpenResearchLeaves54CM`, already without
`gonzalezRotgerThm512X6RCF` and with the 5 CM statements, not 6), or equivalently
`sixContactMin_of_open72_coxlattice r t l ⟨…5 fields…⟩` on the current generation.

### 6.1 Compile record and `#discharges` (VERIFIED)

* `lake build ZInQKernel.Contrib.OneProof.CoxProperLattice` EXIT 0 (11763 jobs); after merging cm-branch2 75e3c1d8,
  `lake build ZInQKernel.Contrib.OneProof.CoxProperLattice.Fold` EXIT 0 (15396 jobs); `scratch/cox-lattice/Axioms.lean`
  (`axioms-out.txt`): `CoxLattice.coxProperLattice_proof`, `reducedCMPeriod_of_leaves_cox`,
  `sixContactMin_of_open72_coxlattice` depend on `[propext, Classical.choice, Quot.sound]`;
  `example : CoxProperLattice := CoxLattice.coxProperLattice_proof` checks
  (the registered form: exactly the statement, no extra hypotheses).
* `scratch/cox-lattice/Discharges.lean` (imports `OneProof.Main`, `OneProof.Discharges`, `CoxProperLattice`,
  `CoxProperLattice.Fold`), output `scratch/cox-lattice/discharges.txt` (re-run after the merge): "30 open hypotheses, 12378 theorems checked,
  120 discharge one" = 16 pre-existing reductions on main (carayol, ds965, deRham, raynaud, javanpeykar, the two `X₆`
  rows, y3, deligne, pazuki, hodgeTate) + 104 projections of cm-branch2's copied `_r5` structures (the known noise
  for copied structures, as cm-branch2 §7.1). No theorem of this task discharges a top field, as expected:
  `CoxProperLattice` is not a top field of `frozenTarget` on main; it is a field of cm-branch2's not-yet-folded
  `CMInputs2`, so the gain shows in the hand fold (§1), not in `#discharges`.
* The autofold spec is a hand fold (cm-branch2's format, `replaces`), so `autofold.py --dry-run` does not apply;
  `Fold.lean` is the dry run.

## 7. Rating of new leaves

No new leaf: the task removes one (`CoxProperLattice`, consequence form, pending review) and adds none.
