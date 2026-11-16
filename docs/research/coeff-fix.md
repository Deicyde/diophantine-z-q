# coeff-fix: Deligne–Serre 4.1 as printed (trace = `T_p`-eigenvalue, `ε(−1) = −1`)

Task coeff-fix (2026-11-16), base wip/coeff-ext bca51e5c (`git merge origin/main`: already up to date).
Scratch: `scratch/coeff-fix/` (log `log.md`). Contribution: `ZInQKernel/Contrib/OneProof/DSThm966EV.lean`
(namespace `DSThm966EV`), next to coeff-ext's `DSCoeffExt.lean`, which is unchanged.

## 1. Result

**`dsThm966` now rests on Deligne–Serre's Thm 4.1 stated as printed. The two GLUE steps the review found
inside coeff-ext's `DSCoeffExt.DSThm966Printed` are now proved in Lean.** VERIFIED: compiled, `#discharges`,
axioms `propext`, `Classical.choice`, `Quot.sound`.

```lean
theorem DSThm966EV.dsThm966_of_printed (h : DSThm966EV.DSThm966Printed) : ZInQ.Contrib.HodgeSplit.DSThm966
```

1. **Trace over the eigenvalue.** In the new leaf the hypothesis is Tau Ceti's
   `HeckeRing.GL2.EigenformAwayFromLevel N 1`: a nonzero cusp form in the `ε`-space of the diamond operators,
   an eigenvector of `T_n` for every `n` prime to `N`. There is no `a₁ = 1` and nothing is asked at `p ∣ N`.
   The conclusion is `tr ρ(Frob_p) = F.eigenvalue p`, the `T_p`-eigenvalue. The coefficient form is now glue,
   `exists_eigenform`: a normalized eigenform is a full Tau Ceti `Eigenform`
   (`DSCoeffExt.isNormalizedEigenformDS_of`), and its `T_p`-eigenvalue equals `coeff g p` because `a₁ = 1`
   (`Eigenform.qExpansion_coeff_eq_eigenvalue`).
2. **`ε(−1) = −1`.** This is now a hypothesis of the leaf, as Deligne–Serre assume. The one consumer,
   `dsThm966_of_printed`, supplies it through the glue `char_neg_one`. That glue is the weight-1 case of the
   parity lemma `TauCeti.char_neg_one_of_mem_cuspFormCharSpace` (Parity.lean:113), applied to the nonzero form
   (`a₁ = 1`) in the `χ`-space (T25's `mem_cuspFormCharSpace_of_hasNebentypus`). `DSThm966` has no other
   consumer that needs the hypothesis: the field's own type is unchanged.

`#discharges` output (`scratch/coeff-fix/discharges-output.txt`):

```
DISCHARGES [OpenResearchLeaves26.dsThm965Weak] by DSCoeffExt.dsThm965Weak_of_printed
  still assumes: [DSCoeffExt.DSThm965Printed, DSCoeffExt.EigenformCoeffFieldFinite]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.dsThm966] by DSThm966EV.dsThm966_of_printed
  still assumes: [DSThm966EV.DSThm966Printed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.dsThm966] by DSThm966EV.dsThm966_of_printedFull
  still assumes: [DSThm966EV.DSThm966PrintedFull]
  axioms: [propext, Classical.choice, Quot.sound]
```

**dsThm965Weak and `k = 2`: left unchanged.** Not every consumer is at weight 2 (VERIFIED, read in the
source). `DSThm965Weak → DSThm965` (TailZ38:83). `DSThm965` is then used only by `r14DetWtGe2_of_ds`
(TailS:1185), which proves `R14DetWtGe2` for every `k ≥ 2`. That result feeds `R14Det` and `EigenformHT`, the
research fields `r14` and `r13` (TailX:200–202). Those are passed whole to TailD:137, TailK:323 and
TailA:3718, where the weight comes from the Serre/Khare–Wintenberger step and is not fixed. So a `k = 2`
`EigenformCoeffFieldFinite` cannot give `DSThm965Weak`, and the leaf is left in its general-`k` form
(coeff-ext's rating stands: printed for `k = 2` by Diamond–Shurman 6.5.1, and for general `k` the standard
consequence of Shimura 1971 Thm 3.52 with the Hecke stability of §3.5, locators UNVERIFIED). Of the two
targets, the first is met (dsThm966 is now a LEAF: −1 GLUE) and the second does not apply.

## 2. The new leaf and its rating

```lean
def DSThm966EV.DSThm966Printed : Prop :=
  ∀ (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (F : EigenformAwayFromLevel N 1),
    F.χ = MulChar.toUnitHom ε → ε (-1) = -1 →
    ∃ ρ : GQ →* GL (Fin 2) ℂ, Continuous ρ ∧ (Set.range ρ).Finite ∧
      ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N),
        (∀ v : ValuationSubring Qbar, LiesOver v p →
          ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).trace =
              F.eigenvalue (p.toPNat hp.pos) (coprime_of_not_dvd hp hpN) ∧
          (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).det = ε (p : ZMod N)
```

**LEAF, published: Deligne–Serre, *Formes modulaires de poids 1*, Ann. Sci. ÉNS (4) 7 (1974), Thm 4.1 (4.1.1),
p. 514.** The locator comes from the brief; I have not read the page (no network), so it is UNVERIFIED.

**Rating: printed form.** Point by point:

* *The form.* Deligne–Serre's hypothesis, as recalled (UNVERIFIED), is a nonzero modular form of type `(1, ε)`
  on `Γ₀(N)`. The leaf takes a nonzero cusp form on `Γ₁(N)` with diamond character `ε`, which is the same
  space restricted to cusp forms. That is a special case, so the leaf is weaker.
* *Eigen-ness.* Deligne–Serre ask for an eigenvector of `T_p`, `p ∤ N`. Tau Ceti's structure asks for one of
  `T_n` for every `n` prime to `N`. That is at least as strong a hypothesis (in fact equivalent, since those
  `T_n` are polynomials in the `T_p` and the diamond operators), so the leaf is weaker or equal. There is no
  normalization in either.
* *`ε(−1) = −1`* is Deligne–Serre's standing assumption, kept as a hypothesis.
* *Conclusion.* A continuous `ρ` with finite image ("représentation linéaire" of the profinite `G_ℚ`, read as
  in the old field), unramified outside `N`, with `tr ρ(Frob_p) = a_p` (the `T_p`-eigenvalue) and
  `det ρ(Frob_p) = ε(p)`. These are the printed conclusions, without the irreducibility clause.
* *Conventions* are inherited from the old field. `G_ℚ = Gal(AlgebraicClosure ℚ / ℚ)` with places as valuation
  subrings, `Frob_𝔭` is pkg-I4's arithmetic Frobenius `IsArithFrob`, and "unramified" means trivial on every
  inertia group above `p`. Tau Ceti's `T_p` for `p ∤ N` is the classical one: its coefficient criterion is
  `a_{pm} = λ a_m − ε(p) p^{k−1} a_{m/p}`.

**Reading risk and fallback.** Thm 4.1 might be printed for newforms only (I could not check). The
consumer needs only full eigenforms, so the file also states `DSThm966PrintedFull`, the same leaf over Tau
Ceti's full `Eigenform N 1`. Two facts are proved: `printedFull_of_printed : DSThm966Printed →
DSThm966PrintedFull`, and `dsThm966_of_printedFull`. If a reader finds the print narrower, the fold can use `DSThm966PrintedFull` with
`dsThm966_of_printedFull` and nothing else changes.

## 3. The glue (all proved, `DSThm966EV.lean`)

* `coprime_of_not_dvd`: `p ∤ N`, `p` prime ⇒ `Nat.Coprime p N`. This is the index proof in
  `F.eigenvalue p _`.
* `char_neg_one`: `IsNormalizedEigenform g χ` (weight 1) ⇒ `χ(−1) = −1` (parity lemma).
* `exists_eigenform`: `IsNormalizedEigenform g χ` ⇒ a full Tau Ceti `Eigenform F` with `F.χ = χ` on units and
  `F.eigenvalue p = coeff g p` for every prime `p`.
* `printedFull_of_printed` (`F ↦ F.toEigenformAwayFromLevel`), `dsThm966_of_printedFull`,
  `dsThm966_of_printed`.

Lean pitfall (VERIFIED): `(⟨p, h⟩ : ℕ+)` elaborates as `Subtype.mk` at type `{n // 0 < n}`, and `rw` with
`F.eigenvalue ?n` then fails on a type mismatch. Use `p.toPNat h`.

## 4. Checks

* `scratch/coeff-fix/DSThm966EV.lean` compiles with `lake env lean` (a copy of the contribution).
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.DSThm966EV`:
  succeeded (13700 jobs, 6 min; `scratch/coeff-fix/build.log`). Because the build tree was copied
  with `cp -r`, modules were recompiled. `ZInQ.OneProof.frozenTarget`: standard axioms.
* `#discharges` (`scratch/coeff-fix/DischargesRun.lean`): the output is above.
* Autofold (`scratch/coeff-fix/autofold.json`, which supersedes `scratch/coeff-ext/autofold.json`: the same
  dsThm965Weak discharge, and dsThm966 from the new leaf): the dry run (`scratch/coeff-fix/autofold-dryrun.txt`) gives
  strict 34/11 on 45 → 35/11 on 46, strictest 34/11 → 35/11. That is the same as coeff-ext's spec: the
  script already counted coeff-ext's `dsThm966Printed` as a LEAF ("unread"), so this task's −1 GLUE is in the
  review's rating, not in kinds.tsv. The generated module, with line 1 stripped (`scratch/coeff-fix/FoldCheck.lean`),
  compiles: `HDec.HSyn.sixContactMin_of_open36` uses `propext`, `Classical.choice` and `Quot.sound`.

## 5. For the integrator

* Fold with `python3 scripts/one_proof/autofold.py scratch/coeff-fix/autofold.json` instead of coeff-ext's
  spec.
* The locators.md row for `dsThm966Printed` changes to: Deligne–Serre 1974, Ann. Sci. ÉNS (4) 7, Thm 4.1
  (4.1.1), p. 514, as printed (eigenvector of the `T_p`, `p ∤ N`; `ε(−1) = −1`; trace = `T_p`-eigenvalue);
  unread.
