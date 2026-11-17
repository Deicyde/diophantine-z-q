# coeff-rational: `K_f` is a number field, with no diamond-operator leaf (strict GLUE −1)

Task coeff-rational (2026-11-16). Base: wip/coeff-field 5bb50efa, merged with origin/main c1e4ed1b (merge commit
2841989d). Scratch files are in `scratch/coeff-rational/` (log `log.md`). Contribution:
`ZInQKernel/Contrib/OneProof/CoeffRational.lean` (namespace `CoeffRational`, about 210 lines). It imports coeff-field's
`EigenformCoeffFieldFinite.lean`, which is unchanged.

## 1. Result

**main's open field `eigenformCoeffFieldFinite : DSCoeffExt.EigenformCoeffFieldFinite` (strict GLUE, kind
composite) is now proved in Lean from two printed-form leaves on `S_k(Γ₁(N))`. One is Shimura's integral basis
(coeff-field's `Gamma1IntegralSpan`). The other is new: `HeckePrimeIntegralToRational`, which says that `T_p`
preserves integrality. It replaces coeff-field's diamond-operator leaf.** The diamond operators are now derived
in Lean, from Dirichlet's theorem and Tau Ceti's `T_p` recurrence. The autofold dry run gives strict
**16/21 on 37 → 18/20 on 38** (strictest the same): GLUE −1. VERIFIED (compiled, `#discharges` run, axioms
`propext`, `Classical.choice`, `Quot.sound`).

```lean
theorem CoeffRational.eigenformCoeffFieldFinite_of_heckePrime
    (hA : CoeffFieldFinite.Gamma1IntegralSpan) (hT : HeckePrimeIntegralToRational) :
    DSCoeffExt.EigenformCoeffFieldFinite
theorem CoeffRational.eigenformCoeffFieldFinite_of_rationalHeckeSpan (hS : RationalHeckeSpan) :
    DSCoeffExt.EigenformCoeffFieldFinite
theorem CoeffRational.diamondIntegralToRational_of_heckePrime (hT : HeckePrimeIntegralToRational) :
    CoeffFieldFinite.DiamondIntegralToRational
theorem CoeffRational.rationalHeckeSpan_of_heckePrime (hA : Gamma1IntegralSpan) (hT : HeckePrimeIntegralToRational) :
    RationalHeckeSpan
theorem CoeffRational.rationalHeckeSpan_of_diamond (hA : Gamma1IntegralSpan) (hB : DiamondIntegralToRational) :
    RationalHeckeSpan
```

`#discharges` (`scratch/coeff-rational/discharges-output.txt`; the full output is in `discharges-full.txt`):

```
DISCHARGES [OpenResearchLeaves28.eigenformCoeffFieldFinite] by CoeffRational.eigenformCoeffFieldFinite_of_heckePrime
  still assumes: [CoeffFieldFinite.Gamma1IntegralSpan, CoeffRational.HeckePrimeIntegralToRational]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves28.eigenformCoeffFieldFinite] by CoeffRational.eigenformCoeffFieldFinite_of_rationalHeckeSpan
  still assumes: [CoeffRational.RationalHeckeSpan]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 45 open hypotheses, 6751 theorems checked, 18 discharge one
```

The two negative findings asked for in the brief:

* **The field cannot be narrowed to rational `f`** (VERIFIED, read in the source; §2). The chain reads it at the
  eigenform that Pan∘Berger attaches to the QM surface's `r₅`. That form's level, character and weight are a
  priori arbitrary, and the field is needed exactly to rule out weight `k ≥ 3`.
* **It cannot be proved outright from the tree** (§3). No library has a `ℚ`-structure on `S_k(Γ₁(N))` for `N > 1`.
  An explicit basis for a fixed level does not apply, because `N` and `k` are not fixed.

So "−1 with no new leaf" is out of reach. The route offered removes one GLUE by replacing the composite field
with two printed-form leaves, and it avoids coeff-field's diamond leaf, which carried a reading risk.

## 2. What the chain reads (VERIFIED, read in the source)

1. `eigenformCoeffFieldFinite` (TailZ45:66) is read once, at TailZ45:95:
   `dsThm965Weak := DSCoeffExt.dsThm965Weak_of_printed n.dsThm965Printed n.eigenformCoeffFieldFinite`.
2. `DSThm965Weak` becomes `HodgeSplit.DSThm965` (TailZ38:83). That is used at TailX:198–200:
   * `r13 := … eigenformHT_of_kato_ds r.eigenformHTNew … r.dsThm965 r.dsThm966`;
   * `r14 := … r14Det_of_printed r.dsThm965 r.dsThm966` (TailT:1532, through `r14DetWtGe2_of_ds`, TailS:1184,
     every `k ≥ 2`).
3. `r13 = PkgI4.EigenformHT` and `r14 = R14Det` / `EigenformRepExists` quantify over every
   `(ℓ, ι_C, ι_L, N, k, χ, g)`. Their consumers:
   * **`G0Galois.g12`** (TailA:2211), reached from TailD:137 (`g8_g12_of_leaves3`) and from TailK:394
     (`afterG7_of3`). Here `g` comes from `hPB : PkgI4.PanBerger` (I4Layer:1398/1412, the conclusion
     `∃ N k χ g, 0 < N ∧ 1 ≤ k ∧ IsNormalizedEigenform g χ ∧ …`) applied to `r₅`. R14 and R13 are applied at this
     `g` inside `G12Weight` (TailA:2059) to show `k = 2` (TailA:2222, `weight_match`). R14 is applied again inside
     `G12Det` (TailA:2078), after `k = 2`.
   * **`g14` / `iso_R14`** (TailA:3497): R14 at the weight-2 newform `f` produced by `g13`.
4. So `K_f` finite is needed for an eigenform of a priori arbitrary level, character and weight `k ≥ 2`. Pan's
   theorem gives it existentially. Nothing in the tree makes its coefficients rational. It should not be expected either (SPECULATIVE): a
   newform with `K_f = ℚ` has a 1-dimensional `A_f`, while the QM surface is 2-dimensional.
5. The weight-2 newform case is covered elsewhere: `r16CoreY` (Eichler–Shimura for `J₁(N)`, TailZ45:47) already
   contains `FiniteDimensional ℚ (coeffField f)` for weight-2 newforms. But `G12Weight` needs R14/R13 at weight
   `k` before `k = 2` is known. This agrees with ht-bypass's finding: R13 is used only to rule out `k ≥ 3`. So no
   existing leaf supplies the `k ≥ 3` case, and a fold reading only `k = 2` (Diamond–Shurman 6.5.1, printed) is
   not possible.

## 3. Why there is no outright proof

The arithmetic of `K_f` is the `ℚ`-structure of `S_k(Γ₁(N))` together with the rationality of the diamond
operators: the `q`-expansion principle on the `ℚ`-model of `X₁(N)`, or Eichler–Shimura with integral cohomology.
None of this exists in Mathlib, Tau Ceti or the other vendored libraries (VERIFIED by search):

* Mathlib has `q`-expansions of Eisenstein series of level 1 only (`EisensteinSeries/QExpansion.lean`) and the
  level-one graded ring.
* Tau Ceti has:
  * the Sturm bound (`SturmBound.lean`);
  * the complex-conjugate form `f_ρ` (`Conjugate.lean`). This is the case `σ = complex conjugation` of
    `Aut(ℂ)`-stability, too weak for finiteness;
  * Hecke operators on `Γ₁(N)` with their recurrences.

  None of these gives a `ℚ`-structure at level `N > 1`.

The operators that preserve rational `q`-expansions by their coefficient formulas alone are the `U_p` (`p ∣ N`) and
the `T_p` with `p ≡ 1 (mod N)`. coeff-field §2.4 showed that these do not determine `f`. I also checked the double
cosets `Γ₁(N) diag(1, p^m) Γ₁(N)` with `p^m ≡ 1 (mod N)`. For `m ≥ 2` they have only `p^m + 1` upper-triangular
representatives out of `p^m + p^{m−1}`, so the diamond operators come back (my count by hand, SPECULATIVE, not checked in Lean). A fixed-level basis checked in the
kernel cannot cover arbitrary `N`. Products of Eisenstein series spanning `S_k(Γ₁(N))` (Borisov–Gunnells,
Khuri-Makdisi) would be a deeper leaf, not a smaller one.

## 4. The leaves and their ratings

Every locator below is from memory, not read (no network), so all are UNVERIFIED.

### 4.1 `CoeffRational.HeckePrimeIntegralToRational` (new; main route)

```lean
def HeckePrimeIntegralToRational : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k), 2 ≤ k →
    p.Prime → ¬ p ∣ N →
    (∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = z) →
    ∀ n : ℕ, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)).coeff n = q
```

**LEAF, printed form (a weakening of the print).** The source statement is that the Hecke operators `T_n`
preserve `S_k(Γ₁(N), ℤ)`: Shimura 1971 §3.5 with Thm 3.52; Diamond–Im 1995 §12.3–12.4; Diamond–Shurman §6.5 for
`k = 2`.

The operator is Tau Ceti's genuine double-coset operator `[Γ₁(N) diag(1, p) Γ₁(N)]_k`. Its recurrence
`a_m(T_p g) = a_{pm}(g) + p^{k−1} a_{m/p}(⟨p⟩ g)` (Tau Ceti `HeckeSlash/Recurrence.lean:149`) is
Diamond–Shurman's normalization (Prop. 5.2.2).

The leaf keeps only primes `p ∤ N`, integral input and rational output, so the print implies it for `A = ℤ`,
`ℤ[1/N]` or `ℚ`. Compared with coeff-field's `DiamondIntegralToRational` it has less reading risk: `T_p`
belongs to the Hecke algebra in every convention, whether or not `𝕋_ℤ` is defined with the `⟨d⟩`.

**Remaining reading risk.** It applies only to a source whose `T_p` is the other double coset
`Γ₁(N) diag(p, 1) Γ₁(N) = ⟨p⟩⁻¹T_p` and whose Hecke algebra lacks the `⟨d⟩`. There, "every `T_n` integral"
still implies the leaf, through `T_p² − T_{p²} = p^{k−1}⟨p⟩^{±1}`, but that step is not written in Lean. Shimura
and Diamond–Shurman both use `diag(1, p)` (recalled, UNVERIFIED).

### 4.2 `CoeffFieldFinite.Gamma1IntegralSpan` (coeff-field; main route)

`S_k(Γ₁(N))` (`k ≥ 2`) is spanned over `ℂ` by forms with integral `q`-expansions. **LEAF, printed form:** Shimura
1971 Thm 3.52 (a basis spans). coeff-field §2.1 has the rating.

### 4.3 `CoeffRational.RationalHeckeSpan` (one-leaf alternative)

```lean
def RationalHeckeSpan : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ), 2 ≤ k →
    Submodule.span ℂ {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k |
      (∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff n = q) ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ∃ q : ℚ,
        (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)).coeff n = q} = ⊤
```

This is the common weakening of both `Γ₁(N)` pairs (`rationalHeckeSpan_of_heckePrime`,
`rationalHeckeSpan_of_diamond`). **Composite.** It is a consequence of "`S_k(Γ₁(N)) = ℂ ⊗ S_k(Γ₁(N), ℤ)` and
`S_k(Γ₁(N), ℤ)` is `T_n`-stable". It counts as printed form only if one statement prints both halves; candidates
are Diamond–Im §12.3–12.4 and Shimura's Thm 3.52 with §3.5. With it the count is unchanged (dry run 16/21 → 16/21,
`scratch/coeff-rational/autofold-oneleaf.json`). It is offered in case the integrator prefers not to add a leaf.
It is not the recommended fold.

## 5. The glue (all proved, `CoeffRational.lean`)

1. **Diamond from `T_p`** (`isRatForm_diamond`). If `g` and every `T_p g` (`p ∤ N` prime) have rational
   coefficients, then so does every `⟨d⟩ g`:
   * choose a prime `p > N` with `p ≡ d (mod N)` (Dirichlet, Mathlib's `Nat.forall_exists_prime_gt_and_eq_mod`);
   * then `⟨d⟩ = ⟨p⟩` (`diamondOpCuspNat_of_coprime`, `ZMod.unitOfCoprime p _ = d`);
   * the recurrence at `m = pn` gives `a_n(⟨p⟩ g) = p^{1−k}(a_{pn}(T_p g) − a_{p²n}(g))`.
2. **`T_p` from the diamond operators** (`isRatForm_hecke`): the same recurrence, read the other way. This proves
   that coeff-field's pair implies `RationalHeckeSpan`.
3. **The `ℚ(χ)`-structure** (`charSpaceRationalSpan_of_rationalHeckeSpan`). This is coeff-field's `χ`-projector
   argument, with the diamond rationality coming from (1) on the spanning set. Then coeff-field's
   `eigenformCoeffFieldFinite_of` finishes: Hecke stability on `S_k(N, χ)`, `a_n = λ_n`, and the abstract
   eigenvalue lemma.

## 6. Checks

* `lake env lean ZInQKernel/Contrib/OneProof/CoeffRational.lean`: compiles with no warnings.
  `lake build ZInQKernel.Contrib.OneProof.CoeffRational` succeeds. A copy is at
  `scratch/coeff-rational/CoeffRational.lean`; the development file `HeckePrime.lean`, with `#print axioms`,
  compiles too.
* `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` succeeds (14101 jobs; build tree copied
  from leaf-fold33b, only Main rebuilt). `ZInQ.OneProof.frozenTarget` uses the standard axioms.
* `#discharges` (`scratch/coeff-rational/DischargesRun.lean`): the output is in §1.
* **Autofold** (`scratch/coeff-rational/autofold.json`):
  `eigenformCoeffFieldFinite := CoeffRational.eigenformCoeffFieldFinite_of_heckePrime {n}.gamma1IntegralSpan {n}.heckePrimeIntegralToRational`.
  Both leaves are kind published, flag "unread: new printed leaf …; locator UNVERIFIED". The dry run
  (`autofold-dryrun.txt`) gives strict 16/21 on 37 → 18/20 on 38, and the same for strictest. The generated
  module, with line 1 stripped (`FoldCheck.lean`), compiles: `HDec.HSyn.sixContactMin_of_open39` uses only the
  standard axioms.
* No numerical check was run; none applies, since no explicit level or weight is involved.

## 7. For the integrator

* Fold with `python3 scripts/one_proof/autofold.py scratch/coeff-rational/autofold.json`. It needs coeff-field's
  `EigenformCoeffFieldFinite.lean`, which is on this branch. The spec supersedes coeff-field's
  `scratch/coeff-field/autofold.json`, which targeted the older field `dsThm965Weak` and used the diamond leaf. On
  top of leaf-fold33 (TailZ46), the generated module number and top theorem shift; the script computes them.
* Proposed locators.md rows (unread):
  * `gamma1IntegralSpan`: Shimura 1971, Thm 3.52 (integral basis of `S_k(Γ₁(N))`).
  * `heckePrimeIntegralToRational`: the `T_p` (`p ∤ N`) part of "the `T_n` preserve `S_k(Γ₁(N), ℤ)`": Shimura 1971
    §3.5; Diamond–Im 1995 §12.3–12.4; Diamond–Shurman §6.5 for `k = 2`.
* `DiamondIntegralToRational` is no longer needed by any route. It remains provable from the new leaf
  (`diamondIntegralToRational_of_heckePrime`).

## 8. What remains

* Page checks (no network): Shimura 1971 Thm 3.52 and §3.5, and Diamond–Im §12.3–12.4. The questions are whether
  the integral basis covers `S_k(Γ₁(N))` for every `k ≥ 2`, and the `T_p` convention (the double coset of
  `diag(1, p)`). If one statement prints both the integral basis and its Hecke stability, `RationalHeckeSpan` is
  printed form and the one-leaf fold also gives GLUE −1.
* An outright proof needs the `q`-expansion principle or Eichler–Shimura over `ℤ`, and neither is in any library.
