# carirr-odd: the oddness and irreducibility steps of Carayol's leaf, proved in Lean

Task carirr-odd, branch `wip/carirr-odd`. Base: wip/r17-rebase 4095ce12, with origin/main e1b31749 and
origin/wip/carayol-herbrand 59f16e5e merged, no conflicts. 2026-11-17.

Marks:

* **VERIFIED**: compiled, or read in the named file;
* **STANDARD**: published, with a reference;
* **SPECULATIVE**.

Theorem and clause numbers given from memory are marked **UNVERIFIED** (no network). The reviewer's verdict
(`crowd-kit/ckpt/leaf-review/queue10-verdict.md`, carIrr) is not in this tree or in any `origin/*` ref. I worked
from the brief's summary of it: every clause is printed in DDT 1997 Thm 3.1 (a)–(d), with "absolutely
irreducible" as 3.1(c).

## 0. Result

**Both open Lean steps are now proved, and the leaf is stated with DDT 3.1's clauses.** All VERIFIED (compiled,
standard axioms):

1. **`χ_ℓ(c) = −1`.** Complex conjugation is an involution of `ℚ̄` that inverts every root of unity
   (`exists_complexConj`). Mathlib's `ℓ`-adic cyclotomic character of `G_ℚ` takes the value `−1` on it
   (`cycL_eq_neg_one`), and the mod-`N` cyclotomic character takes the value `−1 ∈ (ℤ/N)ˣ`
   (`cycN_eq_neg_one`).
2. **Oddness from `det ρ = ψ·χ_ℓ`.** The nebentypus of a weight-2 newform is even (`chi_neg_one_eq_one`, from
   Tau Ceti's parity lemma). So the determinant clause gives `det ρ(c) = ψ(−1)·χ_ℓ(c) = −1` with `c² = 1`
   (`odd_of_det`).
3. **Irreducibility, transcribing 3.1(c).** The leaf now says **absolutely irreducible**: irreducible after
   extension of scalars to `AlgebraicClosure K_{f,λ}`. Irreducibility over `K_{f,λ}` follows
   (`irreducible_of_absIrreducible`, for any field extension and any dimension). Burnside's form then comes from
   r17-rebase's `adjoin_eq_top_of_irreducible_odd` (glue, already proved).

**New leaf, `CarayolDDT.CarayolDDT31`** (in `ZInQKernel/Contrib/OneProof/CarayolDDTOdd.lean`). It has five
clauses:

* continuous;
* absolutely irreducible;
* `det ρ = ψ(σ mod N)·χ_ℓ(σ)`;
* unramified at `p ∤ Nℓ` with arithmetic-Frobenius trace `a_p`;
* conductor in DDT's integral form (carayol-herbrand's clause).

It no longer has an "odd" clause or a plain-irreducibility clause. Main's open field `carayolThmA` is then
discharged by

`carayolThmA_of_DDT31 : CarayolDDT31 → CarayolPrinted.CarayolThmA`.

It runs `CarayolDDT31 → CarayolThmAIrrDDT` (this task) `→ CarayolThmAIrr` (carayol-herbrand, Herbrand) `→
CarayolThmA` (r17-rebase, Burnside). A variant `CarayolDDT31Cond` states the conductor as `condExp`;
`carayolDDT31_iff_cond` proves the two variants equivalent.

* **`#discharges` against main** (TailZ62, `OpenResearchLeaves38`): `DISCHARGES [OpenResearchLeaves38.carayolThmA] by
  CarayolDDT.carayolThmA_of_DDT31`, still assuming `[CarayolDDT.CarayolDDT31]`, with axioms `[propext,
  Classical.choice, Quot.sound]` (§3).
* **Fold dry run**, on main's `kinds.tsv`: `strict count: 16/18 on 34 -> 17/17 on 34; strictest 16/18 -> 17/17`,
  so **GLUE −1** for `carayolThmA` (now `consequence`, GLUE/GLUE), with the leaf flagged `unread`.

## 1. The Lean (VERIFIED: `lake build ZInQKernel.Contrib.OneProof.CarayolDDTOdd`, no warnings; axioms `[propext, Classical.choice, Quot.sound]` for all 13 declarations, `scratch/carirr-odd/axioms.txt`)

| declaration | statement | proof |
| --- | --- | --- |
| `cycN N : GQ →* (ZMod N)ˣ` | mod-`N` cyclotomic character, `σ ζ = ζ^{cycN σ}` for `ζ^N = 1` | Mathlib's `modularCyclotomicCharacter Qbar` composed with `MulSemiringAction.toRingAut`, card via `HasEnoughRootsOfUnity` of `AlgebraicClosure ℚ` |
| `cycL ℓ : GQ →* ℤ_[ℓ]ˣ` | `ℓ`-adic cyclotomic character | Mathlib's `cyclotomicCharacter Qbar ℓ` |
| `exists_complexConj` | `∃ c : GQ, c * c = 1 ∧ ∀ n t, t^n = 1 → n ≠ 0 → c t * t = 1` | fix `ι : ℚ̄ → ℂ` (`IsAlgClosed.lift`). `conj ∘ ι` lands in `ι(ℚ̄)` (algebraic elements, `DSCoeffExt.mem_fieldRange_of_isIntegral`), so it factors as `ι ∘ c`. Then `c ∘ c = id`, since `ι` is injective and `conj` is an involution. `|ι ζ| = 1` gives `conj(ι ζ)·ι ζ = 1` |
| `cycL_eq_neg_one` | **`χ_ℓ(c) = −1`** for any `c` inverting roots of unity | Tau Ceti's `cyclotomicCharacter_eq_neg_one` (`toZModPow` at every level) |
| `cycN_eq_neg_one` | `cycN N c = −1` | `modularCyclotomicCharacter.unique` with `c = −1 : ZMod N`; `t^{val(−1)+1} = 1` since `ord t ∣ N` |
| `chi_neg_one_eq_one` | `f.χ(−1) = 1` for `f : Newform N 2` | Tau Ceti's `char_neg_one_of_mem_cuspFormCharSpace` (`χ(−1) = (−1)^k`), with `k = 2` |
| `odd_of_det` | the determinant clause and `ψ(−1) = 1` give `∃ c, c² = 1 ∧ det ρ(c) = −1` | at `c`: `ψ(cycN c) = ψ(−1) = 1 ∈ K` and `ι(χ_ℓ(c)) = ι(−1) = −1` |
| `irreducible_of_absIrreducible` | irreducible over `L ⊇ K` ⇒ irreducible over `K` (any `n`) | a proper nonzero stable `W` gives `W' = span_L(W)`, stable. It is nonzero, and it lies in the kernel of the base change of a nonzero functional vanishing on `W` (`Submodule.exists_le_ker_of_lt_top`), so it is proper |
| `padicInt_ringHom_ext` | two continuous ring homs `ℤ_ℓ → R` (`R` Hausdorff) are equal | `ℤ` is dense in `ℤ_ℓ` (`PadicInt.denseRange_intCast`) |
| `CarayolDDT31`, `CarayolDDT31Cond` | the leaf (§2), conductor in DDT's form or as `condExp` | definitions |
| `carayolThmAIrrDDT_of_DDT31` | `CarayolDDT31 → CarayolHerbrand.CarayolThmAIrrDDT` | the lemmas above, at each `(N, f, ℓ, λ)` |
| `carayolThmAIrr_of_DDT31Cond` | `CarayolDDT31Cond → CarayolPrinted.CarayolThmAIrr` | same |
| `carayolDDT31_iff_cond` | `CarayolDDT31 ↔ CarayolDDT31Cond` | `CarayolHerbrand.condExp_decomp_eq_ddt` |
| `carayolThmA_of_DDT31`, `carayolThmA_of_DDT31Cond` | the leaf ⇒ main's field `CarayolPrinted.CarayolThmA` | the chain above, then `carayolThmA_of_irr` (Burnside step) |
| `carayolR17'_of_DDT31` | `CarayolDDT31 → EigenformCoeffFieldFinite → LadicCond.CarayolR17'` | `carayolR17'_of_printed` |

## 2. The leaf and its rating against the print

`CarayolDDT31` covers every Tau Ceti `Newform N 2` `f` (nebentypus `ψ = f.χ : (ℤ/N)ˣ → ℂˣ`) for which
`K_f = ℚ(a_n) ⊆ ℂ` is a number field, every prime `ℓ` and every place `λ ∣ ℓ` of `K_f`. For each, it asserts a
continuous `ρ : G_ℚ →* GL₂(K_{f,λ})` with the clauses below.

| clause | Lean | printed? | rating |
| --- | --- | --- | --- |
| existence, continuity | `∃ ρ, Continuous ρ` | DDT 3.1 (Shimura 1971 Thm 7.14, Deligne 1971; UNVERIFIED) | printed form |
| **absolutely irreducible** | every `ρ(G_ℚ)`-stable `K̄`-subspace of `K̄²` is `⊥` or `⊤`, with `K̄ = AlgebraicClosure K_{f,λ}` and `ρ` extended along `algebraMap` | DDT 3.1(c) per the verdict (Ribet 1977; UNVERIFIED) | **printed form**: "absolutely irreducible" means irreducible over an algebraic closure, transcribed literally |
| **`det ρ = ψ χ_ℓ^{k−1}`, `k = 2`** | `∃ ι : ℤ_ℓ →+* K_{f,λ}` continuous with `det ρ(σ) = ψ(cycN σ)·ι(cycL σ)` at every `σ` with `ψ(cycN σ) ∈ K_f` | DDT 3.1 per the verdict (Deligne 1971; UNVERIFIED) | **printed form, never stronger** (see the notes below) |
| unramified at `p ∤ Nℓ`, `tr ρ(Frob_p) = a_p` (arithmetic Frobenius) | unchanged from r17-print | DDT 3.1 (Eichler–Shimura, Shimura 7.14) | printed form (as rated before) |
| conductor at `p ≠ ℓ` | `codim V^{I_p} + ∫₀^∞ codim V^{G_p^u} du = v_p(N)` (carayol-herbrand) | DDT 3.1 with DDT §2's conductor (carayol-herbrand's reading; UNVERIFIED) | carayol-herbrand's rating, unchanged |
| ~~odd~~ | removed from the leaf | derived in the sources from `det` | **proved** (`odd_of_det`) |
| ~~irreducible over `K_{f,λ}`~~ | removed from the leaf | a consequence of 3.1(c) | **proved** (`irreducible_of_absIrreducible`) |

Notes on the determinant clause:

* **The embedding `ι`.** `ℤ_ℓ → K_{f,λ}` is quantified existentially. Any continuous ring hom `ℤ_ℓ → K_{f,λ}` is
  the canonical one (`padicInt_ringHom_ext`, VERIFIED). So the `∃` names the print's embedding and adds nothing.
  Its existence is STANDARD (`K_{f,λ}` is a finite extension of `ℚ_ℓ`). Lean has no ready-made `ℚ_ℓ → K_{f,λ}`
  for Mathlib's `adicCompletion`. That is why the leaf asserts `ι` instead of naming it.
* **Restriction to `σ` with `ψ(σ mod N) ∈ K_f`.** The values of `ψ` lie in `ℚ(a_n)` (STANDARD: for `p ∤ N`,
  `a_{p²} = a_p² − ψ(p)p`, and Dirichlet's theorem puts a prime in every class; Shimura 1971 §3.5, UNVERIFIED
  locator). So the restriction removes no `σ`. It lets the leaf state the print's identity without also asserting
  that membership. The restricted clause is implied by the unrestricted one, so it is a consequence of the print.
  It is not vacuous: at complex conjugation the value is `ψ(−1) = 1 ∈ K_f`, and that is the only value the proof
  uses.
* **Normalization.** The clause says that arithmetic Frobenius has `det = ψ(p)·p`, since `χ_ℓ(Frob_p) = p` and
  `cycN(Frob_p) = p`. The leaf also says that arithmetic Frobenius has trace `a_p`. With characteristic polynomial
  `X² − a_pX + ψ(p)p` (the Diamond–Shurman normalization of `T_p`, which Tau Ceti uses), the two clauses agree:
  they describe the dual of Deligne's `H¹` representation. Oddness uses only `ψ(−1) = 1`, which holds for `ψ` and
  for `ψ⁻¹` alike. So a different reading of the normalization would change neither the proof nor the count.
  The statement check should still confirm DDT's convention (§5).

**Verdict.** `CarayolDDT31` is DDT 1997 Thm 3.1 for weight 2, clause by clause, with:

* the irreducibility clause in the printed absolute form;
* the determinant identity in place of oddness;
* the conductor in DDT's integral form (carayol-herbrand).

It is the published statement or a consequence of it, never stronger: the `det` clause is restricted as
explained above, and only the listed properties of one `ρ` are asserted. It is stated over Mathlib and Tau Ceti
definitions only. Rating: **published, printed form**. Kind `published`, flag `unread` (a new printed leaf, as
the kit prescribes), with the clause-level items for the statement check in the flag.

## 3. `#discharges` (VERIFIED, `scratch/carirr-odd/discharges.txt`)

Build: `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.CarayolDDTOdd` succeeded with 14276 jobs (`build-main.txt`). It reports
`frozenTarget` on the standard axioms. Then:

```
DISCHARGES [OpenResearchLeaves38.carayolThmA] by CarayolDDT.carayolThmA_of_DDT31
  still assumes: [CarayolDDT.CarayolDDT31]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves38.carayolThmA] by CarayolDDT.carayolThmA_of_DDT31Cond
  still assumes: [CarayolDDT.CarayolDDT31Cond]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves38.carayolThmA] by CarayolPrinted.carayolThmA_of_irr
  still assumes: [CarayolPrinted.CarayolThmAIrr]
  axioms: [propext, Classical.choice, Quot.sound]
```

The remaining lines of the output concern other tasks' contributions already on main.

## 4. The fold

`scratch/carirr-odd/autofold.json` replaces field `carayolThmA` by leaf `carayolDDT31 :
_root_.CarayolDDT.CarayolDDT31`:

* kind `published`;
* flag `unread: new printed leaf (DDT 1997 Thm 3.1, weight 2; …) …; statement check: det rho = psi chi_l^{k-1} with
  the arithmetic-Frobenius normalization …, the conductor as DDT's integral …; locators UNVERIFIED`;
* proof `_root_.CarayolDDT.carayolThmA_of_DDT31 {n}.carayolDDT31`.

Dry runs on main's `kinds.tsv`, both VERIFIED (`autofold-dryrun.txt`, `autofold-cond-dryrun.txt`):

| spec | leaf | strict | strictest | module |
| --- | --- | --- | --- | --- |
| `autofold.json` (recommended, needs carayol-herbrand's `CarayolHerbrand.lean`) | `carayolDDT31` (published, unread) | 16/18 on 34 → **17/17 on 34** | 16/18 → **17/17** | compiles: `sixContactMin_of_open56` on the standard axioms (`AutofoldDryRun.lean`, `autofold-dryrun-compile.txt`) |
| `autofold-cond.json` (conductor as `condExp`) | `carayolDDT31Cond` (published, unread) | 16/18 → 17/17 | 16/18 → 17/17 | (same shape) |

The recommended spec makes `carayolThmA` a direct instance of DDT 3.1, which gives the target **GLUE −1**. It
imports `CarayolDDTOdd`, which imports carayol-herbrand's `CarayolHerbrand.lean`, so the integrator folds both
branches together. carayol-herbrand's own spec targets `r17`, a field that main has since replaced by
`carayolThmA`. This spec supersedes it on current main.

Fold recipe:

1. `git merge origin/wip/carirr-odd`. This brings `CarayolHerbrand.lean` (carayol-herbrand) and `CarayolDDTOdd.lean`.
2. `python3 scripts/one_proof/autofold.py scratch/carirr-odd/autofold.json`.
3. Run the usual checks: build `+ZInQKernel.OneProof.Main`, axioms of `frozenTarget`, `DumpCompact` +
   `cmp_hashes.py`, `OpenStatements`, `render_open.py --check`.
4. Add a `locators.md` row: `R17 (DDT form, carirr-odd) | Darmon–Diamond–Taylor 1997 Thm 3.1 (a)–(d), §2
   (conductor); Shimura 1971 Thm 7.14; Deligne 1971; Ribet 1977; Carayol 1986 (A) + Casselman 1973 | — | UNVERIFIED
   | ρ_{f,λ} over K_{f,λ}: absolutely irreducible, det = ψχ_ℓ, traces a_p (arithmetic Frobenius), DDT conductor
   = v_p(N) at p ≠ ℓ`.

## 5. What remains

* **Statement check (reading), DDT 1997 Thm 3.1:**
  1. Is "absolutely irreducible" printed (3.1(c) per the verdict)?
  2. Is `det ρ_{f,λ} = ψ ε^{k−1}` printed, with `ε` the `ℓ`-adic cyclotomic character, and with which Frobenius
     convention for `tr = a_p`?
  3. The conductor clause (carayol-herbrand's item).

  These decide whether the `unread` flag clears. If (2) prints geometric Frobenius, the leaf's trace clause (from
  r17-print) would read the dual representation. Oddness is unaffected.
* The fold itself (integrator).
* `EigenformCoeffFieldFinite` is used only by `carayolR17'_of_DDT31`, not by the discharge of `carayolThmA`.

## 6. Files

* `ZInQKernel/Contrib/OneProof/CarayolDDTOdd.lean` (new).
* `scratch/carirr-odd/`:
  * `Odd1.lean` (the first compiled draft of the lemmas);
  * `Axioms.lean`, `axioms.txt`;
  * `Discharges.lean`, `discharges.txt`, `build-main.txt`;
  * `autofold.json`, `autofold-cond.json` and their dry runs, `AutofoldDryRun.lean` and its compile output;
  * `log.md`.
