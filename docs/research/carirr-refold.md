# carirr-refold: the research row `carayolThmAIrr` re-folded onto the manuscript's Carayol locator

Task carirr-refold, branch `wip/carirr-refold`. Base: wip/leaf-fold33b at bf691da22 (top `sixContactMin_of_open67`,
TailZ74). origin/wip/carirr-odd (7b1ca2c16) is merged in, with no conflicts. 2026-11-17.

Marks:

* **VERIFIED**: compiled, or read in the named file;
* **STANDARD**: published, with a reference;
* **SPECULATIVE**.

Theorem numbers given from memory are marked **UNVERIFIED** (no network).

## Issues for the lead (read first)

1. **Route: the H proof uses Carayol's theorem without citing it, and the project imports a citation that the
   manuscript makes for a different application. The argument is not changed.** VERIFIED (read).
   * **Where the H proof needs it.** The consumer of `carayolThmAIrr` is step D5 ("level ≤ conductor", h-trust.md D5).
     The chain is `carayolThmAIrr → carayolThmA` (Burnside's form) `→ r17 : LadicCond.CarayolR17'` `→`
     `G0ModNewform.NewformLeaves` (TailD.lean L149) `→` D5. In the manuscript, D5 is diophantine_zq.tex L852-857:
     "Local–global compatibility for the weight-two modular representation therefore bounds the primitive level
     `N`". The sentence has **no citation**.
   * **What D5 applies it to.** It is applied to `r_5` at every `p ≠ 5` and to `r_3` at `p = 5` (L790-794). So the
     coefficient places lie above 5 and above 3, and `p` ranges over all primes `≠ ℓ`, including `p = 2` and `p | N`.
   * **Where the manuscript does cite Carayol.** Its only Carayol citation is L9778, in the appendix subsection
     "Integer divisions and actual trace operators" (from L9446), which serves Theorem 5.3. There Carayol is applied to
     `Π_f^∨`, with a coefficient place above 2 and odd `p`.
   * **What the project does.** h-trust.md D5 imports the L9778 locator into D5. The locator audit
     (locators.md, row R17) read Théorème (A) as covering every `p ≠ ℓ` and every `ℓ`. So D5 uses Carayol where the
     manuscript gives no reference, not where it argues otherwise. **No route deviation.** The citation gap is the
     manuscript's.
   * **Casselman is also uncited at D5.** "Bounds the primitive level" needs Casselman's `a(π_{f,p}) = v_p(N)` as well
     as Carayol. The manuscript cites Casselman only at L9802-9806, also in the appendix.
   * **Direction.** D5 needs only `v_p(N) ≤` the conductor exponent. CarayolLevel.lean's `CarayolLevelLe` records this;
     the field asserts equality.
2. **Carayol's Théorème (A), in the form the manuscript's locator gives, cannot be stated in Lean today. The
   conductor clause therefore stays in packaged form.** VERIFIED (searched Mathlib, Tau Ceti and ZInQKernel; §2).
   * **Carayol's form.** Carayol's statement is local–global compatibility: `σ_λ(π)|_{G_{ℚ_p}}` corresponds to `π_p`
     under the local Langlands correspondence, in his normalization.
   * **What Lean lacks.** Stating it needs the local components `π_{f,p}` of a newform (adelic lift), the
     Weil–Deligne representation of an `ℓ`-adic representation of `G_{ℚ_p}`, and the local Langlands correspondence
     for `GL₂(ℚ_p)`. None exists in Lean: no Weil–Deligne, local-Langlands or automorphic-representation definitions
     in Mathlib v4.35, Tau Ceti or ZInQKernel.
   * **Casselman's Theorem 1 as a separate leaf** could be stated over smooth representations of `GL₂(ℚ_p)`, but its
     input `π_{f,p}` could not be supplied, so it would be inert.
   * **Consequence.** The conductor equality stays a consequence of three prints: Carayol A, the conductor
     compatibility of local Langlands, and Casselman Thm 1. Of these, only DDT 1997 Thm 3.1 prints it as one statement
     ("`N(ρ)` is the prime-to-`ℓ` part of `N`", an AI reading, kinds row). The manuscript does not cite DDT.
3. **The unramified clause can be put in Carayol's normalization as the manuscript reads it, and it now is.**
   VERIFIED (read and compiled).
   * L9784-9796 derives from Carayol's normalization that arithmetic Frobenius on `ρ_f` has "good polynomial
     `X² − a_q X + q χ(q)`". Here reciprocity sends geometric Frobenius to a uniformizer, `ω_p = |·|_p`, and
     `ρ_f = σ(Π_f^∨)^∨`.
   * The new leaf `CarayolThmAFrob` has exactly this per-Frobenius clause (trace `a_p`, determinant `p ψ(p)`). It
     replaces carirr-odd's global `det ρ = ψ χ_ℓ`.
   * So the normalization item of carirr-odd's statement check (arithmetic Frobenius, `det ψ(p) p`) is settled by the
     manuscript's own reading of Carayol. No normalization mismatch: the conductor does not change under the
     contragredient or a twist by a finite-order character.
4. **Irreducibility is not in Carayol.** It is Ribet, LNM 601 (1977), Thm 2.3 (UNVERIFIED locator), or DDT 3.1(c)
   ("absolutely irreducible"). The new leaf asks only for irreducibility over `K_{f,λ}`, which is weaker than either.

## 0. Result

**`carayolThmAIrr` is discharged by a weaker leaf, `CarayolRefold.CarayolThmAFrob`.** Its unramified clause is in the
manuscript's Carayol normalization. Its oddness is proved instead of assumed, and it is implied by carirr-odd's DDT 3.1
transcription. **The conductor clause cannot be put on Carayol's locator in Lean** (issue 2), so the leaf stays a
packaged consequence of DDT 3.1. All VERIFIED (compiled, standard axioms):

* `CarayolRefold.odd_of_frobDet` (new): oddness from the determinant at Frobenius elements. Let `ρ : G_ℚ → GL₂(E)` be
  continuous, with `E` ultrametric, `‖ℓ‖ < 1` and `2 ≠ 0`. Suppose `det ρ(σ) = p` at every arithmetic Frobenius
  `σ` above a prime `p ∤ Nℓ` with `σ mod N = −1`. Then complex conjugation `c` has `det ρ(c) = −1`.
* `CarayolRefold.carayolThmAIrr_of_frob : CarayolThmAFrob → CarayolPrinted.CarayolThmAIrr`, the discharge.
* `CarayolRefold.frob_of_DDT31 : CarayolDDT.CarayolDDT31 → CarayolThmAFrob`, so the new leaf is not stronger than DDT
  3.1. Also `carayolThmAIrr_of_DDT31`, and `carayolR17'_of_frob`, which gives `r17` with `EigenformCoeffFieldFinite`.
* `#discharges` against this base (TailZ74, `OpenResearchLeaves48`): see §3.
* **Fold dry run** (`autofold.py --dry-run`): `strict count: 4/27 on 31 -> 4/27 on 31; strictest 4/27 -> 4/27`. The
  fold is **count-neutral now**: the new leaf enters flagged `unread` and counts GLUE (ruling 2026-11-17). It becomes
  **GLUE −1** once a reader checks the leaf against the page.

## 1. The Lean: `ZInQKernel/Contrib/OneProof/CarayolRefold.lean`

It imports `ZInQKernel.Contrib.OneProof.CarayolDDTOdd` (carirr-odd), which imports the module that defines
`CarayolPrinted.CarayolThmAIrr`. It has no `sorry` and no `axiom`, and `lake env lean` gives no warnings.

| declaration | statement | proof |
| --- | --- | --- |
| `isOpen_ker_cycN M` | `ker(σ ↦ σ mod M)` is open in `G_ℚ` | it contains `Gal(ℚ̄/ℚ(ζ_M))`, which is open (`IntermediateField.fixingSubgroup_isOpen`); `Subgroup.isOpen_mono` |
| `cycN_arithFrob` | an arithmetic Frobenius at `v ∣ p`, `p ∤ M`, has `σ mod M = p` | hodge-split's `arithFrob_pow_of_rootOfUnity` (`σζ = ζ^p` on roots of unity of order prime to `p`) |
| `cycL_arithFrob` | `χ_ℓ(Frob_p) = p` for `p ≠ ℓ` | hodge-split's `cyc_arithFrob`; `toRingAut σ = σ.toRingEquiv` |
| `nearOne d r` | `{σ : ‖d(σ) − 1‖ < r}` is a subgroup for a character `d` and `0 < r ≤ 1` | ultrametric inequality; `‖x‖ = 1` when `‖x − 1‖ < 1` |
| **`odd_of_frobDet`** | see §0 | below |
| `CarayolThmAFrob` | the leaf (§2) | definition |
| `carayolThmAIrrDDT_of_frob` | `CarayolThmAFrob → CarayolHerbrand.CarayolThmAIrrDDT` | `odd_of_frobDet` with `u = −1`, `b = p` and `ψ(−1) = 1` (`CarayolDDT.chi_neg_one_eq_one`) |
| `carayolThmAIrr_of_frob` | `CarayolThmAFrob → CarayolPrinted.CarayolThmAIrr` | with carayol-herbrand's `carayolThmAIrr_of_DDT` (Herbrand) |
| `frob_of_DDT31` | `CarayolDDT31 → CarayolThmAFrob` | absolutely irreducible gives irreducible (carirr-odd). At a Frobenius, `cycN σ = u` and `ψ(u) = b/p ∈ K_f`, so DDT's `det = ψ(cycN σ)·ι(χ_ℓ σ) = ψ(u)·p = b` |
| `carayolThmAIrr_of_DDT31`, `carayolR17'_of_frob` | compositions | — |

**Proof of `odd_of_frobDet`.** The proof needs no `ℓ`-adic cyclotomic character in `E` and no embedding `ℤ_ℓ → E`;
the hypothesis is used at a single Frobenius element.

1. Take complex conjugation `c` (`CarayolDDT.exists_complexConj`). It has `c mod M = −1` for every `M`.
2. Let `d = det ρ` and `r = ‖2‖ ∈ (0, 1]`, and choose `k` with `‖ℓ‖^k < r`.
3. Let `U` be the open subgroup `ker(mod N) ∩ ker(mod ℓ^k) ∩ {‖d − 1‖ < r}`.
4. Chebotarev density (the kernel's T18, `CarayolLevel.frobeniusDense_C9`) gives an arithmetic Frobenius `τ` above
   some `p ∤ Nℓ` with `τ⁻¹c ∈ U`. Then:
   * `τ mod N = −1`, so `d(τ) = p` by the hypothesis;
   * `p ≡ −1 (mod ℓ^k)`, so `‖p + 1‖ ≤ ‖ℓ‖^k < r`.
5. Suppose `d(c) = 1`. Then `d(τ⁻¹c) = p⁻¹`, so `‖p − 1‖ = ‖p⁻¹ − 1‖ < r`, and then
   `‖2‖ ≤ max(‖p + 1‖, ‖p − 1‖) < ‖2‖`, a contradiction.
6. Since `d(c)² = 1`, it follows that `d(c) = −1`.

This is glue: the manuscript proves oddness differently (Betti comparison, L742-751), and in the sources oddness
comes from `det = ψχ_ℓ`. It is a short Chebotarev argument over printed inputs, proved in Lean, and nothing else is
built on it.

## 2. The leaf and its rating

`CarayolThmAFrob` quantifies over the following data:

* every Tau Ceti `Newform N 2` `f`, with nebentypus `ψ = f.χ`;
* such that `K_f = ℚ(a_n) ⊆ ℂ` is a number field;
* every prime `ℓ` and every place `λ ∣ ℓ` of `K_f`.

For each, it asserts a continuous `ρ : G_ℚ →* GL₂(K_{f,λ})` with the clauses below.

| clause | Lean | source | rating |
| --- | --- | --- | --- |
| existence, continuity | `∃ ρ, Continuous ρ` | Shimura 1971 Thm 7.14, Deligne 1971, Carayol 1986 Théorème (A) (UNVERIFIED) | printed |
| irreducible over `K_{f,λ}` | no stable subspace other than `⊥`, `⊤` | Ribet 1977 Thm 2.3 (UNVERIFIED); weaker than DDT 3.1(c) "absolutely irreducible" | printed or weaker (proved from 3.1(c), `irreducible_of_absIrreducible`) |
| unramified at `p ∤ Nℓ` | trivial on every inertia group above `p` | Shimura 7.14 / Carayol A at unramified `p` | printed |
| **Frobenius polynomial `X² − a_p X + p ψ(p)`** | at every arithmetic Frobenius: trace `= a_p`, and `det = b` for every `b ∈ K_f` and unit `u ≡ p (mod N)` with `b = p ψ(u)` in `ℂ` | **manuscript L9784-9796** (Carayol's normalization); DS Thm 9.6.5; DDT 3.1 | **printed form, in the manuscript's normalization**. The `∀ b` quantifier adds nothing: `b` is unique, and when `ψ(p) ∉ K_f` the clause is vacuous, hence weaker. It is not vacuous where the proof uses it: at `p ≡ −1 (mod N)`, `b = p ∈ K_f` |
| conductor at `p ≠ ℓ` | `codim V^{I_p} + ∫₀^∞ codim V^{G_p^u} du = v_p(N)` (DDT's form, as in carirr-odd's leaf) | Carayol A + conductor compatibility of local Langlands + Casselman 1973 Thm 1; one statement in DDT 3.1 (AI reading, #65) | **consequence of three prints, printed packaged only in DDT 3.1**, as before. Not in Carayol's form (issue 2) |
| ~~odd~~ | removed | — | **proved** (`odd_of_frobDet`) |

**Verdict.** `CarayolThmAFrob` is a consequence of DDT 1997 Thm 3.1. The implication `CarayolDDT31 → CarayolThmAFrob`
is proved in Lean, and carirr-odd rated `CarayolDDT31` as DDT 3.1's printed form. The unramified clause is the form the
manuscript itself takes from Carayol, and oddness is no longer assumed. **Printed form? Partly:**

* the Frobenius clause is printed (manuscript L9794 and DS 9.6.5);
* irreducibility is printed (Ribet);
* the conductor clause is a composite of Carayol, local Langlands and Casselman, printed as one statement only in
  DDT 3.1.

Kind `published`, flag `unread` (a new leaf), with the conductor packaging named in the flag.

**Why the target "carayolThmAIrr on the manuscript's Carayol locator" is not reached.** Carayol's Théorème (A) at a
ramified `p` is a statement about the local Langlands correspondence. Lean has no `π_{f,p}`, no Weil–Deligne
representations and no local Langlands correspondence (issue 2). Any Lean "Carayol leaf" for the conductor would
either:

* be stated over abstract structures invented for the purpose, which the rules forbid; or
* be the composite conductor clause itself (Carayol ∘ local Langlands ∘ Casselman), which is what both carirr-odd's
  leaf and this one state.

Casselman's Theorem 1 is expressible locally but has nothing to attach to. I therefore keep DDT 3.1's packaging for the
conductor clause only, as the brief allows when the Carayol form cannot express the step. The other clauses no longer
depend on DDT: the Frobenius clause uses the manuscript's Carayol reading, irreducibility uses Ribet, and oddness is
proved.

## 3. `#discharges` (VERIFIED, `scratch/carirr-refold/discharges.txt`)

The build `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.CarayolRefold` succeeded with 16218 jobs (`build-main.txt`) and reports `frozenTarget` on
the standard axioms. Then `lake env lean scratch/carirr-refold/Discharges.lean` printed:

```
DISCHARGES [OpenResearchLeaves48.carayolThmAIrr] by CarayolRefold.carayolThmAIrr_of_DDT31
  still assumes: [CarayolDDT.CarayolDDT31]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves48.carayolThmAIrr] by CarayolRefold.carayolThmAIrr_of_frob
  still assumes: [CarayolRefold.CarayolThmAFrob]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 36 open hypotheses, 15810 theorems checked, 23 discharge one
```

The other lines are earlier contributions: carirr-odd's `carayolThmAIrr_of_DDT31Cond`, carayol-herbrand,
r17-rebase's split, and other fields. Every declaration of `CarayolRefold` is on `[propext, Classical.choice,
Quot.sound]` (`axioms.txt`).

## 4. The fold and the kinds rows

`scratch/carirr-refold/autofold.json` removes field `carayolThmAIrr`, with proof
`_root_.CarayolRefold.carayolThmAIrr_of_frob {n}.carayolThmAFrob`, and adds the leaf
`carayolThmAFrob : _root_.CarayolRefold.CarayolThmAFrob` (kind `published`, flag `unread: …`).

* **Dry run** (`autofold-dryrun.txt`): `strict count: 4/27 on 31 -> 4/27 on 31; strictest 4/27 -> 4/27`. The
  generated module `TailZ75`, which defines `OpenResearchLeaves49` and `sixContactMin_of_open68`, compiles once its
  first line is stripped. Its axioms are `[propext, Classical.choice, Quot.sound]` (`autofold-dryrun-compile.txt`,
  VERIFIED).
* **Kinds rows.** These were generated by a real `autofold.py` run, saved in `kinds-diff.txt`, and then reverted; the
  generated Main.lean, kinds.tsv and TailZ75 are not committed.
  * Removed: `research	carayolThmAIrr	consequence	…	GLUE	GLUE	…`.
  * Added: `research	carayolThmAFrob	published	<flag of autofold.json>	GLUE	GLUE	<source of autofold.json>	carirr-refold; pending review		long-pole	T4	unread	elliotglazer/diophantine-z-q#37`.
  * Count-neutral now. After a reader's check (flag cleared, strict LEAF) the count is GLUE −1.
* **Proposed locators.md row** (not written, since locators.md is shared): `carayolThmAFrob` | DDT 1997 Thm 3.1 (a)-(d)
  pp. 85-86 and §2 p. 54; Carayol 1986 §§0.3-0.7, Théorème (A), pp. 409-411 (manuscript L9778, normalization
  L9784-9796); Casselman 1973 Thm 1 pp. 302-306; Ribet 1977 Thm 2.3 | locators UNVERIFIED | the conductor clause is
  packaged only in DDT.

## 5. What remains

* A reader to check the leaf against DDT 3.1 (a)-(d), pp. 85-86, and Ribet 1977 Thm 2.3. That turns the row LEAF
  (GLUE −1).
* A `docs/research/locators.md` row for `carayolThmAFrob` (proposed text in §4). I did not edit locators.md, a shared
  file.
* Carayol's own form of Théorème (A) needs Weil–Deligne representations, local Langlands for `GL₂(ℚ_p)` and the
  local components of a newform in Lean. That is very large infrastructure and not in reach.
