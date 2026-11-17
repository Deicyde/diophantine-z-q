# carayol-herbrand: the conductor of `CarayolThmAIrr` is DDT's conductor (Herbrand's theorem, proved in Lean)

Task carayol-herbrand. Branch `wip/carayol-herbrand`, from `wip/r17-rebase` 4095ce12, with origin/main c40109f3 merged
(merge commit bae8f7dc, no conflicts). Date: 2026-11-17.

Marks: **VERIFIED** means compiled, computed, or read in the named file. **STANDARD** means published, with the
reference given. **SPECULATIVE** is marked as such. Theorem and page numbers that come from memory, or from the task
text without being re-read here, are **UNVERIFIED** (no network).

## 0. Result

**r17-rebase's leaf `CarayolPrinted.CarayolThmAIrr` is equivalent in Lean to Darmon–Diamond–Taylor 1997 Thm 3.1 with
DDT's own definition of the conductor.** All VERIFIED (compiled, standard axioms):

* **`CarayolHerbrand.condExp_eq_ddt`.** Let `K` be an ultrametric normed field with `‖ℓ‖ < 1`, and let
  `ρ : G_{ℚ_p} → GL_n(K)` be continuous, with `p ≠ ℓ`. Then the kernel's Serre–Tate exponent equals DDT's exponent:
  `(condExp ρ : ℝ) = codim V^{I_p} + ∫₀^∞ codim V^{G_{ℚ_p}^u} du`.
  * `condExp` is `codim V^{I_p}` plus the lower-numbering Swan sum `∑_{i≥1} (g_i/g_0) codim V^{G_i(L)∩P}` at an adapted
    finite level `L`.
  * The right side is DDT's exponent, with the upper-numbering groups `LadicCond.upperAbs p u`.
* **`CarayolHerbrand.carayolThmAIrr_iff_DDT : CarayolThmAIrr ↔ CarayolThmAIrrDDT`.** The new leaf
  `CarayolThmAIrrDDT` is `CarayolThmAIrr` with its conductor clause rewritten to transcribe DDT's integral.
* **`CarayolHerbrand.carayolR17'_of_DDT : CarayolThmAIrrDDT → DSCoeffExt.EigenformCoeffFieldFinite → LadicCond.CarayolR17'`.**
  This discharges `r17` (`#discharges`, §5).
* **Fold dry run** (`scratch/carayol-herbrand/autofold.json`, field `r17`, leaf `carayolThmAIrrDDT`, published, flagged
  unread): strict `11/18 on 29 -> 12/17 on 29`, strictest `11/18 -> 12/17`. That is **GLUE −1**, the count r17-rebase
  claimed.
  * r17-rebase's −1 depended on its conductor clause being printed. That clause carried the reading risk "the Herbrand
    step from DDT's integral to the Lean `condExp`". That step is now a Lean theorem.
  * What remains for the statement check is a clause-by-clause comparison of `CarayolThmAIrrDDT` with DDT Thm 3.1 (§4).

The file is `ZInQKernel/Contrib/OneProof/CarayolHerbrand.lean` (new, about 350 lines). It imports
`ZInQKernel.Contrib.OneProof.CarayolPrintedIrr`, which declares the statement, and `ZInQKernel.OneProof.H.TailB`, which
holds the kernel's proved Swan/Herbrand glue. It does not import `OneProof.Main`. No `sorry`, no `axiom`.

## 1. What was there, and what Mathlib has (VERIFIED, read)

* **Mathlib v4.35 has no higher ramification groups.** `Mathlib/RingTheory/Valuation/RamificationGroup.lean` defines
  only `decompositionSubgroup` and `inertiaSubgroup` ("TODO: Define higher ramification groups in lower numbering").
  There is no Herbrand function and no upper numbering.
* **The kernel already has the finite-quotient theory this task needed.** It is in
  `ZInQKernel/HDecomp/Conductor/LadicCond.lean`:
  * `ramSet L i`: Serre's `G_i(L/ℚ_p)`, pulled back to `G_{ℚ_p}`: `v_L(σx − x) ≥ i+1` on `𝓞_L`.
  * `phiAt L u`: `∫₀ᵘ g_t/g_0 dt`, with `g_t = |G_{⌈t⌉}|`. This is Serre's φ, since `1/(G_0:G_t) = g_t/g_0`.
  * `upperSet L v`: `G_{ψ(v)}`, where `ψ(v) = inf{u ≥ −1 : v ≤ φ(u)}`.
  * `upperAbs p v`: the `σ` with `σ|_L ∈ G^v(L/ℚ_p)` for every finite Galois `L`. This is Serre IV §3's definition for
    infinite extensions.
  * `swanAt`, `swan`, `condExp`.
* **The kernel already proves the conversion at an adapted level.** `ZInQKernel/OneProof/H/TailB.lean` (task swan,
  folded in leaf-fold2) proves, for every coefficient field `k`:
  * `HDec.Swan.swanAtIntegral`: the finite-level change of variables `u = φ_L(t)`.
  * `HDec.Swan.upperAbsWild`: `G^u ⊆ P_p` for `u > 0`.
  * `HDec.Swan.upperAbsSurj_of_herbrand`: `G^u → G^u(L/ℚ_p)` is onto. It follows from Herbrand's theorem
    `HDec.SwanBridge.herbrandUpper_of_quotient PkgI6.herbrandQuotient` (proved in
    `ZInQKernel/Contrib/Different/Local.lean`) and the compactness of `G_{ℚ_p}`.
  * `HDec.Swan.swanIndependent_proved`.
  * Together these give `HDec.Swan.swanAt_eq_integral_upperAbs`: `swanAt L ρ = ∫₀^∞ codim V^{G^u} du` at every adapted
    `L`.
* **What was missing.** An adapted level must exist for the leaf's representations.
  * The kernel proves `AdaptedExists` (`HDec.Swan.adaptedExists`) only for coefficients `ℚ̄_ℓ = PadicAlgCl ℓ`.
  * The leaf's `ρ` has coefficients `K_{f,λ} = λ.adicCompletion K_f`.
  * If no adapted level exists, `condExp` silently takes the Swan term to be `0`. So without existence the two forms
    are not comparable.

## 2. New Lean (VERIFIED, compiled)

`ZInQKernel/Contrib/OneProof/CarayolHerbrand.lean`, namespace `CarayolHerbrand`:

| section | theorem | content |
| --- | --- | --- |
| §1 | `norm_natCast_eq_one_of` | `‖m‖ = 1` for `ℓ ∤ m` in an ultrametric normed field with `‖ℓ‖ < 1` (Bézout `a m + b ℓ = 1`) |
| §1 | `Bd.*`, `norm_pow_sub_one_entry`, `exists_level` | the kernel's ultrametric matrix estimate and Krull-level lemma, for a general `K` instead of `ℚ̄_ℓ` |
| §1 | `adaptedExists_of_norm` | **adapted levels exist** for continuous `ρ : G_{ℚ_p} → GL_n(K)`, `K` ultrametric with `‖ℓ‖ < 1`, `ℓ ≠ p` (the proof of `Swan.adaptedExists`: `ρ(P_p ∩ G_L)` is trivial, since an element of `p`-power order on every level cannot move `1 + A` by `max ‖A_ij‖ < 1` when `ℓ ∤ p^k`) |
| §2 | `ddtCondExp` | DDT's exponent `codim V^{I_p} + ∫_{(0,∞)} codim V^{upperAbs p u} du` |
| §2 | `condExp_eq_ddt_of_adapted` | at any adapted level, `condExp ρ = ddtCondExp ρ` (from `swanIndependent_proved` and `swanAt_eq_integral_upperAbs`; any field, no continuity) |
| §2 | `condExp_eq_ddt` | the same for every continuous `ρ` over an ultrametric `K` with `‖ℓ‖ < 1`, `ℓ ≠ p` |
| §3 | `norm_natCast_lt_one` | `ℓ ∈ λ ⇒ ‖ℓ‖ < 1` in `K_λ` (Mathlib's `instNormedFieldValuedAdicCompletion`, `FinitePlace.norm_lt_one_iff_mem`); `IsUltrametricDist K_λ` is found by instance search |
| §4 | `CarayolThmAIrrDDT` | the leaf with DDT's conductor (below) |
| §4 | `condExp_decomp_eq_ddt` | the two conductor clauses agree for every continuous `ρ : G_ℚ → GL₂(K_λ)`, `λ ∣ ℓ`, `p ≠ ℓ` (through `decomp p`) |
| §4 | `carayolThmAIrr_iff_DDT`, `carayolThmAIrr_of_DDT`, `carayolR17'_of_DDT` | the equivalence and the discharge |

Axioms of the main theorems (`scratch/carayol-herbrand/axioms.txt`): `[propext, Classical.choice, Quot.sound]`.

Mathlib's norm on `adicCompletion` is `Valued.toNormedField`. Its uniform structure is the `Valued` one, so its topology
is definitionally the one in `CarayolThmAIrr`'s `Continuous ρ`. VERIFIED: the proof typechecks with `exact`, with no
`convert`.

### The new leaf

`CarayolThmAIrrDDT` is `CarayolThmAIrr` word for word, except that the last clause
`condExp (ρ.comp (decomp p)) = v_p(N)` becomes

```lean
∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ →
  (codimInv (ρ.comp (decomp p)) inertiaSet : ℝ) +
    ∫ u in Set.Ioi (0 : ℝ), (codimInv (ρ.comp (decomp p)) (upperAbs p u) : ℝ) = (N.factorization p : ℝ)
```

This is `codim ρ^{I_p} + ∫₀^∞ codim ρ^{I_p^u} du = v_p(N)`, the exponent DDT §2 defines (as the task transcribes
it). `I_p^u` is `G_{ℚ_p}^u`; on `u > 0` it lies in `P_p ⊆ I_p` (`Swan.upperAbsWild`). The integral is Mathlib's Bochner
integral. For these `ρ` the integrand is a step function with compact support. That is not assumed; it follows from
the equality with the finite Swan sum.

## 3. Option chosen

The task offered two routes:

1. prove `condExp` equal to DDT's integral for the leaf's representations;
2. redefine the leaf's conductor and re-prove the consumers.

Both are done, and route 1 makes route 2 free. With the equivalence `carayolThmAIrr_iff_DDT`, every consumer of
`CarayolThmAIrr` takes `CarayolThmAIrrDDT` unchanged:

* the `r17` discharge `carayolR17'_of_printedIrr`;
* Scenario F's `carayolRealization_of_printed` in `scratch/r17-rebase/ScenarioF.lean`, through `carayolThmA_of_irr`.

The proof stays in the finite-quotient case, as the task asked. Wild inertia acts through `Gal(L/ℚ_p)` for an adapted
`L`. Herbrand enters only as the kernel's finite-level statement `(G/H)^v = G^v H/H` for `L ⊆ M` finite Galois, plus
compactness.

## 4. Rating of the new leaf

**`carayolThmAIrrDDT`: printed form, LEAF (published), flag `unread`.** The reasons:

* **The conductor clause is DDT's definition, transcribed.** It uses genuine definitions: Serre's lower and upper
  numbering on the finite Galois subextensions of `ℚ̄_p = PadicAlgCl p`, and invariants of `ρ|_{G_{ℚ_p}}`. It no longer
  needs a theorem step (Herbrand) to match the print. That step is the Lean theorem `carayolThmAIrr_iff_DDT`.
* **The other clauses are unchanged from `CarayolThmAIrr`.** Their rating is r17-rebase's (§4 of
  `docs/research/r17-rebase.md`): continuity; irreducible over `K_{f,λ}` (Ribet); odd (from `det = ψ χ_ℓ`); unramified
  outside `Nℓ` with trace `a_p`. The task reports a reading that finds all of them in DDT 1997 Thm 3.1 (a)–(d),
  pp. 85–86, with (d) "the conductor `N(ρ)` is the prime-to-`ℓ` part of `N`". This task did not re-read DDT (no
  network): UNVERIFIED here.
* **Not stronger than the print.** It asserts one representation `ρ_{f,λ}` and only the listed properties, as
  `CarayolThmAIrr` does. The two statements are equivalent in Lean.

**Statement check, what remains to read** (DDT 1997, UNVERIFIED pages):

1. §2, p. 54: the definition of the conductor exponent at `p ≠ ℓ` as `codim V^{I_p} + ∫₀^∞ codim V^{I_p^u} du`.
   * If DDT instead defines it through the Weil–Deligne representation (`codim (ker N)^{I_p}` + Swan), it is the same
     number. `V^{ρ(I_p)} = (ker N)^{I_p}` by Grothendieck's monodromy theorem (STANDARD; Serre–Tate 1968 §2; numbering
     UNVERIFIED).
   * That identification would then be a reading note, not a Lean step.
2. Thm 3.1 (a)–(d):
   * the irreducibility statement over `K_{f,λ}`;
   * `det ρ_{f,λ} = ψ ε` (oddness);
   * the normalization of `Frob_p` in the trace clause: the leaf uses arithmetic Frobenius with `tr = a_p`, as in
     r17-rebase;
   * (d) the prime-to-`ℓ` conductor.

Proposed `locators.md` row (not added; the file belongs to other tasks):
`R17 (DDT form, carayol-herbrand) | Darmon–Diamond–Taylor 1997 §2 p. 54 (conductor), Thm 3.1 (a)–(d) pp. 85–86 | — |
UNVERIFIED | ρ_{f,λ} over K_{f,λ}: irreducible, odd, traces a_p, conductor exponent codim V^{I_p} + ∫₀^∞ codim V^{I_p^u} du
= v_p(N) at p ≠ ℓ; equivalent in Lean to CarayolThmAIrr (Herbrand)`.

## 5. `#discharges` and the fold (VERIFIED)

`scratch/carayol-herbrand/Discharges.lean`, run against the merged main (`lake build +ZInQKernel.OneProof.Main
+ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.CarayolHerbrand`, 14232 jobs, OK; main's `frozenTarget` uses
the standard axioms). Output in `discharges.txt`:

```
DISCHARGES [OpenResearchLeaves31.r17] by CarayolHerbrand.carayolR17'_of_DDT
  still assumes: [CarayolHerbrand.CarayolThmAIrrDDT, DSCoeffExt.EigenformCoeffFieldFinite]
  axioms: [propext, Classical.choice, Quot.sound]
...
#discharges: 35 open hypotheses, 9918 theorems checked, 41 discharge one
```

The other `r17` lines in the output come from r17-rebase's and r17-print's existing theorems (`carayolR17'_of_printedIrr`
and others).

Fold dry run (`scratch/carayol-herbrand/autofold-dryrun.txt`):
`strict count: 11/18 on 29 -> 12/17 on 29; strictest 11/18 -> 12/17`.
The generated module (`AutofoldDryRun.lean`, the dry-run output without its first line) compiles.
`HDec.HSyn.sixContactMin_of_open49` (over `OpenResearchLeaves32`: `r17` dropped, `carayolThmAIrrDDT` added) uses the
axioms `[propext, Classical.choice, Quot.sound]` (`autofold-dryrun-compile.txt`).

Specs:

* `scratch/carayol-herbrand/autofold.json`, against main, where `r17 : LadicCond.CarayolR17'` is still open:
  * field `r17`;
  * proof `_root_.CarayolHerbrand.carayolR17'_of_DDT {n}.carayolThmAIrrDDT {n}.eigenformCoeffFieldFinite`;
  * leaf `carayolThmAIrrDDT : _root_.CarayolHerbrand.CarayolThmAIrrDDT`, kind `published`, flag `unread: …` (the
    statement-check items of §4).
  * This **supersedes** `scratch/r17-rebase/autofold.json`: same count, and no Herbrand reading risk.
* `scratch/carayol-herbrand/autofold-after-r17rebase.json`, for the case where r17-rebase's fold has landed first and
  `carayolThmAIrr` is the open field:
  * proof `_root_.CarayolHerbrand.carayolThmAIrr_of_DDT {n}.carayolThmAIrrDDT`;
  * count-neutral (LEAF for LEAF); it removes the reading risk from the flag.

Fold recipe for the integrator:

1. Merge `wip/carayol-herbrand`. Under `ZInQKernel/` this adds r17-rebase's four files (`NewformDict.lean`,
   `CarayolLevel.lean`, `CarayolPrinted.lean`, `CarayolPrintedIrr.lean`) and `CarayolHerbrand.lean`, all in
   `ZInQKernel/Contrib/OneProof/`.
2. Run `python3 scripts/one_proof/autofold.py scratch/carayol-herbrand/autofold.json`.
3. Run the usual checks:
   * `lake build +ZInQKernel.OneProof.Main`;
   * `#print axioms ZInQ.OneProof.frozenTarget`;
   * DumpCompact with `cmp_hashes.py`;
   * `OpenStatements.lean`;
   * `render_open.py` and `render_open.py --check`.

## 6. What remains

* **The statement check of §4** against DDT 1997 (§2 p. 54 and Thm 3.1). It decides whether the count is −1 or 0.
  The Herbrand step is no longer part of it.
* **`eigenformCoeffFieldFinite`** (composite, pending reading) is unchanged. The discharge uses it at `k = 2` only.
* **The fold itself** is the integrator's step.

## 7. Files

* `ZInQKernel/Contrib/OneProof/CarayolHerbrand.lean` (new).
* `scratch/carayol-herbrand/`:
  * `log.md`;
  * `Axioms.lean`, `axioms.txt`;
  * `Discharges.lean`, `discharges.txt`;
  * `autofold.json`, `autofold-after-r17rebase.json`, `autofold-dryrun.txt`, `AutofoldDryRun.lean` and its compile
    output;
  * build logs `build1.txt`, `build2.txt`.
