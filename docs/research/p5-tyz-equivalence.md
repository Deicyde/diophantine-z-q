# P5: the exact existential content of `PropN.TYZInputs`

**Result:** the source-derived `ZInQ.PropN.tyzInputs_iff` is proved and passed fresh Lean compilation and scoped raw-body kernel replay. It is an equivalence of the existing formal predicates, **not** an unconditional proof of `TYZInputs`, reading A, analytic continuation, or the headline theorem. Independent non-author review and designated Astra acceptance remain pending.

- Target: `elliotglazer/diophantine-z-q` issue 37, P5.
- Frozen base: `a5937595cde3e3db00975b81e5171cdef92c801a`.
- Contributor: P5 proof-worker, AI-assisted formalization; no authenticated serving-model claim is made.
- Date: 2026-11-13 UTC.
- New sources only: `ZInQKernel/Contrib/TYZEquivalence/CanonicalL.lean`, `Equivalence.lean`, `Checks.lean`, and this dedicated research note.
- No existing source, statement, registry, checker, root import, dependency pin, manuscript, or acceptance record was changed. No commit, push, PR, land, publication, or human outreach was performed.

## 1. Exact declarations and meaning

The principal declaration is in `Equivalence.lean:42`:

```lean
theorem ZInQ.PropN.tyzInputs_iff :
    ZInQ.PropN.TYZInputs ↔ ∀ n : ℕ, n % 8 = 5 → Squarefree n →
      (∃ F : ℂ → ℂ,
        ZInQ.Literature.IsLContinuation (ZInQ.shortCurve (-(n : ℚ) ^ 2)) F ∧
        analyticOrderAt F 1 ≤ 1) ∨
      (ZInQ.Literature.T5aCl n = 0 ∧ ZInQ.RouteK.Rank5b.T5bCl n = 0)
```

There are no explicit, implicit, typeclass, universe, or section hypotheses on this declaration. `Checks.exactStatement` spells out the same type separately; the raw-body audit checked full kernel definitional equality against it and rejected the possibility of extra binders. The printed kernel type negates the square of the rational parameter: `Rat.instNeg.neg (instHPow.hPow n.cast 2)`, not the square of its negative.

The appropriate reading-A formulation is:

```lean
def ZInQ.PropN.ParitySupportedContinuation : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    (ZInQ.Literature.T5aCl n ≠ 0 ∨ ZInQ.RouteK.Rank5b.T5bCl n ≠ 0) →
    ∃ F : ℂ → ℂ,
      ZInQ.Literature.IsLContinuation (ZInQ.shortCurve (-(n : ℚ) ^ 2)) F

theorem ZInQ.PropN.tyzInputs_iff_readingA_and_supportedContinuation :
  ZInQ.PropN.TYZInputs ↔
    ZInQ.Literature.TYZThm35ReadingA ∧ ZInQ.PropN.ParitySupportedContinuation
```

Equivalently, `tyzInputs_iff_supportedOrderOne` identifies `TYZInputs` with continuation of order at most one on that same support. Both rows matter: replacing their disjunction by row 5b alone is not the assertion proved.

**No global Hecke strengthening.** The frozen `HeckeContinuation` ranges over every nonzero natural parameter, including even and non-squarefree ones. The existing `TYZInputs` only forces continuation at squarefree class-5 indices where its integer witness is nonzero. Eliminating that existential witness forces existence on the nonzero support of either genus sum, not on the full Hecke domain. P5 does not claim the converse implication to global Hecke continuation, nor a counterexample to that classical statement. It proves the exact restricted equivalence instead.

The separate corollaries preserve the broader premise explicitly:

```lean
theorem ZInQ.PropN.tyzInputs_of_readingA
  (hA : ZInQ.Literature.TYZThm35ReadingA)
  (hH : ZInQ.Literature.HeckeContinuation) : ZInQ.PropN.TYZInputs

theorem ZInQ.PropN.tyzInputs_and_hecke_iff :
  ZInQ.PropN.TYZInputs ∧ ZInQ.Literature.HeckeContinuation ↔
    ZInQ.Literature.TYZThm35ReadingA ∧ ZInQ.Literature.HeckeContinuation
```

These are conditional implications/equivalences, not recognized closed providers for any literature premise. In particular no theorem of type `TYZInputs`, `TYZThm35ReadingA`, or `HeckeContinuation` without assumptions was supplied. No `Fact TYZInputs` is used.

## 2. Reconstruction from the actual sources

The formal source definitions, not the earlier verdicts, fix the claim:

1. `Hypotheses/TYZInputs.lean:99–105,181–185` requires one integer function with `L 1 = 1`, the two exact convolution congruences, I7 only when `L n ≠ 0`, and genus data for each squarefree class-5 `n`.
2. `Hypotheses/CR3Literature.lean:43–59,118–144` fixes the entire continuation, its uniqueness, the first genus sum, the broader Hecke domain, and reading A with its universal quantifier over continuations.
3. `RouteK/Rank5b/Sec3/RedeiStatement.lean:32–57` fixes the exact class number and the second genus sum.
4. `RouteK/PropN.lean:765–772,1369–1372,1392–1449,1454–1496,1612–1613,1797–1820` supplies the convolution solution, its uniqueness induction, matching, the forward implication, and the two witness branches.
5. `pn-design.md:24–30,69–74,99–123,147–155,213–217` and `nt-tyz.md:93–108,181–185,198–219,375–421,483–509` explain the intended predicate and unordered conventions.

Only after this source reconstruction, the exact existing proposal was compared: `rv-pn-encoding.md` F1, lines 84,105–106,129–139, already proposes this disjunctive iff and its derivation. This is a formalization of an existing justified proposal, not a claim of new mathematical priority. The current `PropN.lean` consistency discussion at lines 1499–1524 already contains the zero-value witness and says that the last iff assembly is not yet written in Lean. P5 supplies that assembly in new modules.

### The simultaneous integer witness

`TYZEquivalence.canonicalL` is one function on all natural numbers:

```lean
def canonicalL (m : ℕ) : ℤ :=
  if m % 8 = 1 ∨ m % 8 = 3 then ((Lam m).val : ℤ)
  else if m % 8 = 5 ∧ (T5aCl m ≠ 0 ∨ T5bCl m ≠ 0) then 1 else 0
```

On classes 1/3, `ZMod.natCast_zmod_val` gives the exact parity `Lam m`. The already proved `lemmaN1_core` supplies exactly the frozen convolution; `lemmaN1` is its strong-induction uniqueness argument. Thus no new recursive function or unproved choice of convolution coefficients is needed: the lift is a representative of the existing uniquely recursively determined parity solution.

On class 5, the value is the indicator of the minimum parity-forced analytic support. This is deliberately not an assertion that the original Tian–Yuan–Zhang invariant equals this bit. The frozen existential encoding reads class-5 values only through zero/nonzero. A both-even index may be assigned 0 even if an order-one continuation also exists there; that is allowed by the actual one-way I7 condition. On all other residue classes the value is 0.

`canonicalL_values` proves that every chosen integer value is 0 or 1. `canonicalL_genusData` constructs the genus-data existence simultaneously on the required domain but supplies no I7 continuation:

- Nonzero branch: `Witness.genusData_nonempty` supplies the free-plus-torsion model.
- Zero branch: `genusData_nonempty_iff_genusSums` translates `Witness.genusData_nonempty_iff_parities` through `lemmaN1` and `matching`; both rows are zero by the indicator definition.

The same exact integer `gNat` is retained inside the source witness, including `beta_seven`. It is not replaced by a parity bit; only the final weighted sums are cast into `ZMod 2`.

### The two directions

**Available → needed, forward.** Unpack the one `L` and its full frozen hypotheses. At a required `n`, `L n ≠ 0` invokes precisely I7. If `L n = 0`, the model, normalization and convolution feed `genusSums_eq_zero`, producing both zero genus sums. There is no appeal to the iff being proved.

**Available → needed, reverse.** Choose `canonicalL` once, before the quantifiers over `n`. Normalization and convolution are already proved. If its class-5 value is nonzero, at least one row is nonzero; the both-zero disjunct of the supplied criterion is impossible, so its other disjunct supplies the required I7 continuation and order bound. Genus data come from the two branches above. No analytic continuation is chosen or asserted at a both-zero index.

**Reading-A transition.** The existing `tyzThm35ReadingA_of_tyzInputs` gives reading A in the forward direction; its uniqueness argument compares continuations of exactly the same curve and L-series. Conversely, restricted continuation existence chooses an `F` only on the nonzero support. If its order is not at most one, `two_le_of_not_le_one` supplies `2 ≤ analyticOrderAt F 1`; reading A would make both rows zero, a contradiction. This works also at infinite analytic order. No functional equation or root number is assumed to strengthen `≤ 1` to `= 1`.

## 3. Source-to-consumer contract and exceptional cases

The claimed scope is the entire internal equivalence, not an assembled proof of a published arithmetic theorem. The following are author reconstruction and checked formal derivations, **not independent acceptance**.

| Obligation | Required, constructed, and connecting evidence |
|---|---|
| Source hypotheses | All four conjuncts of the frozen existential predicate are used or supplied exactly. Main iff has no additional binders. The zero-model criterion is applied with its actual `L 1 = 1`, squarefreeness, class-5 and zero-value hypotheses; convolution is used only in the parity-to-genus translation. |
| Constructed objects | One `canonicalL : ℕ → ℤ` for every index. Each genus model is the existing `Witness` model, including its exact Gaussian-integer torsion quotient and exact `gNat`. No identification with a geometric TYZ point is newly claimed. |
| Domain/index coverage | Class-1 convolution uses squarefree `m > 1`; class-3 convolution uses squarefree `m % 8 = 3`. For a divisor of required `n`, `Nat.div_dvd_of_dvd` preserves squarefreeness of the quotient. Divisor residues 5 and 7 give quotient residues 1 and 3 respectively through the existing `div_mod8_of`. The analytic domain is exactly squarefree class 5 on either-row support. |
| Transition maps | Integer-to-`ZMod 2` cast commutes with the finite sums and products. `canonicalL_cast` identifies the representative with `Lam`. The exact quotient `n/e` is justified by divisor membership, and `weightedParity_eq_lam` plus `matching` identifies both weighted parities with the consumed rows. |
| Consumed-object identity | Both sides use the same `shortCurve (-(n : ℚ)^2)`, the same `IsLContinuation` and `analyticOrderAt`, and the existing `T5aCl`/`T5bCl`. No change of L-series normalization, curve, genus-sum index set, or witness universe occurs. |
| Coefficients/normalizations | `L 1 = 1` is proved, not just oddness at 1. `Lam` is lifted via its finite representative; original TYZ integer values are not identified with that lift. `gNat` remains the exact integer class number where required by the genus-data fields. |
| Local conditions | No new number-field, local-field, Galois or geometric theorem application is made. Source genus models remain abstract modules exactly as in the frozen encoding. Analytic continuation retains global differentiability and agreement on `Re s > 3/2`; no new convergence assertion is made. |
| Exceptional cases | Zero and one are handled explicitly; `class5_domain` proves positive odd `n ≠ 1`. Both integer-value branches are checked, including an inhabited zero model. Even, other-residue, and non-squarefree analytic indices are outside the frozen domain, not implicitly added. Infinite analytic order is covered by the existing ENat order lemma. |
| Downstream consumption | The exact reading-A and order-one-support corollaries are supplied. Existing `TYZRow5b` and headline providers remain unchanged. Global Hecke is used only in explicitly conditional corollaries and included on both sides of its conjunction iff. Root integration and renewed independent review remain the integrator's work. |

### Unordered partitions and small cases

- The class-1 convolution still sums over `d % 8 = 1 ∧ d*d < m`. It does **not** replace this by the ordered divisor sum. The source `part_N1_one` compares representatives using its fixed-point-free divisor involution; `m > 1` and squarefreeness are retained.
- For class 3, the class-1 divisor is distinguished by its residue; the sum remains `L (m/d) * L d`. No extra factor of two is inserted.
- Both genus sums remain sums over `Finpartition` of the set of prime factors, with nonempty blocks, not ordered factorizations. The source `matching` retains the unique class-5 block, or the unique class-7 and class-3 blocks, and the class-1 remainder.
- `m = 1` is excluded from the first convolution and supplied by exact normalization. The empty-partition value is the source `part_Lam_one`, not a new convention.
- `m = 3` is included in the second convolution. This uses the already frozen mod-2 statement, not an equality that would lose the documented odd `w_K = 3` factor.
- At `n = 0`, `canonicalL_zero` proves 0 without consuming `Lam 0` or a zero-parameter L-series. `zero_and_one` checks both endpoints together.
- At a squarefree class-5 `n`, the class-5 divisor `e = n` remains present and has quotient 1; its coefficient is the exact normalization `L 1 = 1`.
- Nonsquarefree indices are not smuggled into `matching` or I7. The chosen function is total there, but no corresponding analytic/model assertion is claimed outside the stated domain.
- `Checks.no_zero_value_at_nonzero_rows` proves that any normalized convolution witness with genus data must have `L n ≠ 0` whenever either row is nonzero. Thus an all-zero class-5 choice cannot bypass the actual analytic obligation at such an index.

No mathematical counterexample to the fixed P5 iff was found. The broader informal phrase “reading A together with continuation” must retain the domain qualification above; dropping it would assert more than this formal derivation supplies.

## 4. Frozen proof-source hashes

All digests are SHA-256 of the actual file bytes. New sources are UTF-8 with LF line endings.

| Source | SHA-256 |
|---|---|
| `ZInQKernel/Contrib/TYZEquivalence/CanonicalL.lean` | `e7536e64986958162cb3d0da90e4f542d422b682bddc14bae11375b9a295240e` |
| `ZInQKernel/Contrib/TYZEquivalence/Equivalence.lean` | `441e086783184bfb5fb148056a65b7126a00ae02206aead428ef4223c78efa17` |
| `ZInQKernel/Contrib/TYZEquivalence/Checks.lean` | `1d6bb04292730202e46363f5d742a9386710d6b622ca349b2ce26fdd1a432c02` |
| `ZInQKernel/Hypotheses/TYZInputs.lean` | `a14dd433e5c557be2d48b3f325d3b3a7d70e5531061c5d6936c5902fd5a701cd` |
| `ZInQKernel/Hypotheses/CR3Literature.lean` | `cdd4d0946f229121a9824629cf8ddade58d8490d6eaf67164fa4dd9b0ef5cc3d` |
| `ZInQKernel/RouteK/PropN.lean` | `5909f4f7f4f72cdbe0b17f6446b969e188e0fb3d3f8530b1a159c48c514dd080` |
| `ZInQKernel/RouteK/Rank5b/Sec3/RedeiStatement.lean` | `2b7db0a329cb7837af8b1d97083bca52c900e18fa8d8290f9a63f98f715d6663` |
| `docs/research/pn-design.md` | `c19b9183bc53f45ec9c47bc80da798dbdf332b9f9452363e19121a526b052130` |
| `docs/research/nt-tyz.md` | `37099e2006a61eb485105f54d94404d16e424ef1070137590ec62989d3693be1` |
| `docs/research/rv-pn-encoding.md` | `4bb1aab5f4d9645ecd9710922febe5351168ab7ce9938791b26abc90fb2c898f` |
| Mathlib `Mathlib/Data/ZMod/Basic.lean` | `f86120453447f00e0c87188381e0e8d15e0d8c85a080c8f8a8ba2da04f5e2f8a` |
| `scripts/audit_kernel.lean` | `673af3d23f5433cb17145e9de8cac97b40a7d513281b7c2a726fb19ca089facc` |

Toolchain and dependency identity:

- Lean 4.35.0, compiler commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (Release).
- Lake 5.0.0-src+eb6cafb.
- Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, committed input `v4.35.0`.
- `lakefile.toml`: `59de72bc6b1a590bb351a0fc4b877565943d9f55c7aa1fcaf377209464a0d2f2`.
- `lake-manifest.json`: `f7ce830d517bfbcb4cdcc90bef299da854c9b28653b9accc2b13df2822233779`.
- `lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.

The pinned package tree was shared read-only. Existing project imports came from the private root-build snapshot. P5 compiled only its own new modules; it did not run dependency/cache setup or a whole-project build. The source/pin invariance check against the exact base passed.

## 5. Actual verification and axiom evidence

Final verification was a successful sequential chain, exit status **0**, in fresh Lean processes with `LEAN_NUM_THREADS=2`, `-j2`, and warnings treated as errors for the three P5 modules. At most one P5 compiler process ran at a time.

| Check | Result | Elapsed | Peak resident memory |
|---|---|---|---|
| `CanonicalL.lean` fresh compile | passed, no warnings/errors | 5.18 s | 6,986,648 KiB |
| `Equivalence.lean` fresh compile | passed, no warnings/errors | 4.76 s | 6,969,912 KiB |
| `Checks.lean` fresh compile and `#print axioms` | passed, no warnings/errors | 4.65 s | 6,976,748 KiB |
| Scoped raw-body kernel replay | passed | 16.05 s | 16,291,016 KiB |

The existing `scripts/audit_kernel.lean` ran unchanged and treated P5 modules as data rather than importing them into its executable or executing candidate initializers. It rebuilt a kernel environment from the external imports, replayed **32 declaration bodies/raw occurrences from exactly 3 P5 modules**, checked the explicit expected headline type and all 24 named exports, and traversed actual dependency bodies for forbidden axioms.

Actual audit fields:

```json
{
  "schema": "kernel-audit/v1",
  "status": "passed",
  "modules": [
    "ZInQKernel.Contrib.TYZEquivalence.CanonicalL",
    "ZInQKernel.Contrib.TYZEquivalence.Equivalence",
    "ZInQKernel.Contrib.TYZEquivalence.Checks"
  ],
  "declarations": 32,
  "raw_declaration_occurrences": 32,
  "duplicate_theorem_bodies_rechecked": 0,
  "runtime_declarations_not_replayed": [],
  "allowed_axioms_used": ["Quot.sound", "Classical.choice", "propext"],
  "headline": "ZInQ.PropN.tyzInputs_iff",
  "targets": [],
  "protocol_acceptance": false
}
```

`Checks.lean` printed the axiom closure of **every one of the 24 named new declarations**, including the three new definitions, main iff, both continuation-support equivalences, conditional Hecke corollaries, the explicit expected statement, and boundary/non-vacuity checks. Every output was exactly `[propext, Classical.choice, Quot.sound]`. It also printed and checked that same closure for seven substantive frozen suppliers: `lemmaN1_core`, `lemmaN1`, `matching`, `genusSums_eq_zero`, both existing genus-data existence/iff lemmas, and `IsLContinuation.eq`. There was no `sorryAx` or other extra axiom.

An explicit-file token scan additionally found no admission, unsafe declaration, native-decision tactic, partial declaration, or runtime proof override in the P5 code. This scan is supplementary; the raw-body replay and actual axiom closure are the proof evidence.

Audit artifact bindings (local build artifacts; reproduction below supplies the specification):

| Artifact | SHA-256 |
|---|---|
| `kernel-spec.json` | `f2354477676be161ad745b858c49f6b2e95b77a8cc48358121fb4c5e51a904d3` |
| `kernel-report.json` | `3eaa70ff1e52448fb5f140e2d85e19634f056e63a4eee5f5409fe91228a34d27` |
| `axioms-final.log` | `2a54c98077c9fe80bba361fb04c97587c8206b2be17c6cae8ff8223d5580cfe9` |
| `kernel-final.log` | `531a0320d1a537f626f684276f1cf15b619d3f713b0dd212cf2cf593bdb7af1a` |

These machine results certify the newly elaborated formal equivalence relative to the identified imports and the allowed primitive axioms. They do not certify independent mathematical source coverage, geometric faithfulness of TYZ's published inputs, current global CI, or protocol/release acceptance. The memory/time measurements are for this snapshot-based scoped run, not a cold dependency build.

## 6. Error and review history

All failures were preserved as failures; none was used as a successful check or repaired by changing a statement.

1. Initial `CanonicalL.lean` compile exited 1. Its `canonicalL_ne_zero_iff` proof used `simp only` with the old outer-condition proof and the residue equality in one call. Simplification normalized `n % 8` before matching that outer proof, leaving an impossible `5 = 1 ∨ 5 = 3` branch and unresolved branch goals. It also reported deprecated `if_pos`/`if_neg` names. The repair first eliminates the outer branch with explicit `rw`, then splits the row-support condition with `ite_eq_left`/`ite_eq_right` and explicit `iff_of_true`/`iff_of_false`. The theorem statement and witness definition were unchanged. The next narrow compile exited 0 with no diagnostics.
2. Initial `Equivalence.lean` compile exited 0 with no diagnostics.
3. First final chain freshly compiled those two proof modules successfully, then `Checks.lean` exited 1 because the optional printing setting `pp.width` is not a registered source option in this toolchain. Its axiom commands printed the intended closures, but that failing process was not counted as successful verification. The setting was removed; no theorem or proof changed. The failed log is retained as `axioms-ppwidth-failed.log`, SHA-256 `a0560aab0cc7d28222fa5aa63a7852c2ad05183f7a0f3bf243f19d86a5978b59`.
4. The complete final chain was restarted from `CanonicalL.lean`; all three fresh compilations and raw-body replay passed, as recorded above.
5. Author source-to-consumer review rechecked both directions, simultaneous witness quantifiers, both rows, exact casts, all specified boundary cases, and the global-Hecke scope distinction. No unresolved mathematical blocker was found within this internal equivalence. This repeat check is **not** an independent review.
6. Existing F1 evidence and earlier substantive objections were read at their exact frozen version. Historical reports were neither overwritten nor converted into current acceptance. Non-author source-first reconstruction/reconciliation and designated Astra acceptance of the new packet remain pending.

## 7. Reproduction without setup or a whole-project build

Prerequisite: the exact pinned dependencies and existing root import snapshot are available. If not, root/dependency build preparation belongs to the integrator; P5 did not change the pins or run that setup.

From the repository root, run sequentially:

```sh
export LEAN_NUM_THREADS=2
out=.lake/build/lib/lean/ZInQKernel/Contrib/TYZEquivalence
mkdir -p "$out" .lake/build/p5
lake env lean -j2 -E warning -o "$out/CanonicalL.olean" \
  ZInQKernel/Contrib/TYZEquivalence/CanonicalL.lean
lake env lean -j2 -E warning -o "$out/Equivalence.olean" \
  ZInQKernel/Contrib/TYZEquivalence/Equivalence.lean
lake env lean -j2 -E warning -o "$out/Checks.olean" \
  ZInQKernel/Contrib/TYZEquivalence/Checks.lean
lake env lean -j2 --run scripts/audit_kernel.lean \
  .lake/build/p5/kernel-spec.json .lake/build/p5/kernel-report.json
```

The exact audit specification is below. Save these JSON bytes with a final LF as `.lake/build/p5/kernel-spec.json` for the recorded specification digest:

```json
{
  "modules": [
    "ZInQKernel.Contrib.TYZEquivalence.CanonicalL",
    "ZInQKernel.Contrib.TYZEquivalence.Equivalence",
    "ZInQKernel.Contrib.TYZEquivalence.Checks"
  ],
  "headline": {
    "declaration": "ZInQ.PropN.tyzInputs_iff",
    "type_declaration": "ZInQ.PropN.TYZEquivalence.Checks.exactStatement"
  },
  "exports": [
    "ZInQ.PropN.TYZEquivalence.canonicalL",
    "ZInQ.PropN.TYZEquivalence.canonicalL_cast",
    "ZInQ.PropN.TYZEquivalence.canonicalL_zero",
    "ZInQ.PropN.TYZEquivalence.canonicalL_one",
    "ZInQ.PropN.TYZEquivalence.canonicalL_ne_zero_iff",
    "ZInQ.PropN.TYZEquivalence.canonicalL_eq_zero_of_other",
    "ZInQ.PropN.TYZEquivalence.canonicalL_lemmaTwoEight",
    "ZInQ.PropN.TYZEquivalence.weightedParity_eq_lam",
    "ZInQ.PropN.TYZEquivalence.genusData_nonempty_iff_genusSums",
    "ZInQ.PropN.TYZEquivalence.canonicalL_genusData",
    "ZInQ.PropN.ParitySupportedContinuation",
    "ZInQ.PropN.ParitySupportedOrderOne",
    "ZInQ.PropN.tyzInputs_iff",
    "ZInQ.PropN.tyzInputs_iff_supportedOrderOne",
    "ZInQ.PropN.supportedOrderOne_of_readingA",
    "ZInQ.PropN.tyzInputs_iff_readingA_and_supportedContinuation",
    "ZInQ.PropN.supportedContinuation_of_hecke",
    "ZInQ.PropN.tyzInputs_of_readingA",
    "ZInQ.PropN.tyzInputs_and_hecke_iff",
    "ZInQ.PropN.TYZEquivalence.Checks.exactStatement",
    "ZInQ.PropN.TYZEquivalence.Checks.class5_domain",
    "ZInQ.PropN.TYZEquivalence.Checks.zero_and_one",
    "ZInQ.PropN.TYZEquivalence.Checks.canonicalL_values",
    "ZInQ.PropN.TYZEquivalence.Checks.no_zero_value_at_nonzero_rows"
  ],
  "targets": []
}
```

The final log digests include measured timings and therefore are run-specific; a fresh reproduction need not reproduce those bytes. The source/specification hashes and the formal statement, allowed-axiom result, declaration scope, successful replay and lack of skipped runtime declarations are the binding checks.

## 8. Integration, record-maintenance scope, and separate existing-file report

The present contribution is a proof-only, non-release packet. It proposes no new polynomial record and changes no current manuscript, application contract, audit register or bound historical source. Complete TeX/PDF release preparation, cumulative release synchronization, assembled headline review and protected acceptance publication do not apply to this worker's scoped delivery. The integrator must assess this scope and perform any newly triggered checks when integrating it. The audit-history self-test was not run here because none of its bound sources or records was changed; no hashes were refreshed to simulate acceptance.

**Separate report, not an edit:** `RouteK/PropN.lean:1520–1522` still describes `tyzInputs_iff` as not written in Lean. After reviewed integration, a maintainer can replace that historical status sentence with a reference to this new exact iff and the restricted continuation formulation. The new module is not yet imported by the existing root, and the current manuscript is untouched. `pn-design.md` contains historical scratch-stage proof counts and an optional global-Hecke split; those records must not be taken as the current iff type. The F1 proposal remains historical evidence, not an acceptance of this newly frozen code. No existing Lean statement needs a fix for P5.

Required next judgments are distinct: non-author review of this exact equivalence and its scope; integration against the same objects/conventions; any affected current-record updates and parent whole-project checks; and eligible Astra acceptance through the protected process. This packet supplies none of those judgments on its own.
