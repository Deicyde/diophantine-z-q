# D1: the numerical upper-break bound with both global leaves proved

## Exact contribution

`ZInQ.Contrib.ConductorBounds.D1_closed` supplies the two complete global literature-leaf arguments to the unchanged baseline `GlueConductor.D1_genuine`. The conclusion uses its genuine original global lower groups and Herbrand function:

```lean
∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
  (p : ℕ) [Fact p.Prime]
  (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
  (a : ℕ), 1 ≤ a → P.ramificationIdx ℤ ≤ a.factorial →
  ∀ (b : ℕ), GlueConductor.ramGroup L P b ≠ ⊥ →
    GlueConductor.phi (GlueConductor.ramCard L P) b ≤ 4 * a ^ 2
```

All fourteen original residual binders remain, including the Galois assumption, the actual prime above `(p)`, the factorial ramification bound, positivity, and nontriviality at the original lower index. The only omitted inputs are the two literature leaves, now supplied by their proved global contributions. No local model, desired comparison, unrelated group cardinality or hidden Fact assumption replaces them.

This is a thin numerical conductor lemma, not H, a height bound, a complete arithmetic assembly, a polynomial record, manuscript/PDF incorporation, registry adoption or independent acceptance.

## Actual suppliers and consumer identity

- **Global Hilbert formula:** `ZInQ.Contrib.HilbertDifferent.hilbertDifferentFormula : GlueConductor.HilbertDifferentFormula`. Its source is from global PR58 head `11a2303f0a707553465613c75f3124de298c89d0`, not the earlier LOCAL PR55 theorem. GlobalFormula source SHA-256 `eddc3026ed0a627c73bc03e053e0fa234cc3db4da5fe8c5a93288b6e6a65566f`. It concerns the original absolute different in `𝓞 L`, all original lower indices and actual global Galois actions.
- **Global Serre bound:** `ZInQ.Contrib.DifferentBound.serreDifferentBound : GlueConductor.SerreDifferentBound`. The exact eighteen DifferentBound source files are the frozen public core PR56 head `fcc6b75d4aecdd112ca15e1ba8eed237fb2b34bf`. The common twenty-seven GlobalDifferentTransport source files are byte-identical in both bundles; no producer body is changed.
- **Original consumer:** `GlueConductor.D1_genuine`, `ZInQKernel/HDecomp/Conductor/Breaks.lean:363–404`. The numerical argument derives `P≠⊥` from the actual prime-over-prime assumptions, uses the Hilbert cutoff to place the nontrivial lower index below it, identifies actual inertia order with ramification index, compares the two genuine different-power statements and invokes the unchanged arithmetic `upper_break_le`.

The supplied objects are exactly the ones consumed in this existing proof. The Hilbert statement covers the Galois field/prime used by D1; the Serre statement is stronger than needed and covers the same number field and prime. No additional arithmetic route is introduced.

## Same-tree source and kernel validation

The validation used one complete physically merged project import namespace, not partial competing `LEAN_PATH` roots. All forty-three global Hilbert/transport sources and the eighteen exact DifferentBound sources are explicitly available in this contribution tree. The latter eighteen sources and the new D1 module were freshly source-compiled sequentially with Lean 4.35.0, two threads per gated compiler. The former sources/objects are the unchanged exact-head global T20 normal candidate; their earlier validation is separate evidence, not a new D1 full-normal replay.

A private independently expanded residual proposition was compared with the actual stored D1 type using `Kernel.isDefEq`. The baseline consumer's first two binders were checked against the literal original leaf types and instantiated with the actual closed global supplier constants; its **entire remaining type** was then compared with D1. Both comparisons passed. The provider has no universe parameters and exactly fourteen residual binders.

The actual proof body directly references **both** global supplier constants and the original `D1_genuine`, with no self-reference. At kernel trust zero, `Kernel.check` inferred its exact type and the raw proof body was re-added under a fresh diagnostic name, retaining the original type, body and universe data. The actual type-and-body dependency walk visited **43,659** declarations and found only:

```text
propext
Classical.choice
Quot.sound
```

This is a dependency/axiom walk, not a claim that every imported library body was independently manually reviewed or newly replayed here. The new D1 body is checked; the full core normal/public-CI validations remain separately source-bound. No second T20/T21 root/normal gate is claimed.

Negative controls compiled an extra-Hilbert-leaf version and an extra-universe/type version and rejected both by the whole-type check. A deliberately corrupted actual proof body was rejected with `declTypeMismatch`. The first two private-verifier runs had a record-update parser error and an explicit UInt32-to-Nat output-field mismatch; their exact failed sources/logs remain preserved. Those are verifier infrastructure failures, not contributed proof repairs or accepted runs.

## Scope, chronology and reproduction

The original five headline premises remain open. Existing preliminary reviews are not designated Astra acceptance; serving identity is unknown. No protected definition, compiler/dependency pin, root import, checker, registry, policy, current manuscript, TeX/PDF or historical review is changed. No merge or human outreach is authorized by this note.

Older global-open LOCAL Hilbert and pre-extension Serre notes retain their exact bytes and historical scope. Their completion is supplied by the separate global continuations, not by rewriting the old evidence. The D1 module's draft header was replaced only after the successful same-tree check; its imports and complete theorem/diagnostic suffix stayed byte-identical. Final source/object bindings are checked again before committing.

A full-source reproduction uses this self-contained contribution tree with the unchanged pinned dependencies and stock `python3 -B scripts/check_kernel.py --output build/d1-normal`; no new package, toolchain or hidden source module is needed. Public CI on the actual D1 PR is a separate required stage, not inferred from PR55, PR56, PR58 or this private smoke test. Portable private typed fixtures and actual negative-control/run receipts are retained with the evidence packet.
