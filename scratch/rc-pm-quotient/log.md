# Results

## Initial draft

- Base merge: 164fadfa60c0f3fee3eb1866a0dd5bf23e5679fc and 77255b723c39631f737224bb96e3393b79b6bc7c.
- Citation verdict: tex 1784–1788 (Milne) and 8468–8474 (Jetchev–Kane), recorded and committed.
- No new print. At the base pins, the reviewed Manin–Drinfeld source transcript is in `RC/PrintsArith/Heegner.lean`.
- Model: Néron extension of fixed `π`, actual residue point reading, additive degree-zero quotient and Frobenius compatibility.
- Operators: normalized cusp, generic signed and Hecke identities specialized on the same quotient.
- CM: contracted place and exact detector residue embedding, source and target diagram, `hπ` through `GoodReduction.hpi_of_integralDiagram`.
- Cusps: actual rational moved cusp image, Manin–Drinfeld, fixed annihilator, additive reduction.
- Assembly: total selector, pinned newform, actual row and focused dependent `#discharges` audit.
- Verification: serial builds under 60 GB user scopes, host load/memory gate. Source-matched dependencies available. Automatic review rejected a build while another lane's Lean process was active; later build attempts were guarded on host process exit.
- Initial `lake build`, Model: FAIL (Frobenius rewrite and model field elaboration in the first draft). Source edits applied; no revised module ran before handoff.
- Operators, Cusps, CM, Assembly, focused `#discharges`: NOT RUN (Lean process gate; no Model artifact).
- Axiom audit: NOT VERIFIED. Static source check: no `sorry`, `admit`, axiom declaration, local notation, or import of `OneProof.Main`; whitespace check passed.

## Continuation

- Citation errors at tex 1784–1788 and 8468–8474 carried forward in `.fleet/rc-pm-quotient2-verdict.md`.
- The first workspace build could not reach the user scope from the sandbox. It ran with escalation but started missing prerequisites in parallel; stopped that scope. The subsequent focused Lake builds use source-matched prerequisites, a private compiler lock, the load/memory gate and a 60 GB user scope.
- `Model`: PASS after parenthesizing the integral endomorphism type and fixing the coerced Frobenius subtraction. Its five axiom prints list only `propext`, `Classical.choice`, `Quot.sound`.
- `Operators`: PASS. The identity section is smooth; the Hecke branch sum uses a general list-to-finite-sum lemma. `specialFibre`, `specialize_eq_value`, and both operator proofs passed the axiom check.
- `Cusps`: PASS. `hCusp` has only the standard three axioms.
- `CM`: PASS. The residue map uses the valuation ring contracted along the selected datum embedding. `hPM` is discharged by the computed readout and the source section comparison.
- `Assembly`: PASS. Explicit dependent selector arguments fix elaboration. `hpiAt` uses the actual Artin label and `StageKummer.reduceDatum`; `hCuspAt` uses the same signed family. The constructor has only the standard three axioms.
- Axiom audit: PASS. All 25 printed checks (21 theorems including the private branch-sum lemma, and four definitions) return only `propext`, `Classical.choice`, `Quot.sound`.
- Focused `#discharges`: PASS. Conclusion definitionally equals the type of `Wiring.PreLeaves.odd_staged` at `SelectorTotal.withParamIndices a`. Actual `Wiring.Leaves` imported; no `OneProof.Main` import.
- The audit prints 30 binders. In order (square brackets are instances):
  `ℓ`, `W₀`, `a`, `L`, `s`, `[NeZero (newformLevel (Ecurve ℓ))]`, `F`,
  `[NeZero (StageKummer.level ℓ)]`, `[((EcurveZ ℓ)⁄ℚ).IsElliptic]`,
  `π`, `hQ`, `han`, `R`, `[∀ i, CommRing (R i)]`, `[∀ i, Algebra (R i) ℚ]`,
  `m`, `hN`, `hcop`, `H`, `hm`, `ap`, `X`, `J`, `G`, `relations`, `cusps`,
  `refs`, `ha`, `hL`, `hsign`. No free special fibre, quotient, `hπ`, or `hCusp` binder.
