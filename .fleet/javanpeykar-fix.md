# javanpeykar-fix (2026-11-16)

**Result.** `javanpeykarBound` is proved from printed leaves only. Only the standard axioms are used:

`JavanpeykarFix.javanpeykarBound_of_printed_fix : JavanpeykarPrintedMap → ConstantFieldExtensionUnramifiedFull → UniformizationLeafAll → MumfordTorsionAlgClosed → JavanpeykarBound`

The file is `ZInQKernel/Contrib/OneProof/JavanpeykarFix.lean`; the helpers are in `JavanpeykarFix/{Basic,BelyiMap}.lean`. The last two hypotheses are existing textbook fields that give T35.

The review's four GLUE steps of javanpeykar-dict's leaf are all closed:
- **(a)** The leaf is restated over height-dict's `IsPrintedStableHeight`. The proof goes through `isPrintedStableHeight_of`.
- **(b)** The leaf now takes a Belyi *map* `β : X → ℙ¹ = Proj ℚ̄[X₀,X₁]`: finite, ramification index 1 at closed points over `D₊(X₀X₁(X₀−X₁))`, degree read from the generic stalk.
  - The glue "Belyi function ⇒ Belyi map" is proved in full (`belyiMapOfFunction_proof`).
  - The proof uses the valuative extension, finiteness from finite fibres, the residue field at closed points, the Belyi property at `𝒪_{C,x}`, and the degree via the generic stalk.
- **(c)** The leaf assumes `X` projective. "Smooth proper integral curve ⇒ closed immersion into ℙⁿ" is proved (`exists_closedImmersion_projectiveSpace`), from the vendored Chow lemma plus the valuative extension.
- **(d)** The leaf takes `Jac(X)` as a tensor-compatible `Pic⁰_{X/ℚ̄}` representative with a model `V/K`. Existence is proved (`exists_jacBar`), via the vendored `baseChangeIso`.

The Stichtenoth leaf is restated with the full-constant-field hypothesis (`ConstantFieldExtensionUnramifiedFull`). That hypothesis is proved at the consumer from `K(X) ⊗ K̄ ≅ K̄(X_K̄)` (`fullConstantField_of_bijective`).

**Compiles (VERIFIED).**
- `lake build` of the Contrib module succeeds.
- `#discharges`: the field is discharged by `javanpeykarBound_of_printed_fix` with standard axioms (`scratch/javanpeykar-fix/Discharges-output.txt`).
- The autofold spec is `scratch/javanpeykar-fix/autofold.json`. Its dry run exits 0, with strict count `34/11 on 45 -> 35/11 on 46`. That is GLUE −1 against the re-rated base, where `javanpeykarBound` counts as GLUE.
- The generated module compiles: `sixContactMin_of_open36` uses only the standard axioms.

**Leaves.**
- `JavanpeykarPrintedMap`: printed form, flagged unread.
- `ConstantFieldExtensionUnramifiedFull`: printed form, flagged unread. Stichtenoth's theorem number (3.6.3(a)) is UNVERIFIED.

**Remains.**
- Human reading of both leaves.
- height-dict's definition-level readings R1-R3 of the printed height.
- `locators.md`, `kinds.tsv` and `OPEN.md` rows for the integrator (proposed in `docs/research/javanpeykar-fix.md` §6).
