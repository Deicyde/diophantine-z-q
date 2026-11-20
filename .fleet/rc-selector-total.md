# rc-selector-total — fork issue #83

Implementation and report commit: 95d66e20790a66847cf0e53e5ddd9c4644542fad

`SelectorTotal.oddStagedOfParamValues` gives
`Nonempty (OddStagedInstance (withParamIndices a))`, the type of
`PreLeaves.odd_staged` at the data with the two parametrization indices
installed. `genusInstance` builds the instance using the raw genus and
ring values, with `hjg` and `hjr` by reflexivity. Its conductor-one
selector covers every admissible row, including torsion rows.
`pointInputs` supplies the selection equation to `oddStagedActual` from
the actual stage setup. No existing Lean files or prints changed.

`SelectorTotal/Assembly.lean` and `scratch/rc-selector-total/Axioms.lean`
compiled with serial `lake env lean` under the 60 GB memory cap. All
eleven audited declarations depend only on `propext`, `Classical.choice`,
and `Quot.sound`.

The integrator supplies the fixed stage setup and geometry for the new
instance, the reference data and pointwise `hCM` and `hπ`, the Atkin sign
and cusp proofs, the torsion and odd-sign proofs, and the phase reading
for `W.aθ`. The genus inputs include existing `Prints`, rationality of the
chosen `κ`, and one `CMFieldOfDefinition` proof on `X0Branch.model` shared
with the Heegner anchor residual. The report lists all inputs and their
owners. Inherited source scope issues for Milne and Jetchev–Kane are
recorded there; no new source error was found.

Report: `docs/research/rc-selector-total.md`.
