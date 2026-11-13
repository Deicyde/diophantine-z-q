/-!
# Notice: vendored Tau Ceti code

The modules under `ZInQKernel/Contrib/TauCeti/` (module prefix `ZInQKernel.Contrib.TauCeti.`) are
copied from **Tau Ceti**, a Lean 4 library downstream of Mathlib:

* repository: https://github.com/TauCetiProject/TauCeti
* commit: `5a01f5fe3621126cccf9ba22e700493cbc7b7156` (2026-10-17, the last Tau Ceti commit on
  Lean v4.35.0)
* license: Apache License 2.0
* authors: The Tau Ceti contributors

Each vendored file keeps its Tau Ceti copyright header and carries a provenance line naming the
commit and the original module. Declaration names and namespaces are unchanged. The only
mechanical change is the rewriting of `import TauCeti.X` to `import ZInQKernel.Contrib.TauCeti.X`.

1118 modules are vendored: the 397 modules of the import closures of the Chebotarev density
theorem (`NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet`) and of
`NumberTheory/NumberField/LocalGlobal/Different/{Exponent,Permutation}`, plus 721 modules of the
Kronecker–Weber closure that exist at this commit (class field theory and its prerequisites).

Local changes, made so that the code compiles against this project's Mathlib (commit 56a00585,
a few days older than the Mathlib Tau Ceti used), are listed one line per file in
`docs/research/tc-port.md`. They are: eight vendored files edited (a renamed `Sylow` field, the
explicit arguments of `Is*Apply` classes, one `rfl`, one import), and one new file
`MathlibBackport/Sylow.lean` that supplies `Sylow.maximal_isPGroup`, a Mathlib declaration newer
than our pin.

Every constant declared in these modules depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound` (audited by `scratch/tc-port/AllKW.lean`).

This file contains no declarations.
-/
