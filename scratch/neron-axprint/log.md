# Néron declaration inventory

The pinned `origin/main` tree is `29bfbc3f6793d98b7c1ac637f9728fe51e701e5b`.

```sh
base=29bfbc3f6793d98b7c1ac637f9728fe51e701e5b
git grep -nE '\b(NeronDVRLocal|NeronSchemeExtensionExists|NeronSchemeExtensionDedekind)\b' "$base" -- '*.lean'
git grep -niE '(neronDVRLocal|neronSchemeExtension(Exists|Dedekind))[[:space:]]*(:=|:)' "$base" -- '*.lean'
```

## Theorems that return the audited propositions

| Declaration | Source | Hypotheses | Result |
| --- | --- | --- | --- |
| `NeronDVR.neronSchemeExtensionDedekind_proof` | `ZInQKernel/Contrib/OneProof/NeronDVR/RelativeSquare.lean:83` | None | `NeronSchemeExtensionDedekind` |
| `ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind` | `ZInQKernel/Contrib/OneProof/MumfordGroupLawNeron.lean:78` | `h : NeronSchemeExtensionDedekind` | `NeronSchemeExtensionExists` |
| `NeronExt.dvrLocal_of_extension` | `ZInQKernel/Contrib/OneProof/NeronSchemeExtensionExists.lean:421` | `h : NeronSchemeExtensionExists` | `NeronDVRLocal` |
| `NeronExt.extension_of_dvrLocal` | `ZInQKernel/Contrib/OneProof/NeronSchemeExtensionExists.lean:399` | `hpr : ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii`, `hloc : NeronDVRLocal` | `NeronSchemeExtensionExists` |
| `ZInQ.Contrib.NeronC.neronSchemeExtensionExists_of_neronModelExists` | `ZInQKernel/Contrib/NeronC/NeronGroup.lean:115` | `h : ZInQ.H5Neron.NeronModelExists` (T41) | `NeronSchemeExtensionExists` |
| `NeronDVR.neronSchemeExtensionDedekind_of_relativeSquare` | `ZInQKernel/Contrib/OneProof/NeronDVR/RelativeSquareReduction.lean:160` | `square : NeronDVR.RelativeSquareStrictNeron` | `NeronSchemeExtensionDedekind` |
| `NeronDVR.neronSchemeExtensionDedekind_of_strictHenselizationDescent` | `ZInQKernel/Contrib/OneProof/NeronDVR/StrictHenselization.lean:63` | `descend : NeronDVR.NeronDescentFromStrictHenselization` | `NeronSchemeExtensionDedekind` |
| `NeronExtDedekind.neronSchemeExtensionDedekind_of_dvr` | `ZInQKernel/Contrib/OneProof/NeronDedekind.lean:94` | `hDVR : ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDVR` | `NeronSchemeExtensionDedekind` |

The reverse bridge in the last row is `ZInQ.Contrib.GroupLawNeron.dvr_of_dedekind` (`ZInQKernel/Contrib/OneProof/MumfordGroupLawNeron.lean:74`). It takes `h : NeronSchemeExtensionDedekind` and proves the general `NeronSchemeExtensionDVR` proposition. The latter is a separate proposition from `NeronExt.NeronDVRLocal`.

The three proposition definitions have type `Prop` and have no parameters. Their sites are `ZInQKernel/Contrib/OneProof/NeronSchemeExtensionExists.lean:390`, `ZInQKernel/Contrib/NeronC/NeronGroup.lean:82`, and `ZInQKernel/Contrib/OneProof/MumfordGroupLawNeron.lean:56`, respectively.

The lower-case `neronSchemeExtensionExists` and `neronSchemeExtensionDedekind` field declarations supply assumptions in older bundles. Applying their generated projections requires a proof of the enclosing bundle. The field sites can be reproduced with `git grep -nE '^[[:space:]]+(neronDVRLocal|neronSchemeExtensionExists|neronSchemeExtensionDedekind) : ' "$base" -- '*.lean'`. The case-insensitive search for uses of `neronDVRLocal` found no corresponding field in a Lean file at this revision.

The tracked draft `scratch/neron-ext/Near.lean` defines the same fully qualified names in a separate environment (`NeronDVRLocal` at line 371, `extension_of_dvrLocal` at line 380 with the local statement and EGA premise, and `dvrLocal_of_extension` at line 402 with the global existence premise). `Check.lean` uses the library declarations. The draft has its own axiom queries at lines 426–427.

`ZInQKernel/OneProof/H/TailZ99.lean:63` supplies the Dedekind theorem to the previous research bundle. The surrounding theorem at line 59 takes an `OpenResearchLeaves73` and returns `OpenResearchLeaves72`. `ZInQKernel/OneProof/Main.lean:223` documents the discharge.

## Kernel check

Both `lake build` commands succeeded, for `+ZInQKernel.Contrib.OneProof.NeronDVR.RelativeSquare` and `+ZInQKernel.Contrib.OneProof.NeronSchemeExtensionExists`, followed by `lake env lean scratch/neron-axprint/Check.lean`. The commands ran sequentially with a 60 GB memory limit. The build reused artifacts from a cache with identical Lean configuration and tracked sources throughout the imports. [Axiom output](axioms.txt)
