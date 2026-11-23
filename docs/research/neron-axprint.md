# Néron existence over the local DVRs

**Verdict.** `NeronDVRLocal` is proved on main by `NeronExt.dvrLocal_of_extension (ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind NeronDVR.neronSchemeExtensionDedekind_proof)`, with only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

The `LEAF; published` label is stale as a proof-status description at this revision. The earlier research note also lists local existence as still open. [Declaration docstring](../../ZInQKernel/Contrib/OneProof/NeronSchemeExtensionExists.lean#L382) · [Earlier research note](neron-ext.md#L148)

## Proof on the pinned base

Base commit `29bfbc3f6793d98b7c1ac637f9728fe51e701e5b`.

1. `NeronDVR.neronSchemeExtensionDedekind_proof` supplies Néron existence over affine Dedekind bases. [RelativeSquare.lean:83](../../ZInQKernel/Contrib/OneProof/NeronDVR/RelativeSquare.lean#L83)
2. `ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind` specializes the base to the ring of integers of the target number field and applies existence to the base-changed abelian variety. [MumfordGroupLawNeron.lean:78](../../ZInQKernel/Contrib/OneProof/MumfordGroupLawNeron.lean#L78)
3. `NeronExt.dvrLocal_of_extension` localizes that Néron model at each maximal ideal. The reverse bridge `extension_of_dvrLocal` has an additional `EGAIV_8_10_5_xii` premise. [NeronSchemeExtensionExists.lean:421](../../ZInQKernel/Contrib/OneProof/NeronSchemeExtensionExists.lean#L421) · [Reverse bridge at line 399](../../ZInQKernel/Contrib/OneProof/NeronSchemeExtensionExists.lean#L399)

Both imports built successfully. `lake env lean scratch/neron-axprint/Check.lean` accepted the composed term at type `NeronExt.NeronDVRLocal`. `#print axioms` returned the same three standard axioms for the composed term and all nine audited declarations. [Check.lean](../../scratch/neron-axprint/Check.lean) · [Axiom output](../../scratch/neron-axprint/axioms.txt) · [Declaration inventory](../../scratch/neron-axprint/log.md)

The manuscript invokes Raynaud’s semistable-reduction criterion via Silverberg–Zarhin Theorem 3.5. The source declarations identify the Néron existence statement with the Dedekind-scheme case of Bosch–Lütkebohmert–Raynaud, *Néron Models* (1990), §1.4, Theorem 3, and cite §1.2, Definition 1 for the mapping property. [Manuscript](../../diophantine_zq.tex#L816) · [Dedekind existence statement](../../ZInQKernel/Contrib/OneProof/MumfordGroupLawNeron.lean#L48) · [Local statement](../../ZInQKernel/Contrib/OneProof/NeronSchemeExtensionExists.lean#L382)

## Consumers and counts

- The library has one direct consumer at the pinned base. `NeronExt.extension_of_dvrLocal` takes `hloc : NeronDVRLocal` to recover the global number-field existence statement. [NeronSchemeExtensionExists.lean:399](../../ZInQKernel/Contrib/OneProof/NeronSchemeExtensionExists.lean#L399)
- The tracked scratch draft repeats that consumer at `scratch/neron-ext/Near.lean:380`. The dry-run text proposes a bundle field at `scratch/neron-ext/AutofoldDry.lean.txt:25` and supplies it to the bridge at line 38. [Scratch draft](../../scratch/neron-ext/Near.lean#L380) · [Dry run](../../scratch/neron-ext/AutofoldDry.lean.txt#L25)
- The O.7 consumers are on the separate `wip/rc-model-neron` ref and absent from the pinned main tree. They are `ZInQKernel/Contrib/OneProof/RC/ModelNeron/LocalExtension.lean:24` and `ZInQKernel/Contrib/OneProof/RC/ModelNeron/LocalTarget.lean:67,125`.
- `NeronDVRLocal` appears in neither count file. [kinds.tsv](../one-proof/kinds.tsv) · [OPEN.md](../one-proof/OPEN.md)
