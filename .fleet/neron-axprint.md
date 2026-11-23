# Néron DVR existence audit

The local Néron existence `LEAF; published` label is stale at the pinned main base `29bfbc3f6793d98b7c1ac637f9728fe51e701e5b`. Lean accepted the closed term `NeronExt.dvrLocal_of_extension (ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind NeronDVR.neronSchemeExtensionDedekind_proof)`. `#print axioms` returned only `propext`, `Classical.choice`, and `Quot.sound`. [Axiom output](../scratch/neron-axprint/axioms.txt)

The pinned library consumes the proposition in `extension_of_dvrLocal`. The O.7 consumers are on a separate branch. The proposition appears in neither count file. [Research report](../docs/research/neron-axprint.md)
