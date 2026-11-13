# Version 17 artifact index

| Artifact | Purpose |
|---|---|
| [Current TeX](../../manuscripts/quartic_v17.tex), [current PDF](../../manuscripts/quartic_v17.pdf) | Complete numbered manuscript pair |
| [Source promotion](SOURCE-PROMOTION.json) | Exact front-matter changes and unchanged mathematical body |
| [Build](BUILD.json), [build adaptation](BUILD-ADAPTATION.json), [builder](build_pdf.py) | Source/PDF identity and bounded compilation |
| [Current profile](../../docs/current-manuscript.json) | Current display paths and byte bindings |
| [Current Version 17 guide](../../CURRENT_VERSION17.md) | Operative numbered-edition navigation |
| [Older revision 2 guide](../../CURRENT_214_REVIEW.md), [older revision 3 guide](../../CURRENT_214_REVISION3.md) | Superseded historical guides; their original bound bytes and former Version 16 status statement remain unchanged |
| [214 proof assembly](../quartic214/PROOF.md) | Arithmetic interfaces, domains and quantifiers |
| [214 construction](../quartic214/construction/) | Exact 214 IR, quartic table, statistics and checker |
| [Receiving revision 3](../quartic214-manuscript-revision3/) | Preserved mathematical promotion source |
| [Native review](../quartic214-native-review/) | Original source/use/finding records and additive current extension |
| [Version 16](../version16/README.md) | Preserved previous public edition |
| [Handoff base](HANDOFF-BASE.json) | Exact published cumulative archive and overlay selection policy |
| [Manifest](MANIFEST.json) | Complete immutable Git-tree inventory, raw blob hashes and modes, with verified base or overlay location |
| [Packer](pack_handoff.py), [handoff instructions](CUMULATIVE-HANDOFF.md) | Reproducible cumulative archive and readback checks |

The manifest is finalized only after the current public review records and navigation files are frozen. It excludes its own digest and the root checksum file from its internal file list; the archive's separate overlay manifest binds both. The final ZIP digest is an external checksum asset.
