# Version 18 artifact index

| Artifact | Purpose |
| --- | --- |
| [Complete TeX](../../manuscripts/quartic_v18.tex), [PDF](../../manuscripts/quartic_v18.pdf) | Full argument and printed tables |
| [Build record](BUILD.json), [builder](build_pdf.py), [profile](../../docs/current-manuscript.json) | Actual source/PDF identity and build inputs |
| [Selected 196 table](../../quartics/quartic-196-symbolic-coefficients.json) | Complete unbalanced quartic, with the fixed `A` specified by the manuscript |
| [196 reproduction](196/REPRODUCTION.md), [source pins](196/provenance/SOURCE-PINS.json) | Original Brox sources, portable independent reconstruction and scope |
| [196 elimination](196/proof/elimination196.tex), [theorem](196/proof/theorem196.tex), [printed rows](196/tex/q196-rows.tex) | Components incorporated into the complete manuscript |
| [Parent 198 table](../../quartics/quartic-198-symbolic-coefficients.json), [reproduction](198/REPRODUCTION.md) | Retained parent construction and independent checker |
| [Parent package pins](198/provenance/PACKAGE-PINS.json), [complete source package](198/upstream/H10-quartic198/) | Unchanged supplied package and upstream attribution |
| [Parent arithmetic component](arithmetic-component/arithmetic198.tex) | Arithmetic proof incorporated into the manuscript |
| [Busy Beaver component](height-bb/q198bb-proof.tex) | Uniform parameter selection and coefficient bound, incorporated into the manuscript |
| [Dependency pins](dependencies/SOURCE-PINS.json) | Source identities used by the dependency inventory |
| [Current inverse dependency](../../docs/research-review/version18-inverse-dependency.md) | Exact supplier, conventions, derivation and source-version qualifications |
| [Release notes](RELEASE-NOTES.md), [reproduction guide](REPRODUCTION.md), [handoff guide](CUMULATIVE-HANDOFF.md) | Changes, commands and archive preparation |

The complete manuscript is authoritative for the current argument. Source-component files and earlier audit reports retain their original scopes. A finite check or a component approval is not acceptance of the full arithmetic argument, source/PDF pair or release. The release manifest must record the actual final review and publication state; no draft template is an acceptance record.
