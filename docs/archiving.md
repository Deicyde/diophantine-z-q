# Citation and archival release

Use [CITATION.bib](../CITATION.bib) for the 11/5 manuscript and the dated research handoff. The author field is intentionally omitted at the maintainer's request. The 11/5 manuscript itself also retains its blank author field.

There is no `CITATION.cff` because the [CFF 1.2 schema](https://github.com/citation-file-format/citation-file-format/blob/main/schema.json) requires an author record. This repository does not invent a personal or organizational author to satisfy that requirement.

## DOI status

No DOI has been minted or claimed. The repository is public. The release tag, commit hash, source manifests, and SHA-256 checksums currently identify the materials.

For the eventual public release:

1. Complete the original-work license choice and the historical archive's third-party rights review.
2. Select the exact repository commit and the artifacts to preserve. Identify the 10/11 manuscript, 11/5 manuscript, and curated reproducibility package explicitly in the deposit inventory; do not assume an external service will preserve linked assets automatically.
3. Connect the maintainer's archival account, for example through [Zenodo's GitHub integration](https://help.zenodo.org/docs/github/enable-repository/), or make a manual deposit. Review how the service represents a work with no named author before supplying creator metadata.
4. Reserve or obtain the DOI through that service, publish only when the public release is authorized, then add the actual DOI to `CITATION.bib` and the README.
5. Verify the deposited file hashes against the local release and retain the deposition record alongside the release notes.

GitHub release creation and DOI registration are separate actions. Preparing this repository does not create an archival record or connect a Zenodo account.
