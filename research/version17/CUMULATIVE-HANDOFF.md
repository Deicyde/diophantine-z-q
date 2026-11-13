# Version 17 cumulative research handoff

The historical base is the exact published [Version 16 cumulative archive](https://github.com/elliotglazer/diophantine-z-q/releases/download/quartic-222-version-16/z-in-q-version16-cumulative.zip):

```
bytes: 287551307
sha256: 703b75f3bf4eee5a94d2e7cd12fcab92fd6f8d101422cb4248b36afccf0b11d9
```

A local file with the same name but another size or digest is not an acceptable base. [HANDOFF-BASE.json](HANDOFF-BASE.json) pins this identity. The Version 17 packer preserves that ZIP unchanged under `historical/`.

The current inventory covers every regular file in an explicit immutable Git tree. The new manuscript, review and navigation paths must be staged in that tree before freezing. It therefore includes the intervening PR30 proof sources and evidence, not merely a retitled manuscript. The packer reads raw Git blobs with `git cat-file`, not worktree bytes or `git archive`; checkout newline conversion and export filters cannot change the packaged content. Genuine CRLF blobs remain CRLF, while LF blobs remain LF even on a CRLF checkout. Git executable bits are retained.

To avoid unnecessary duplication, a current file may be supplied by the historical base only when the packer has hashed the actual bytes at its effective Version 15/16 overlay location and found a byte and executable-bit match. Paths not established by that check are included in the new overlay, even if an older nested archive might also contain them. This conservative rule does not infer absence from an incomplete historical index.

Preserve the historical Version 16 ZIP and reconstruct it separately according to its own instructions. To obtain the exact current publication, populate a fresh directory with only the paths in `CURRENT-TREE.json`, taking new files from `overlay/` and unchanged files from their recorded historical member chains, and retain the listed executable bits. This leaves all historical files intact. A cumulative research workspace may keep extra historical files, but those extras are not part of the exact current Git tree. [MANIFEST.json](MANIFEST.json) binds the current inventory; `OVERLAY-MANIFEST.json` additionally binds the manifest itself and the root `SHA256SUMS` file. The external `.sha256` asset binds the completed ZIP, avoiding a circular self-hash.

After the public report and navigation bytes are final, stage the reviewed candidate and obtain its full tree object ID with `git write-tree`. From the repository root, use that immutable ID to inspect a plan and freeze:

```text
python -B research/version17/pack_handoff.py --tree TREE_BEFORE_MANIFEST --previous /path/to/published-version16.zip --plan
python -B research/version17/pack_handoff.py --tree TREE_BEFORE_MANIFEST --previous /path/to/published-version16.zip --freeze-manifest
```

Then update the checksum inventory, stage the new manifest and `SHA256SUMS`, and obtain the final tree ID. Build to a new path outside the checkout:

```text
python -B research/version17/pack_handoff.py --tree FINAL_TREE --previous /path/to/published-version16.zip --output /path/to/z-in-q-version17-cumulative.zip
```

The final tree must have exactly the same inventoried paths, blob IDs, bytes and executable bits as the pre-manifest tree; only the two excluded integrity files can differ. The packer refuses a different base, missing required staged additions, changed inventoried content, unsafe paths or an existing output. It verifies the nested historical digest and every new overlay file and mode by reading the completed archive. The final tree ID appears in `CURRENT-TREE.json` and the external build result, not in the self-containing manifest. The packer does not stage, publish, sign, commit or alter controller state. Conversation transcripts, host-session directories and credentials are outside the allowed selection.
