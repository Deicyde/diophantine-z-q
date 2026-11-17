# Version 19 cumulative handoff

The release archive contains the immutable release tree and the exact published
[Version 16 cumulative archive](https://github.com/elliotglazer/diophantine-z-q/releases/download/quartic-222-version-16/z-in-q-version16-cumulative.zip).
That historical base is 287,551,307 bytes with SHA-256
`703b75f3bf4eee5a94d2e7cd12fcab92fd6f8d101422cb4248b36afccf0b11d9`.
The overlay preserves the later released manuscripts and includes Version 19's
complete source/PDF pair, selected construction inputs and independent finite
checkers. Historical manuscript bytes are not rewritten.

`pack_handoff.py` reads raw Git blobs from an explicit immutable tree. It retains
executable bits and omits an overlay file only when the historical archive
supplies identical bytes and mode. It verifies every selected member after
packing. `HANDOFF-BASE.json` records the historical layers and required additions.

The final inventory and root checksum list are derived after merge in an
isolated index; they are the only two cycle exclusions. The archive's
`ARCHIVE-SOURCE.json` release asset identifies the reviewed source commit and
the derived archive tree. `CURRENT-TREE.json` inside the ZIP lists every current
file and its exact delivery location. Reconstruct that listed tree in a fresh
directory, following the recorded historical member chains and preserving the
listed modes. Keep the original historical ZIP intact.

Publication follows actual protected acceptance of the final source/PDF pair.
The release assets record the observed App check, both reviewer decisions,
archive size and hash, and post-merge checks. This guide does not itself assert
that a candidate has passed review or that an archive has already been published.
