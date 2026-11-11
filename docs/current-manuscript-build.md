# Build the current manuscript

The [current manuscript profile](current-manuscript.json) identifies the versioned TeX entry point, required local project inputs, committed PDF and recorded build. Every official new record must update this profile and meet the [complete-manuscript requirement](release-policy.md#complete-manuscript-required-for-every-official-record).

Run from the repository root:

```sh
python -B scripts/check_current_manuscript.py
python -B scripts/build_paper.py
```

The first command checks the required files and their bindings. The second validates the profile and rebuilds its current TeX with the pinned Tectonic engine and bundle, writing the generated PDF, logs and report under `build/paper/current/`. It does not replace the committed PDF or silently build a historical edition.

These checks do not establish mathematical completeness or authenticate a build record supplied by a contributor. Engine platforms and PDF timestamps can affect binary identity. The build report states the actual comparison with the committed PDF. Required independent review must establish that the supplied PDF corresponds to the reviewed source and contains the complete current argument.

The [earlier build guide](building.md) is preserved as part of the exact Version 16 review record. Its statement that `scripts/build_paper.py` always builds Version 14 describes the earlier script and is superseded by this guide. Its historical construction commands retain their stated scope.

## Preparing a new candidate

The profile checks expect the candidate TeX, PDF and build record to exist. First build the new source with the pinned Tectonic engine and bundle and retain its real command, source hash, input hashes and output hash. Package the resulting PDF at its versioned release path and create the corresponding release build record. Then update the current manuscript profile and run the checks above. Do not fabricate a successful build record to satisfy the preflight.

The generated `build-report.json` is rebuild evidence, not a replacement for the release build record: its PDF field names the build output, and its bundle field is `bundle_url`. The profile-bound release record must identify repository-relative `source` and `pdf` paths, their SHA-256 hashes, `engine`, `bundle`, and actual `tex_errors` and `unresolved_references` results. Independent review must check the packaging and source/PDF correspondence.
