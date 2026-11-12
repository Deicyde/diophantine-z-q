# Complete receiving revision 2 of the proposed 214 manuscript

This directory contains the complete operative receiving manuscript. Its frozen predecessor remains unchanged in `research/quartic214-manuscript/`; that earlier PDF is historical. The underlying polynomial, arithmetic proof sources and V16 foundation remain fixed at public commit e3626cac202cdbcdfedc2bff1978dcd3ea3fd3ab.

The receiving overlay repairs the lost M3 unit-group stars, groups the positive-real component correctly, explicitly chooses the primitive character's least conductor, and identifies the existing Deligne–Serre primitive-form argument at the current retained native consumer. It also corrects the catalogue description of the branch-reconstruction certificate and restores the twenty source-local F8–F11 group/field/scheme/form/point indices, conjugation inverse scope and composition maps. The original source text and historical verdicts are preserved; these changes require a separate current receiving decision.

`assemble.py` creates the full TeX and updated source map by exact bounded edits of the frozen complete predecessor. Original spans are retained; the foundation span is split around the operative native note and later locations are shifted. The output is a complete manuscript, not an errata-only supplement. `RECEIVING_OVERLAY.json`, `ADAPTATION.json`, `F7_APPLICATION.json`, `F8_F11_APPLICATION.json` and the author evidence state the exact changes, nine obligations and bounded related-use comparisons. Complete general semantic serialization review belongs to the independent reviewer.

```sh
python3 -B research/quartic214-manuscript-revision2/assemble.py --check
python3 -B research/quartic214-manuscript-revision2/build_pdf.py --check
python3 -B research/quartic214-manuscript-revision2/check_records.py --self-test --reviewed-artifacts
```

The PDF entrypoint reuses the frozen builder with the new target directory, preserving its serial lock, no-shell-escape invocation and 1GiB child ceiling. The record checker is standard-library-only, serial and capped at512MiB. It checks only declared transformations and byte/record consistency, with intended-reason negative controls. It does not supply mathematical acceptance, complete inventory/history coverage, reviewer eligibility or a protected-controller result. `--allow-unbuilt` is explicitly source-only and validates no PDF; it is not a release check.

A matching PDF and build record must follow the final source freeze. The manifest must be refreshed only after the changed applications and actual artifacts have been reviewed; updating hashes does not repair an invalid proof. Current navigation and the separate review/progress records identify the latest review state without relabeling earlier reports.

The required receiving receipt is authored independently at `research/quartic214-protocol-d-review/RECEIVING_REVIEW.json`, outside this artifact manifest to avoid a hash cycle. `--reviewed-artifacts` checks its actual accepted scope and exact artifact subjects; it does not authenticate the reviewer or infer App eligibility. Author checks may omit that flag while the independent decision is pending, and must report that narrower scope.
