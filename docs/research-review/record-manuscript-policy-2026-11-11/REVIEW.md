# Complete-manuscript policy review

Accepted within the policy and software scope in `REVIEW.json`. The review binds the eleven exact Git blobs in `STAGED-CHANGES.json`, SHA-256 `be7bf41769420713e765e9685ea780c043b736f8bfd5fb342a23a015c5912aaf`, staged tree `9f628c6b0ee49bcee4d302308f0776af3e957021`, based on `39182bffc48c0412b2888d9d28f1ca138a2004e7`.

The policy requires a complete updated TeX project and matching PDF for every official new record. It requires the complete integrated project argument, exact build provenance and independent review of the pair and assembled proof. Contributors can submit short notes; maintainers must integrate them before record promotion. No milestone threshold remains in the active policy.

The validator checks declared artifacts, input hashes, edition and build-record correspondence. The builder uses the declared current source, stages its declared inputs, keeps historical outputs and the published PDF intact, and reports actual binary comparison. It rejects unsafe paths and output overlap before installing or running the engine. Documentation accurately separates these checks from mathematical completeness and from authenticating supplied build evidence.

I ran 15 focused tests: 14 passed and one symlink-creation test was skipped because Windows denied creation. Current-profile validation passed. The actual cached build succeeded before the final output-only preflight guard; that guard passes for the current profile and has a negative overwrite test. Published and rebuilt PDFs each have 549 pages; all decoded page content streams and page geometries match. All extracted page texts also match; extraction lacks optional fontTools support and is supplementary evidence. Details are in `PDF-COMPARISON.json`. Their binary hashes differ. This comparison does not establish full rendered equivalence or inspect every resource, link, bookmark or metadata item.

The review raised option-like source names and unclear release-record packaging. The implementation now passes `./name`, and the guide explains genuine first-build evidence and release-path packaging. Another reviewer checked the argument repair. The author separately added the reserved-output overlap guard, which I reviewed.

The manuscripts, `research/version16`, historical build outputs and `docs/building.md` remain unchanged. The separate frozen Version 16 checkout is clean. This is a non-record policy/build change, so it needs no new cumulative research ZIP. Future official records must satisfy the new rule.

There are no remaining defects within this scope. This report supplies no new mathematical, controller, required App, merge or release acceptance.
