# Historical manuscript gate after the main merge

The frozen 214 manuscript manifest and its scoped reviewer receipt bind the old root README and the old manuscript workflow. Main adds a four-line Lean contribution note to the root README. The active historical workflow therefore cannot validate that README as if its old bytes were still current.

This continuation preserves the original manifest, checker, reviewer receipt and every mathematical/artifact input. The two exact historical navigation/CI files are retained under `historical/`. Before invoking the unchanged original validator, the wrapper verifies that the current README is exactly the historical README plus the four-line note, and that the current workflow differs only by the wrapper command and its new directory trigger. No arbitrary override is exposed to callers. Every other original binding is read against the actual current repository.

The workflow now runs:

```sh
python3 -B research/quartic214-main-integration/check_historical_records.py --self-test --reviewed-artifacts
```

This requires a separately authored `REVIEW.json` for the exact new continuation, wrapper, historical copies and current files. The original scoped acceptance stays bound to its original bytes and retains its incomplete whole-proof status. The new receipt checks this limited integration; it does not renew mathematical acceptance or attest controller eligibility. `--author-check` exists only to test the proposed implementation before that independent decision and is never the workflow command.

The main additions and the new .gitattributes kernel patterns have their own scope. They do not change the retained manuscript's mathematics, and this wrapper does not validate Lean proofs or claim that it reviews the whole main merge. The separate current revision2 and progress gates remain active.
