# Source reuse and changes

The complete proof in `ZInQKernel/Contrib/OneProof/TYZThm33.lean` is reused from the existing project contribution at:

- Revision: `d489fc13f1eadba5ca95d61b8f455cd2b0e7c402`.
- Original file: https://github.com/Deicyde/diophantine-z-q/blob/d489fc13f1eadba5ca95d61b8f455cd2b0e7c402/ZInQKernel/Contrib/OneProof/TYZThm33.lean
- Original Git blob: `84af2d4bb7404555d24699f08ac2a97466f1c466`.
- Original SHA-256: `fd62d9bc7d1d3338aa23ca64f2f8965691c4c09cd37f0de2f85909ac4d900a52`.
- Original size: 44,219 bytes.
- Original report: https://github.com/Deicyde/diophantine-z-q/blob/d489fc13f1eadba5ca95d61b8f455cd2b0e7c402/docs/research/h33-dict.md

This is reuse of the completed reduction, not a new proof of the Gross–Zagier formula. Attribution to the original project contribution and its dependent sources is retained. The original proof history is preserved; no historical commit is amended or represented as scrubbed.

## Changes to the source

All pre-existing imports, named declarations, definition bodies and proof bodies are preserved. Changes are:

1. Comment-only revision/provenance information, replacing the original operational header with the immutable source reference.
2. Comment-only correction distinguishing the Lean reduction steps from the standard analytic-to-algebraic interpretation of `IsX0Identification` and the modular-curve/component dictionary.
3. Comment-only exact arXiv v1/journal comparison, edition and page references. The original report's lack of a journal reading remains a historical fact, not a claim about this new reading.
4. One new conditional theorem:

```lean
theorem CloudB3SC7H33.h33_proof
    (hCM : T5Glue.ShimuraMainCM)
    (hPrinted : ZInQ.Contrib.TYZGenus.H33Dict.TYZThm33Printed) :
    ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33 :=
  ZInQ.Contrib.TYZGenus.H33Dict.tyzThm33_of_printed hCM hPrinted
```

The source was compared with the original after lexical removal of comments, with the new export excluded. This is a source-preservation check, not a compiler or imported-kernel replay certificate.

## Dependencies and notices

No dependency pin, existing module, target definition or assembly is changed. The existing source's imports are retained; no additional library is vendored. Existing dependency copyright, license and attribution material remains applicable and is not relicensed by this contribution. The external sources read during the bounded supplier search are references only, not newly ported proof code.

The public claim starts from main `0caafe66103a89994198e26d8d68af6ae227ed0e`. Its claim-only commit `e75670ff8e85f9d958d720e026df9d26e388299f` remains in history.

AI assistance supplied the immutable-source recovery, printed-source comparison, new conditional export and check preparation. Source interpretation is AI-READ and does not clear human-reading flags. Fresh compiler evidence and independent review must be reported separately.
