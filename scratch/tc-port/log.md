# tc-port results log

## Step 1 (VERIFIED)
- tcport.py ~/tc-oct16 (5a01f5fe3621) port1.txt: copied 397 files. Commit 9c0a5684.

## Step 2 (VERIFIED, read ~/tc-oct16/lakefile.toml)
- Tau Ceti leanOptions: weak.linter.mathlibStandardSet = true, weak.linter.style.longFile = 1500,
  weak.linter.style.longFileDefValue = 1500, weak.linter.style.header = true, warningAsError = true.
- No autoImplicit / maxHeartbeats / pp options set globally: Lean defaults (autoImplicit true,
  maxHeartbeats 200000) apply in both projects. All Tau Ceti global options are linters or
  warningAsError, which only make the build stricter; none is needed for elaboration.
  So no file-level set_option was added for Step 2.

## Mathlib gap
- Mathlib 56a00585..ccbef15e = 85 commits (git log in .lake/packages/mathlib; blobs not local).
  Notable: #41506 Set one-field structure, #42704 Is*Apply args implicit, #43966 KummerDedekind
  from a prime, #44884 IsRoot.map explicit RingHom, #44903 deprecations removed, #44823 renames.

## Step 3 (VERIFIED, compiled)
- `lake build` of FrobeniusPrimeCount, Different.Exponent, Different.Permutation: Build completed
  successfully (4729 jobs), with NO local change to any vendored file. 397 TauCeti oleans built.
  Cold build of the 397 modules (Mathlib oleans prebuilt): real 1m22.5s, user 14m56.8s, sys 3m20.2s.
