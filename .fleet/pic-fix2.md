# pic-fix2: status

**Result.** `phiAmpleIsogeny` now folds for −1 in both the strict and the strictest count, from leaves that are
instances of the print under either reading of Mumford's "ample".

**The leaves.**
* Both Mumford leaves assume `IsAmple L ∧ IsVeryAmple L`. `IsAmple` is supplied in the glue by `veryAmpleIsAmple`.
* §6 Application 1 (`MumfordKLFiniteDivisorAC`) is stated over an effective Cartier divisor, given as an invertible
  ideal sheaf, with `L = 𝒪(D) = divisorClass D hD`.
* The vendored lemmas `isInvertible_zeroLocus` and `nonempty_iso_dual_toModules_tensorObj` are used: a very ample
  `L` is `𝒪(D)` for a hyperplane section `D`.
* The second Mumford leaf is §8 Thm 1 (`MumfordPhiSurjectiveVAC`).

**Two folds.**
* **A** (`scratch/pic-fix2/autofold.json`, foldable now): the field as it stands, plus a third leaf
  `AmplePowVeryAmple` (Stacks 01VU / EGA II 4.5.10). Dry run: 34/11 → 37/10, strict and strictest; the dry-run module
  compiles. Reading risk: if 01VU prints only the `P(E)` form, this leaf becomes pending reading and fold A gives 0.
* **B** (recommended; `narrow.patch` + `autofold-narrow.json`): the chain reads only very ample `L`. Its only reader
  is `addedLeaves12_of_open13`, via `phiVeryAmpleIsogeny_of_printed`. The patch narrows the field to
  `PhiVeryAmpleIsogeny` in TailZ24/26/30/31/34. `phiVeryAmpleIsogeny_of_reading` then needs only the two Mumford
  leaves. Very ampleness base-changing to `K̄` is proved. Count: 34/11 → 36/10, strict and strictest. Tested on a
  throwaway copy: autofold ran, Main built, and `frozenTarget` has the standard axioms. It is a hand fold (it edits
  existing constants), so it needs hash-guard exceptions.

**What compiles** (standard axioms):
* `ZInQKernel/Contrib/OneProof/PhiAmpleIsogenyReading.lean`;
* `#discharges`: `phiAmpleIsogeny` by `PicFix2.phiAmpleIsogeny_of_reading`, assuming the 3 leaves;
* both dry-run fold modules (A, and A plus pic-fix's `picZeroAbVar`).

**What remains:**
* the integrator chooses fold A or fold B;
* the hash guard and OPEN.md regeneration;
* readings of the UNVERIFIED locators (Mumford §6 App. 1, §8 Thm 1; Stacks 01VU);
* locators.md rows (proposed in the report).
* pic-fix's spec miscounted strictest: with its KL leaf flagged "strictest", it gives 0 in strictest.

Report: `docs/research/pic-fix2.md`.
