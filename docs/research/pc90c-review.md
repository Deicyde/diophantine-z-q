# pc90c-review: re-check of draft PR #90 at head a04588b4

Task pc90c-review, 2026-11-17. Branch `wip/pc90c-review`, which is exactly a04588b4f with nothing merged. The only new
commit since a8099a02 (reviewed in `docs/research/pc90b-review.md` on `origin/wip/pc90b`) is the merge a04588b4f
(parents a8099a02a, the PR, and b9b854867, an older fork main; merge base 67950e829). Log: `scratch/pc90c-review/log.md`.
Every claim below is VERIFIED (compiled, computed or read in the tree) unless it is marked otherwise.

## Verdict

* **The Lean at a04588b4 is clean.** The build succeeds (16180 jobs). `frozenTarget`, the MainGreenTao headline and
  `PoleS12.kummerSelmerM` use only the standard axioms. No `sorry`, `admit` or `axiom` occurs in the PR's `ZInQKernel/`
  files. **(1) PASS.**
* **The merge resolution is correct. (2) PASS.** a04588b4f keeps fork main's current H bundles (`OpenResearchLeaves60`,
  `sixContactMin_of_open79`, the `TailZ86` import and the ss-faltings and d2a6b paragraphs). It also keeps the PR's
  `hRC, h54, hB, hK` and its import of `PoleCompletenessFromRCGenuineFinal`. Nothing from either side was dropped.
* **The labels are still wrong. (3) FAIL.** None of the three fixes is in a04588b4: the merge did not touch
  `Leaves.lean`, and it carried the old wording of `Main.lean` over unchanged. The exact replacement text is given below
  (`Leaves.lean` lines 7, 14–15, 17, 20, 52, 57–58, 81, 85–86, 91; `Main.lean` lines 12–13 and 155–157;
  `PoleCompletenessFromRCGenuineFinal.lean` lines 15 and 27–29). These are docstring edits only.
* **A merge onto be73b91c5 is not clean. (4) CONFLICT.** `git merge-tree --write-tree be73b91c5 a04588b4f` reports a content
  conflict in one file, `ZInQKernel/OneProof/Main.lean`, in one hunk: the signature and body of `frozenTarget`. The
  resolution is mechanical: fold-c8's `OpenResearchLeaves61`, `OpenAddedLeaves28` and `sixContactMin_of_open80`, plus the
  PR's `hRC, h54, hB, hK`. Built in a temporary worktree: see (4).
* Not checked here and still open from pc90b: S12 is still in the PR's history (commit 4b2595108). Squash the PR before
  merging it.
* Note: during this run the shared `origin/main` ref moved from be73b91c5 to dafd6c7c8 (the merge of PR #99). Everything
  below uses be73b91c5 explicitly, as the task specifies.

## (1) Build and axioms: PASS

| check | result |
|---|---|
| `lake build` of 25 targets: `ZInQKernel.OneProof.Main`, `ZInQKernel.MainGreenTao`, every `Contrib/OneProof/PoleS12/*.lean` (including `GoodF`), every `Contrib/OneProof/PoleCompleteness*.lean` and `Hypotheses.PoleManuscript` (list: `scratch/pc90c-review/build-targets.txt`) | **Build completed successfully (16180 jobs)**, exit 0, 0 errors (`build1.log`) |
| `#print axioms ZInQ.OneProof.frozenTarget` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness` | same |
| `#print axioms ZInQ.Manuscript.PoleS12.kummerSelmerM` | same; its type is `ZInQ.Manuscript.PoleS12.KummerSelmerM` |
| `#print axioms …PoleS12.poleCompleteness_of_restrictedConverseGenuine_final` | same |

(`scratch/pc90c-review/Axioms.lean`, output `Axioms-output.txt`.)

The forbidden-token check: I grepped the 64 `.lean` files that differ between b9b854867 and a04588b4f (whole words
`sorry|admit|axiom|native_decide|implemented_by|extern|unsafe`). There is **no hit in any `ZInQKernel/` file**. The only
hits are two `sorry` in `scratch/pc-from-rc/T3.lean:181-182`, a scratch file of the PR that is neither built nor
imported. It is informational and does not count against the build.

## (2) Merge resolution: PASS

`git show --remerge-diff a04588b4f` touches only `ZInQKernel/OneProof/Main.lean`, so every other file is git's own
auto-merge. That file had one conflict hunk, the `frozenTarget` signature and body:

* PR side (a8099a02): `OpenResearchLeaves57`, `sixContactMin_of_open76`, `hRC, h54, hB, hK`.
* Main side (b9b854867): `OpenResearchLeaves60`, `sixContactMin_of_open79`, `hPC : ZInQ.PoleCompleteness`.
* Resolution: `OpenResearchLeaves60`, `sixContactMin_of_open79`, `hRC, h54, hB, hK`, and the proof term
  `poleCompleteness_of_restrictedConverseGenuine_final hRC h54 hB hK`.

What the merge changed in `Main.lean`, against each parent:

* Against a8099a02 (the PR): the import `TailZ83` became `TailZ86`, main's ss-faltings and d2a6b paragraphs were added,
  `Leaves57` became `Leaves60`, and `open76` became `open79`. All of these come from main.
* Against b9b854867 (main): the import of `Contrib.OneProof.PoleCompletenessFromRCGenuineFinal` was added, the module and
  theorem docstrings were changed, and `hPC` became `hRC, h54, hB, hK`. All of these come from the PR.

Nothing is dropped on either side. `hPC` disappears on purpose, because PC is now proved from the four hypotheses.

`frozenTarget` at a04588b4 (compiled `#check`):
```
ZInQ.OneProof.frozenTarget : HDec.HSyn.OpenResearchLeaves60 → HDec.HSyn.OpenTextbookLeaves18 →
  HDec.HSyn.OpenAddedLeaves27 → ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine →
  ZInQ.Manuscript.PoleS12.Lemma54 → ZInQ.Manuscript.PoleS12.BCDTThmA → ZInQ.Manuscript.PoleS12.KolyvaginThm1 →
  ZInQ.FrozenTarget
```

## (3) Labels: FAIL. All three fixes are still missing

The merge did not change `ZInQKernel/Contrib/OneProof/PoleS12/Leaves.lean`: it is identical in a8099a02 and a04588b4. In
`Main.lean` the old wording moved to new line numbers (12–13 and 155–157). The exact current text and its replacement
follow. Line numbers are at a04588b4.

### Lemma54: a lemma of the manuscript, not a printed leaf

`Leaves.lean:7` (module title). Current:
```
# The printed leaves of Lemmas 5.4 and 5.5 over genuine definitions, and the support bound
```
Replace with:
```
# Lemma 5.4 of the manuscript and the leaves of Lemma 5.5 over genuine definitions, and the support bound
```

`Leaves.lean:17`. Current:
```
* `Lemma54` (printed leaf, tex `lem:corank`, Cassels–Tate via Poonen–Stoll): full rational
```
Replace with:
```
* `Lemma54` (a lemma of the manuscript, tex `lem:corank`, not a printed leaf: the manuscript proves it
  from the Kummer sequence and Cassels–Tate via Poonen–Stoll): full rational
```

`Leaves.lean:81`. Current:
```
/-- **Lemma 5.4 (`lem:corank`, tex L1072–1084), printed form over genuine definitions.** For an
```
Replace with:
```
/-- **Lemma 5.4 (`lem:corank`, tex L1072–1084), a lemma of the manuscript (not a printed leaf),
stated over genuine definitions.** For an
```

`Leaves.lean:85-86`. Current (end of the sentence):
```
Math. 150 (1999) 1109–1149 (`\cite{poonenstoll}`, tex L1081). A cited leaf here; not proved. -/
```
Replace with:
```
Math. 150 (1999) 1109–1149 (`\cite{poonenstoll}`, tex L1081). It is a hypothesis here, a lemma that
the manuscript proves and not a published theorem; it is not proved in Lean. -/
```

`Main.lean:12-13`. Current:
```
`Sel_{2^∞}(E_ℓ/ℚ)`), the printed leaves Lemma 5.4 (`ZInQ.Manuscript.PoleS12.Lemma54`), BCDT Theorem A
(`ZInQ.Manuscript.PoleS12.BCDTThmA`) and Kolyvagin's Theorem 1 (`ZInQ.Manuscript.PoleS12.KolyvaginThm1`).
```
Replace with:
```
`Sel_{2^∞}(E_ℓ/ℚ)`), the manuscript's Lemma 5.4 (`ZInQ.Manuscript.PoleS12.Lemma54`, a lemma of the manuscript,
not a printed leaf), the printed leaf BCDT Theorem A (`ZInQ.Manuscript.PoleS12.BCDTThmA`) and a consequence of
Kolyvagin's Theorem 1 (`ZInQ.Manuscript.PoleS12.KolyvaginThm1`, through Shimura's construction and Faltings'
isogeny theorem).
```

`Main.lean:155-157`. Current:
```
/-- **Theorem 1.1, from every statement still open:** the open H bundles, the manuscript's Theorem 5.3 (the restricted
converse) and the printed leaves Lemma 5.4, BCDT Theorem A and Kolyvagin's Theorem 1. Pole completeness PC (the
manuscript's Theorem 5.2) is proved from the last four
```
Replace with:
```
/-- **Theorem 1.1, from every statement still open:** the open H bundles, the manuscript's Theorem 5.3 (the restricted
converse) and Lemma 5.4 (both lemmas of the manuscript), the printed leaf BCDT Theorem A and a consequence of
Kolyvagin's Theorem 1 (through Shimura's construction and Faltings' isogeny theorem). Pole completeness PC (the
manuscript's Theorem 5.2) is proved from the last four
```

Two more places carry the same wording but were not in the task's list. I recommend fixing them in the same commit.

`Contrib/OneProof/PoleCompletenessFromRCGenuineFinal.lean:15`. Current:
```
(`SelmerTwoPower.RestrictedConverseGenuine`) and the printed leaves `PoleS12.Lemma54`,
```
Replace with:
```
(`SelmerTwoPower.RestrictedConverseGenuine`), the manuscript's Lemma 5.4 `PoleS12.Lemma54`, and the leaves
```

`Contrib/OneProof/PoleCompletenessFromRCGenuineFinal.lean:27`. Current:
```
Theorem 5.3 over the genuine Selmer condition and the printed leaves Lemma 5.4
```
Replace with:
```
Theorem 5.3 over the genuine Selmer condition, the manuscript's Lemma 5.4
```
The next line, `(`PoleS12.Lemma54`), BCDT Theorem A …`, then reads correctly.

Older intermediate files of the PR use similar wording (`PoleCompletenessFromRCGenuine.lean:18`, `…GenuineMW.lean:14`,
`…GenuineLeaves.lean:5`). They are not on the path of `frozenTarget`. Fixing them is optional.

### KolyvaginThm1: rated consequence

`Leaves.lean:14-15`. Current:
```
* `KolyvaginThm1` (printed leaf, the `r = 1` case): a modular elliptic curve with
  `ord_{s=1} L(E,s) = 1` has rank one and finite `Ш(E/ℚ)` (Tau Ceti's Ш, `SelmerTwoPower.sha`).
```
Replace with:
```
* `KolyvaginThm1` (consequence of Kolyvagin's Theorem 1, the `r = 1` case: Kolyvagin assumes a weak Weil
  parametrization, and `IsModular` gives one through Shimura's construction and Faltings' isogeny theorem):
  a modular elliptic curve with `ord_{s=1} L(E,s) = 1` has rank one and finite `Ш(E/ℚ)` (Tau Ceti's Ш,
  `SelmerTwoPower.sha`).
```

`Leaves.lean:52`. Current:
```
/-- **Kolyvagin, Theorem 1, the case `r = 1`** (printed leaf as cited: "On the Mordell–Weil group
```
Replace with:
```
/-- **Kolyvagin, Theorem 1, the case `r = 1`** (consequence of the print, not the printed statement; cited: "On the Mordell–Weil group
```

`Leaves.lean:57-58`. Current:
```
(p. 3). `IsModular` is a weaker hypothesis, so this leaf follows from the print only through
Shimura's construction and Faltings' isogeny theorem (with trivial nebentypus), the step BCDT cite
```
Replace with:
```
(p. 3). `IsModular` is a weaker hypothesis, so this statement is a consequence of the print: it follows
from Kolyvagin's weak Weil parametrization hypothesis only through Shimura's construction (an abelian
variety quotient of `J₀(N)` attached to the newform) and Faltings' isogeny theorem (with trivial
nebentypus), the step BCDT cite
```

pc90b already noted, as SPECULATIVE, that going to level exactly the conductor also uses newform theory and Carayol.
Naming it here is optional.

### KummerSelmerM: proved

`Leaves.lean:20`. Current:
```
* `KummerSelmerM` (textbook GLUE, not proved): for `E_ℓ`, the explicit system `SelM ℓ` has as many
```
Replace with:
```
* `KummerSelmerM` (textbook GLUE, proved by `PoleS12.kummerSelmerM` in
  `Contrib/OneProof/PoleCompletenessFromRCGenuineFinal.lean`, from `PoleRC.kummerSelmerM_proof`): for `E_ℓ`,
  the explicit system `SelM ℓ` has as many
```

`Leaves.lean:91`. Current:
```
/-- **The Kummer identification for `E_ℓ`** (textbook GLUE, not proved in Lean; Silverman, *The
```
Replace with:
```
/-- **The Kummer identification for `E_ℓ`** (textbook GLUE, proved: `PoleS12.kummerSelmerM`, with standard
axioms only; Silverman, *The
```

Related stale text, optional: `PoleCompletenessFromRCGenuine.lean:19` still says "(`PoleS12.KummerSelmerM`, textbook
GLUE);" and could add "proved by `PoleS12.kummerSelmerM`".

## (4) Landing preview on be73b91c5: CONFLICT (one hunk). Resolved build: see below

`git merge-tree --write-tree be73b91c5 a04588b4f` (`origin/main` was be73b91c5 when I ran it) exits with 1. Tree
d065e84f3, with **one conflicted file**:

* `ZInQKernel/OneProof/Main.lean` (stages 012b67f1 / bebc8d36 / 372fa404). The imports auto-merge (`TailZ87` and
  `PoleCompletenessFromRCGenuineFinal`), and so does fold-c8's doc paragraph. The one conflict is the `frozenTarget`
  signature and body:
  * be73b91c5 has `(r : OpenResearchLeaves61) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves28) (hPC : PoleCompleteness)`
    and `sixContactMin_of_open80 r t l` applied to `hPC`.
  * a04588b4 has `(r : OpenResearchLeaves60) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves27) hRC h54 hB hK` and
    `sixContactMin_of_open79 r t l` applied to `poleCompleteness_of_restrictedConverseGenuine_final hRC h54 hB hK`.

The intended resolution takes fold-c8's bundles plus the PR's hypotheses:
```
theorem _root_.ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves61) (t : HDec.HSyn.OpenTextbookLeaves18) (l : HDec.HSyn.OpenAddedLeaves28)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (h54 : ZInQ.Manuscript.PoleS12.Lemma54) (hB : ZInQ.Manuscript.PoleS12.BCDTThmA)
    (hK : ZInQ.Manuscript.PoleS12.KolyvaginThm1) :
    ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open80 r t l)
    (ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine_final hRC h54 hB hK)
```
The full diff of the resolved `Main.lean` against be73b91c5 is `scratch/pc90c-review/resolved-merge-Main.diff`.

RESOLVED_BUILD_PLACEHOLDER
