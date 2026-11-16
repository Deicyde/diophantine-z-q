# bfh-leaf (fleet summary)

**Result.** `ZInQ.GZDecomp.FHNonvanishing` is proved from one new leaf, `ZInQ.BFHPrinted.BFHClauseII`:
Bump–Friedberg–Hoffstein, Invent. Math. 102 (1990), opening theorem, clause (ii), at weight 2 and trivial character.
It is stated over genuine objects: Tau Ceti's `Newform N 2` with `f.χ = 1`; `ε` the sign of the functional equation
`Λ_N(2 − s) = ε Λ_N(s)` over the kernel's `completedL` at level `N`; `S` any finite set of primes containing the
primes of `2N`; Mathlib's `Int.IsFundamentalDiscr d`, `d ≠ 1`; "p splits in ℚ(√d)" as two distinct primes of `𝓞 K`
above `p` (`Ideal.primesOver`) for a quadratic number field `K ∋ √d`; and fh-printed's `CentralValueNeZero`. All
glue is proved (`fhNonvanishing_of_bfhClauseII`). No twisted root number, no auxiliary `D₀`, no Dirichlet theorem.
So `hFH` (GLUE) can be replaced by a leaf in printed form: −1 GLUE.

**Compiles** (standard axioms, no warnings except Lake's module-system import notes):
`ZInQKernel/Contrib/OneProof/BFHNonvanishing.lean`, helpers `BFHPrinted/Split.lean` (fundamental identity gives
e = f = 1 at a split prime, hence d ≡ 1 mod 8 from 2 split and (d/p) = 1 from p split) and `BFHPrinted/Witness.lean`
(7 splits in ℚ(√−3): the splitting clause is satisfiable). `isFESign_iff` shows `ε` = `rootNumber`. The fold is
checked without editing Main (`scratch/bfh-leaf/FoldCheck.lean`, `frozenTarget_bfh`, standard axioms).
`#discharges` output recorded: it does not list the file (the theorem's type is `FHNonvanishing`, not `hFH`'s type);
hand fold described in `scratch/bfh-leaf/autofold.json` and the report §5.

**Rating.** Printed form (direct instance: k = 1, 2 ∈ S, ∃ K for "the field ℚ(√d)"), flagged **unread**: the
statement is the theorem-application audit's reading of page images (A025), not read here. Three checks remain:
(1) no CM exclusion (the use is the CM newform of C_d); (2) no level condition (N = 32d²); (3) wording
(fundamental vs squarefree d; "split" vs a congruence mod 4N). If (1) or (2) fails: pending reading (GLUE).

**Remains.** The three checks; the hand fold (Main.lean, kinds.tsv row, locators row, OPEN.md). Report:
docs/research/bfh-leaf.md.
