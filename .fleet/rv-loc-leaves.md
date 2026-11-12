# rv-loc-leaves (fleet report)

**Verdict.** I checked the ten items (a)-(j) of the locator audit against the Lean leaves. None is
vacuous. One Lean statement is stronger than its published source: T27 `PkgI3.QMDichotomy` drops
Yu's "indefinite" hypothesis. I repaired it to `QMDichotomyYu`; the old form implies it, and the
project's B = (2,-3) satisfies it. Five placeholder docstrings were wrong or out of date and are
repaired:
- R02 claimed indices 4,6,2 for the degree-4 map X₆→X₆/W. In fact (4,6,2) are orbifold orders and
  the index is 2 (Lean check on Elkies' model).
- R05 claimed #CM(R) = h(R); the correct count is 2^b h(R).
- R16, R17 and R22 are updated.

All other leaves are FAITHFUL:
- (a) PanBerger: stated for p ≥ 5 only, so Pan's p=3 exception does not arise; the arithmetic-Frobenius
  form follows from Pan's geometric one via tr(M⁻¹)=trM/detM, compiled.
- (b) Serre–Tate potential good reduction and the Grothendieck forms: one K' for all n.
- (c) Pazuki in the log π and +3 forms: the audit's consequence steps (truncation, min, |·|,
  h_D = h_F + log π) are proved in Lean.
- (f) Carayol R17: all ℓ including 2, all p ≠ ℓ including p | N.
- (g) R13/R14: cusp forms only by type; no consumer needs Eisenstein forms.
- (h) R15 keeps semisimplicity.
- (j) R16 does not use Shimura 1973's zeta clause, so the Fricke condition does not enter.

**Compiles** (scratch/rv-loc-leaves/, one Lean process at a time, standard axioms only):
- `LeavesPatched.lean`: Leaves.lean with all repairs applied by `patch_leaves.py` (16 edits;
  diff in `LeavesPatch.diff`). Exit 0, 0 errors, 81 axiom prints; the only sorry is the
  pre-existing `HSyn.sixContactMin_of_leaves`.
- `T27Yu.lean`, `PazukiR22.lean`, `Conventions.lean`, `Placeholders.lean`.

**Remains.**
- I re-read no primary source (no network); every paper reading is the audit's.
- Pazuki's level-2 theta height = Thomae Euclidean height is unchecked.
- Index 2 at j = ∞ is not proved in Lean.
- Leaves.lean, h-decomposition.md and LadicCond.lean were not edited (other tasks' files): the
  integrator applies the diff and the docstring list in docs/research/rv-loc-leaves.md.
