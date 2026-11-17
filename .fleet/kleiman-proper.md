# kleiman-proper (fleet note)

**Verdict: `kleimanPicZeroProper` cannot be removed with no new leaf. The brief's phisurj route is circular.**
phisurj's bound `dim Pic⁰ ≤ dim A` (`PhiSurj.dim_le_of_open0`, PhiSurjCharZero.lean:304) applies the torsion leaf to
`B`. `B` is the abelian variety that `PicZeroAbVar0` supplies (`exists_torsAddEquiv hT B …`, line 317), and an
`AbVar` is proper by definition, so `B` is proper only because the field makes it so. The other lemmas of phisurj's
surjectivity proof are also typed over that `B`.

No torsion count can replace properness: `𝔾_a` has no torsion in characteristic 0, and the universal vector
extension of `Â` has dimension `2g` with the torsion of `Â`. Excluding the unipotent part is the cohomological
statement `h¹(A, 𝒪_A) = g`. No other open hypothesis mentions Picard, the identity component or `IsProper` (scan of
open-statements.json).

**What compiles** (`scratch/kleiman-proper/KleimanProper.lean`, standard axioms):
* a verbatim copy of the field, checked equal to the original by `rfl`;
* the narrowed form the chain reads, `KleimanPicZeroProperAbVar0` (abelian varieties, characteristic 0), and
  `PicZeroAbVar0` from it;
* the isolated core `PicZeroDimLeAbVar0` (`dim Pic⁰ ≤ dim A`), derived from the narrowed field and the chain's
  leaves;
* the brief's last step, `picZeroProper_of_surjective`: any surjection from `A` onto the identity component makes it
  proper (Stacks 03GN, with the vendored `GrpObj.isSeparated_hom`).

**What remains.** The converse, core ⇒ properness, is not compiled. It needs an ample class over `K` (or properness
over `K̄` followed by descent), `λ_L` lifted into `V`, and the finite-kernel lemmas re-proved for `V` instead of `B`.

The core is rated: printed form no. It is a consequence of Mumford §13 (UNVERIFIED numbering), and kinds.tsv would
count it as GLUE. So no fold is proposed and the field stays a printed LEAF.

The tree does contain the vendored homotopy invariance (CloudW07 `nonempty_iso_pullback_lift_of_isAlgClosed`,
Stacks 0BEH), which excludes `𝔾_a` and `𝔾_m` from `Pic⁰`. Turning it into properness would still need
Auslander–Buchsbaum, Chevalley's structure theorem and Borel's lemma, none of which is in the tree.

Report: docs/research/kleiman-proper.md.
