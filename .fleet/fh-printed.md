# fh-printed (fleet summary)

**Result.** `hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE` is discharged from a new leaf
`ZInQ.FHPrinted.FriedbergHoffsteinB_Printed`, Friedberg–Hoffstein 1995 Thm B stated over its own
objects: local conditions as equality of the local components `χ_{d,v}` (norm-residue / Hilbert
symbol characters of `ℚ_v^×`, `v ∈ S ∪ {∞}`), quadratic characters `χ_d` (`d` squarefree) with
Dirichlet coefficients built from their local components, the root number as the sign of the
functional equation for *some* conductor, "infinitely many" as `Set.Infinite`. Proved in Lean,
standard axioms: `friedbergHoffsteinB_FE_of_printed` (discharges hFH), the converse
`friedbergHoffsteinB_printed_of_FE` (the two leaves are equivalent, so the new one is not
stronger), `rootNumberTwistEqOne_iff` (root-number clause ⟺ `χ_{D₀}(−N) ε(f) = 1`, the Atkin–Li
value), `idelicChar_eq_jacobiSym`, and the local dictionary (Hensel, descent on the norm form, at
odd p, 2 and ∞).

**Compiles.** `ZInQKernel/Contrib/OneProof/FriedbergHoffsteinBFE.lean` and
`ZInQKernel/Contrib/OneProof/FHPrinted/LocalNorm.lean` (Mathlib-only helper) build with no
warnings; `#discharges` (scratch/fh-printed/Discharges.lean, output recorded):
`DISCHARGES [hFH] by ZInQ.FHPrinted.friedbergHoffsteinB_FE_of_printed, still assumes
[ZInQ.FHPrinted.FriedbergHoffsteinB_Printed]`; `fhprinted_frozenTarget` (the fold, checked without
editing Main) has standard axioms. Autofold spec: scratch/fh-printed/autofold.json (hFH is a
top-level hypothesis: hand fold, described in its `_note`).

**Rating of the new leaf.** Printed form for the review's clauses (i) (the conductor theorem is
gone; the sign of the FE is the definition of the root number) and (ii) (now literal), and for the
character and "infinitely many". Not printed in one clause, (iii): `L(s, π_f ⊗ χ_d)` is read as
the classical series `∑ aₙ(f) χ_d(n) n^{−s−½}` (local newform theory at `p ∣ N`); Mathlib has no
automorphic L-functions. If that standard normalization is accepted the fold is −1 GLUE.

**Remains.** Reading (iii); the human checks of the print (label, page, dihedral π, places in S,
full or partial L; all locators UNVERIFIED); the hand fold, kinds row and locators row (proposed
in docs/research/fh-printed.md §4–5).
