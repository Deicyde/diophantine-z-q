# glue-b3b (fleet report)

**Result.** LeafB3b is proved as glue in Lean: `GlueB3Unram.leafB3b : LeafB3b`, with
glue-b3-unram's statement unchanged (md5 of the def blocks match). The statement: the Legendre
character mod an odd `p`, as a character of `G_ℚ`, is nontrivial on every inertia group over `p`
(ℚ(√p*) is ramified at `p`). B3 (v) is discharged accordingly:
`unramified_outside_b3a (hA : LeafB3a) ...` has the same conclusion as glue-conj's
`unramified_outside_final`, minus `hB`.

Bonus results:
- `GlueB3Unram.t32b : LeafPush.T32b_QuadraticRamification` proves leaf T32(b) of the synthesis
  bundle (text verbatim, diff-identical to `scratch/h-decomposition/Leaves.lean`).
- `leafB3a_of_t32a : T32a_TameQuadratic → LeafB3a` and `unramified_outside_t32a`. So **B3 (v) now
  rests only on the bundle's existing leaf T32(a)**, and L-B3a is no longer a separate leaf.

**Method.** No discriminants and no ramification indices. Take α = the Gauss sum (α² = ±p), H =
Stab(α) and A = B^H. Mathlib's profinite invariant theory over (A, H)
(`exists_smul_of_under_eq_of_profinite`, `Ideal.Quotient.stabilizerHom_surjective_of_profinite`)
yields an element of I_w negating α. The only arithmetic input is v(α)² = v(p). This is the core
theorem `exists_inertia_neg`, valid for any prime and any α with α² = c ∈ ℤ, v(c) = v(p).

**What compiles.** `scratch/glue-b3b/B3b.lean` (1810 lines, `import Mathlib`; glue-conj's
UnramConj.lean verbatim plus the new sections). `lake env lean` gives no errors (about 20 s). All
14 `#print axioms` lines read [propext, Classical.choice, Quot.sound]; there is no sorry and no
axiom. Nothing under ZInQKernel/ or blueprint/ was touched.

**What remains.** T32(a) (the unique quadratic character of tame inertia; L-B3a follows from it)
is not proved. It needs tame-inertia structure (G₀/G₁ ↪ k^×, G₁ a p-group), or Kummer theory
plus the value group of the inertia field; Mathlib has neither. Integration: turn B3b.lean's
prefix (glue-b3-unram + glue-conj) into a module and import Leaves.lean's T32 definitions
instead of copying them. Report: docs/research/glue-b3b.md; log: scratch/glue-b3b/log.md.
