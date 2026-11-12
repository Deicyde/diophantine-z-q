# glue-conj — fleet summary

**Result: LeafConj is proved in Lean as glue, and B3(v) now rests on LeafB3a and LeafB3b only.**
(VERIFIED, compiled; axioms propext, Classical.choice, Quot.sound.)

- `scratch/glue-conj/Conj.lean` (self-contained): `GlueConj.leafConj : LeafConj`, with
  `LeafConj`, `LiesOver`, `inertiaGQ` and `GQ` copied verbatim from glue-b3-unram (the md5 sums of
  the definition blocks match). Proof:
  1. Center of a place: `𝔓_w = {b ∈ B | v_w(b) < 1}` on the algebraic integers `B`.
  2. Mathlib's profinite transitivity, `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`,
     applied to `Gal(ℚ̄/ℚ)` acting on the discrete `B`. The invariance and continuity instances
     are proved in the file.
  3. Center lemma: a place of `ℚ̄` is determined by its center. Proved in the number field `ℚ(x)`
     with Mathlib's `HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq`.
  4. `inertia_conj`: `w' = g•w ⇒ g⁻¹ I_{w'} g ≤ I_w`.
- `scratch/glue-conj/UnramConj.lean`: glue-b3-unram's `Unram.lean` plus the Conj section.
  `GlueB3Unram.unramified_outside_final` now takes only `(hA : LeafB3a) (hB : LeafB3b)`.
  Compiles with no errors; all `#print axioms` lines show only the three standard axioms.
- T1–T3.lean are the compiled step drafts.

**Remains:** the leaves L-B3a (uniqueness of the quadratic character of tame inertia) and L-B3b
(the Legendre character mod p is ramified at p). L-B3b might be provable as glue from Mathlib's
cyclotomic results (SPECULATIVE, not attempted). Integration: paste the Conj section into
glue-b3-unram's file and drop `hConj` from callers. h-decomposition's leaf table should move L-conj
to glue. Report: `docs/research/glue-conj.md`.
