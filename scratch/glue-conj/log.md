# glue-conj results log

- T1.lean: `le_of_center` (two valuation subrings of ℚ̄ over p with the same center on the
  algebraic integers: w₁ ≤ w₂), via Mathlib `HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq`
  in the number field ℚ(x). COMPILED (warnings only), 00:42.
- T2.lean: algebraic integers `B := integralClosure ℤ ℚ̄` with the `Gal(ℚ̄/ℚ)` action,
  `Algebra.IsInvariant ℤ B Gal` (via `InfiniteGalois.mem_bot_iff_fixed`, ℤ integrally closed),
  discrete topology, `ContinuousSMul` (via `stabilizer_isOpen_of_isIntegral`); then Mathlib's
  `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` gives transitivity on primes of `B`
  over the same prime of ℤ. COMPILED.
- T3.lean: `val_lt_one_iff`, `val_smul_lt_one_iff` (v_{g•w}(y) < 1 ↔ v_w(g⁻¹y) < 1),
  `inertia_conj` (w' = g•w ⇒ g⁻¹ I_{w'} g ≤ I_w, inertia = image of Mathlib's
  `ValuationSubring.inertiaSubgroup`). COMPILED.
- Conj.lean (T1+T2+T3 + assembly): `centerIdeal w = {b ∈ B | v_w(b) < 1}`, prime, lies over
  `pℤ` (`centerIdeal_under`), `centerIdeal (g•w) = g • centerIdeal w`; `leafConj : LeafConj`.
  LeafConj/LiesOver/inertiaGQ text identical to glue-b3-unram's (md5 of the def blocks match).
  COMPILED; `#print axioms GlueConj.leafConj`: [propext, Classical.choice, Quot.sound]. 00:46.
- UnramConj.lean: glue-b3-unram's Unram.lean verbatim + section `Conj` (the proof above, in
  namespace GlueB3Unram) + `unramified_outside_final` with the `hConj` hypothesis removed
  (now `(hA : LeafB3a) (hB : LeafB3b)`; calls `leafConj`). COMPILED, no errors; all eight
  `#print axioms` lines: [propext, Classical.choice, Quot.sound]. 00:47.
