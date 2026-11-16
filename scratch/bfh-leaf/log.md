# bfh-leaf results log

Task: replace top hypothesis `hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE` of `ZInQ.OneProof.frozenTarget` by a printed
leaf for Bump–Friedberg–Hoffstein 1990, opening theorem clause (ii), and prove `ZInQ.GZDecomp.FHNonvanishing` from it.

## 11-15 23:00 setup
- Merged origin/wip/fh-printed (8d0b9b64), clean. Build tree copied from ~/dzq-wt/unif-printed (.lake/build, lean/.lake/build).
- `lake build ZInQKernel.Contrib.OneProof.FriedbergHoffsteinBFE`: OK (VERIFIED).

## Split primes (Mathlib only) — VERIFIED (compiled)
- `ZInQKernel/Contrib/OneProof/BFHPrinted/Split.lean` (= scratch/bfh-leaf/Split.lean): `SplitsIn K p` := two distinct
  primes of `𝓞 K` in `(Ideal.span {(p:ℤ)}).primesOver (𝓞 K)`. Proved: `ef_eq_one` (fundamental identity
  `Ideal.sum_ramification_inertia_eq_finrank`), `exists_int_sub_mem` (f = 1), `natCast_not_mem_sq` (e = 1, via
  `ramificationIdx'_eq_ramificationIdx`), `zmod_isSquare_of_splitsIn` (p² ∤ d, √d ∈ K, p split ⇒ d nonzero square mod p),
  `mod_eight_of_splitsIn_two` (d fundamental discriminant, √d ∈ K, 2 split ⇒ d ≡ 1 mod 8). No deprecated API.

## Leaf and glue — VERIFIED (compiled, standard axioms)
- `ZInQKernel/Contrib/OneProof/BFHNonvanishing.lean` (copy: scratch/bfh-leaf/BFHNonvanishing.lean.txt):
  `IsFESign f ε` (FE Λ_N(2−s) = ε Λ_N(s) over `ZInQ.Literature.completedL N`), `SplitsInQuadratic d S`
  (∃ quadratic number field K ∋ √d, every p ∈ S has two distinct primes of 𝓞K above it), leaf `BFHClauseII`;
  `fhNonvanishing_of_bfhClauseII : BFHClauseII → FHNonvanishing`; `isFESign_iff : IsFESign f ε ↔ ε = rootNumber f hχ`.
- `lake env lean` on the file: no errors, no warnings. `lake build ZInQKernel.Contrib.OneProof.BFHNonvanishing`: OK.
- FoldCheck.lean: `frozenTarget_bfh` = Main's body with hFH ↦ hBFH; axioms [propext, Classical.choice, Quot.sound].
- Discharges.lean: #discharges does not list the new file (its theorem has type FHNonvanishing, not an open
  hypothesis; hFH's type FriedbergHoffsteinB_FE is not derivable from BFH (ii)); output recorded. The `hFH` line in
  the output is fh-printed's theorem (imported transitively through FriedbergHoffsteinBFE).
- autofold.json written (hand fold note).

## Nonvacuity witness — VERIFIED (compiled, standard axioms)
- `ZInQKernel/Contrib/OneProof/BFHPrinted/Witness.lean` (= scratch/bfh-leaf/Witness.lean): 7 splits in ℚ(ζ₃) ∋ √−3 = 2ζ₃+1
  (kernels of ζ₃ ↦ 2, ζ₃ ↦ 4 into 𝔽₇ via `IsPrimitiveRoot.integralPowerBasis`). Pitfall: `IsCyclotomicExtension {3} ℚ
  (CyclotomicField 3 ℚ)` is not found by instance search even with a local hypothesis; prove for a general K and
  instantiate with explicit `@`.
- `splitsInQuadratic_witness : Int.IsFundamentalDiscr (-3) ∧ (-3:ℤ) ≠ 1 ∧ SplitsInQuadratic (-3) {7}`.
- Rebuilt; FoldCheck and #discharges rerun (2260 theorems checked; no change in the discharge lines).
