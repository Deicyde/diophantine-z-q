# rv-redei log

## 2026-11-11
- Read RedeiStatement.lean, Sec3/Defs.lean (gBit, redeiG, lapl, kappa, T5b), Slots/Symbols.lean
  (legBit), Redei/{Field,Entry,Bridge,FourRank} and the definitions in Primes/Ambiguous/Genus.
- PARI differential check (scratch/rv-redei/gbit_check.py, output gbit_check.out): 30 pairs (d, B),
  d_B in classes 7, 3, 1 mod 8, 1-5 primes in B: gBit (transcribed) = parity of #Cl^2 in 30/30;
  both parities occur (14 even / 16 odd).
- Main-theorem variants: git diff 2b048334^1..2b048334 shows only the `hR` argument removed and
  `RouteK.Redei.redeiFormula` supplied in its place; docstrings updated.
- Docstring findings (non-blocking): TYZ.lean:107-108 says "every set B" (false for B = ∅:
  gBit d ∅ = 0, g(1) = 1), Lean statement has B.Nonempty; TYZ.lean:92-93 "none of them formalized
  here" contradicts the Rédei bullet "proved in Lean".
- Started `lake build ZInQKernel` (full).
- `lake build ZInQKernel`: success, 9918 jobs, 6 min (build.txt).
- `lake env lean scripts/print_axioms.lean`: 50 entries, all [propext, Classical.choice, Quot.sound]
  (axioms.txt).
- Scratch Lean file Instances.lean: Odd (gCl 7), Odd (gCl 19), Even (gCl 17) derived from
  redeiFormula; compiled; fixes needed: Subtype motive in `rw [hp.primeFactors]` (used
  Nat.mem_primeFactors + prime_dvd_prime_iff_eq), Finset.univ_nonempty needs a Nonempty instance
  (gave an explicit element). Source copied into docs/research/rv-redei.md §1.6, file deleted.
- Wrote docs/research/rv-redei.md and .fleet/rv-redei.md. Verdict: no blocker; N1, N2 docstring nits.
