# Results log

- Base: `849e76044f2a3c95649ce2e84c61f2befa0857f2`.
- Print: Astérisque 183 (1990), p. 59, Théorème, reviewer read; torsion of degree-zero cuspidal classes. `ManinDrinfeldTorsion N cuspClass := ∀ r, ∃ n : ℕ, 0 < n ∧ n • cuspClass r = 0`. LEAF-candidate pending skeptic pass; actual class map and Jacobian GLUE.
- `cuspClass_finiteRange_of_cuspOrbits`: factor through `CuspOrbits Γ₀(N)` via `cuspOrbit N` → `(Set.range cuspClass).Finite`. Mathlib supplies finite arithmetic cusp orbits.
- `maninDrinfeld_of_torsion`: torsion print + finite range → existing `ElkikMD.ManinDrinfeld N cuspClass`; proof uses the torsion subgroup and finite generation.
- `hElkikMD_of_elkikTorsion`: torsion print + cusp descent + original curve, newform, partner, lattice, scale, map and `hAJ` → `∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = GenusOdd.Lstar (Ecurve ℓ) Lat d`.
- Source check: tex 2937–2940 uses the finite consequence of the print; no manuscript or source error found in scope.
- Transitive imports checked: no `ZInQKernel.OneProof.Main`.
- Sequential `lake env lean`: `Prints.lean`, `Finiteness.lean`, `Reduction.lean` passed. Resource gates checked with `uptime` and `free -g` before each invocation. All three theorem audits: `propext`, `Classical.choice`, `Quot.sound` only.
