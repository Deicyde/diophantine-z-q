# Elkik's printed torsion theorem and the finite cuspidal subgroup

Elkik's printed statement gives torsion of each degree-zero cuspidal divisor class. Lean derives the finite subgroup at `diophantine_zq.tex` 2937–2940: the class map descends through the finite `Γ₀(N)` cusp orbit type, so its range generates a finitely generated subgroup of the torsion subgroup. The result has exactly the base reduction's `ManinDrinfeld N cuspClass` type. The genus partner corollary supplies the same nonzero rational witness as that reduction, conditional on the printed torsion, the descent of the class map, and the existing inputs below.

The base is `849e76044f2a3c95649ce2e84c61f2befa0857f2`. The revised print is R. Elkik, *Le théorème de Manin–Drinfeld*, Astérisque 183 (1990), p. 59, Théorème (tex 11158–11160). The reviewer read: “THÉORÈME. Si Γ est un sous-groupe de congruence, la classe de tout diviseur de degré 0 de X_Γ à support dans les pointes, est un élément de torsion de Pic⁰(X_Γ).” For `Γ = Γ₀(N)` this applies to every `[c(r)] − [∞]`, `r ∈ ℙ¹(ℚ)`. The torsion statement is a **LEAF-candidate**, pending the lead's skeptic pass. Identifying the parameters with the printed objects is still GLUE.

## Lean statements and the input they supply

Write `E = Ecurve ℓ`, `N = newformLevel E` in the corollary. Let `CuspOrbits Γ₀(N)` denote Mathlib's orbits of rational cusps, realized inside `OnePoint ℝ`. The files are in `ZInQKernel/Contrib/OneProof/RC/ElkikPrint/`.

| Declaration | Statement and use |
| --- | --- |
| `ManinDrinfeldTorsion N cuspClass` (print proposition) | For `N > 0`, `J` an additive commutative group and `cuspClass : OnePoint ℚ → J`, `∀ r, ∃ n : ℕ, 0 < n ∧ n • cuspClass r = 0`. Input to the proof of `hMD`. |
| `cuspOrbit N r` (definition) | Sends the rational representative `r` to its orbit in `CuspOrbits Γ₀(N)`, using Mathlib's description of the cusps of arithmetic subgroups. It is the quotient map used in the finite range proof. |
| `cuspClass_finiteRange_of_cuspOrbits` | For `classOfCusp : CuspOrbits Γ₀(N) → J` and `hCuspFactor : ∀ r, cuspClass r = classOfCusp (cuspOrbit N r)`, proves `(Set.range cuspClass).Finite`. Supplies `hFinite` in the proof of `hMD`. |
| `maninDrinfeld_of_torsion` | `ManinDrinfeldTorsion N cuspClass → (Set.range cuspClass).Finite → ElkikMD.ManinDrinfeld N cuspClass`, where the last proposition is `Finite (AddSubgroup.closure (Set.range cuspClass))`. Supplies `hMD` to `ElkikMD.hElkikMD_of_maninDrinfeld` and can also supply its finite subgroup to `cuspidalImage_annihilator`. |
| `hElkikMD_of_elkikTorsion` | With `hTorsion`, `classOfCusp`, `hCuspFactor` and the remaining original inputs below, proves `∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = GenusOdd.Lstar E Lat d`. Supplies the original reduction's conclusion at `d = h_*`; it discharges `hMD` by the two preceding theorems. |

Provenance (c), on the spot: the map to Mathlib's cusp orbits, the finite image argument, the use of Mathlib's finitely generated torsion group theorem, and the composition with the base reduction. The only new proposition taken as an input is `ManinDrinfeldTorsion`. It is strictly weaker than `ManinDrinfeld` on the abstract parameters: finiteness gives a common positive annihilator, whereas pointwise torsion is compatible with an infinite range, for example the rational residues in `ℚ/ℤ`. The separate `hFinite` is also strictly weaker than finiteness of the generated subgroup: a map with range `{0, 1}` into `ℤ` generates an infinite group. `hCuspFactor` only identifies the values attached to representatives of the same cusp, independently of their orders; even the constant map with value `1` in `ℤ` factors and generates an infinite group. There is no new hypothesis structure.

## Exact remaining inputs

In the table, `r_a` is the rational `a / d.natAbs` (viewed in `OnePoint ℚ` in `cuspClass r_a`) and `χ_d(a) = chiD d a`. Brackets on the right of the cusp comparison denote `QuotientAddGroup.mk' Lat.lattice.toAddSubgroup`. The positive curve parameter and `d = h_*` are fixed by the assembly.

| Input to the corollary | Manuscript lines | Owner and size |
| --- | --- | --- |
| `[(Ecurve ℓ).IsElliptic]` and `[NeZero (newformLevel (Ecurve ℓ))]`. | 1761–1767, 1779–1782 | ELLIOT input, already present as curve and positive level data. |
| `J : Type*`, `[AddCommGroup J]`, `cuspClass : OnePoint ℚ → J`, `classOfCusp : CuspOrbits Γ₀(N) → J`, and `hCuspFactor : ∀ r, cuspClass r = classOfCusp (cuspOrbit N r)`. The intended realization is `J = J₀(N)(ℚ̄)` and `classOfCusp c = [c] − [∞]`. | 1781–1786, 2937–2939 | Missing theory, large: the curve, Jacobian, and actual divisor classes with the identification of analytic cusp orbits. Descent for the realized class map is the small statement above; finiteness of the orbit type is already proved by Mathlib and no cusp count is needed. |
| `hTorsion : ManinDrinfeldTorsion N cuspClass` for that realized map. | 2937–2940, 11158–11160 | ELLIOT input via the single Elkik print, pending the lead's skeptic pass and the preceding geometric identification. |
| `f : Newform N 2` and `hf : PrintsAnalytic.IsNewformOf E f` (trivial character and matching coefficients for every `n > 0`). | 1779–1784 | ELLIOT input via existing modularity and form data. `ElkikMD.curveNewform_eq_assemblyForm` gives the matching newform from the existing modularity input and the assembly form with its coefficient equality. |
| `hgp : GenusPartner E d`: `d < 0`, `d % 4 = 1`, `Squarefree d`, `4 < |d|`, `SquareAt p d` for every prime `p ∣ 2*N`, and `AnalyticRank (qtwist E d) 0`. | 2404–2410, 8247–8254 | ELLIOT input via the existing partner data. `Gz34Instance.genusPartner_of_support` supplies it once the support contains the primes of `2*N`. |
| `Lat : PeriodPair` (the assembly's fixed period pair), `κ : ℚ`, `hκ : κ ≠ 0`, `φ : J →+ ℂ ⧸ Lat.lattice.toAddSubgroup`, and `hAJ : ∀ a < d.natAbs, χ_d(a) ≠ 0 → φ (cuspClass r_a) = [(κ : ℂ) * ElkikMD.cuspSymbol f.toCuspForm r_a]`. | 1781–1787, 1825–1828, 2836–2838, 2937–2942, 7137–7139, 7175–7177 | Missing theory, large for the fixed geometry: realize `φ` by `α q_f` followed by uniformization with this `Lat` and compare its cusp images with the symbol at a common rational scale. The displayed comparison on the nonzero weights is the smallest statement the reduction uses. |

With these inputs, the corollary gives the base assembly's `hElkikMD` witness. No input for global central value normalization or any other part of the assembly is discharged here.

All three new files passed `lake env lean` sequentially. The three theorem audits list only `propext`, `Classical.choice`, and `Quot.sound`. The transitive imports do not include `ZInQKernel.OneProof.Main`.

## Known issues

- `RC/ElkikMD/Prints.lean` labeled the finite subgroup form as the print. The page states torsion instead, and the manuscript correctly uses its finite cusp consequence. The original proposition remains available to existing consumers; use `ElkikPrint.ManinDrinfeldTorsion` as the print for new consumers.
- `RC/PrintsArith/Heegner.lean` records an analytic reformulation that requires Abel–Jacobi. It does not supply the cusp comparison or enter the proof here. The attribution of rationality to Manin–Drinfeld in `GenusOdd/Defs.lean` leaves implicit the cusp comparison and the twist calculation, as recorded in the [base report](rc-elkik-md.md#known-issues).
- No error was found in the manuscript or the quoted source in this scope.

## Manuscript check

- 1761–1767, 1779–1784 — OK: the reduction takes the elliptic curve, positive level and matching weight-two newform as existing inputs.
- 1781–1787, 2836–2838, 2937–2939 — unverified: the actual Jacobian, cusp classes and image under the fixed parametrization are still parameters in Lean.
- 11158–11160, 2940 — OK: the locator agrees with the reviewer's reading of the printed torsion theorem; the Lean statement specializes it to the cusp differences used here.
- 2937–2940 — gap filled: finiteness uses the finite cusp orbit type and the finite generation of the subgroup spanned by the resulting torsion classes.
- 2941–2942 — OK: the existing `cuspidalImage_annihilator` turns that finite subgroup into one positive annihilator on its image under the fixed additive map.
- 2943–2946 — OK: given the stated Atkin–Lehner formula, its cusp constant lies in that image and the same annihilator kills it. The involution formula is not formalized here.
- 2404–2410, 8247–8254 — OK: the corollary takes the negative partner and uses its analytic rank zero for nonvanishing through the base reduction.
- 7118–7139, 7188–7192 — gap filled by the base reduction for the central value: the quadratic Fourier and twist calculation relates the weighted cusp sum to the central value. This does not verify the Appendix E Euler system comparison.
- 1825–1828, 7175–7180 — unverified: the actual comparison with the chosen period pair is still input `hAJ` at the rational scale `κ`.
- 2438–2439, 10172–10178 — gap filled conditionally: the corollary gives the nonzero rational value whose valuation is used at `h_*`, subject to the inputs above. It does not establish the height comparisons.
