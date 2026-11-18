# Cyclotomic Tate pairing and the degree-one Hodge number (S16)

**Result.** `HodgeFil1.tatePolarizationSymmetry_proof` supplies a nondegenerate pairing on the rational Tate module of every abelian variety over a finite extension of `ℚ_p`, with cyclotomic Galois multiplier. `HodgeFil1.scholzeH1AbVar_of_dR` uses it to recover the full degree-one row in every dimension from de Rhamness, the filtration range, and the existing T10 duality. The internally proved Fil¹ clause is the justification of L10996 on the comparison side, including the surface case.

## Route

The [route map](../../scratch/tate-polar-sym/route.md) accounts for the old Picard inputs. The proved projective embedding gives a very ample line bundle `L` over the original field. Native seesaw supplies descent of its normalized family through the actual finite and surjective quotient `q : A → A/K(L)`. Specializing the descended family gives an injective map from geometric quotient points to invertible-sheaf classes. On a point `q(x)` the class is `t_x^*L ⊗ L⁻¹`. This formula and the native square give multiplicativity and translation invariance, and pullback in the parameter gives Galois compatibility.

The class of an `n`-torsion quotient point is itself killed by `n`. Native seesaw identifies pullback by addition with the tensor product of the two factor pullbacks for translation invariant classes. Iteration identifies `[n]^* M` with `M^n`, giving the trivialization required by the existing Weil formula. A zero Weil character forces the class to be trivial by descent, and injectivity then forces the quotient point to be zero. Torsion counts and the equality of dimensions give perfection on the left, too. The proof uses compatibility of the formula and the Galois action on the actual roots of unity. It requires no representability of the relative Picard functor, no Picard-zero properness input, and no construction of adjoints to arbitrary endomorphisms.

The pulled-back pairings at the p-power levels satisfy the transition identity
`eᵠₙ(mx,my) = eᵠₘₙ(x,y)^m`. They yield a bilinear map to the Tate module of roots of unity. A quasi-inverse to `q` shows that a radical element at every level is killed by the same positive integer `d`. For a compatible sequence, writing `d = p^a d'` with `p ∤ d'` and moving up by `a` levels gives `d' xₖ = 0`. Since each `xₖ` is killed by `p^k`, it is zero. In coordinates on the roots-of-unity Tate line, the Galois character is cyclotomic. Extending scalars on the finite free Tate lattice preserves the nonzero Gram determinant and the multiplier. The restriction of the cyclotomic character to the local Galois group agrees with the `cycPow ... 1` convention in the old row.

The existing `fil1_of_dR` theorem uses this symmetry on `Vₚ(A)` after T10 identifies the cohomology representation with its linear dual. The two filtration multiplicities are equal and sum to `2 * g`. The third clause of the old row, `finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = finrank ℚ_[p] F * g`, therefore follows from its first two clauses and T10.

## Lean statements

The intermediate declarations are in namespace `HodgeFil1.TatePolar`. The final two are in `HodgeFil1`.
In the main statement, for each prime `p`, each finite extension `F/ℚ_p`, and each `A/F`, the form is `B : LinearMap.BilinForm ℚ_[p] (A.V p)` with `B.Nondegenerate` and
`B (A.galRep p σ x) (A.galRep p σ y) = cycPow p (gfToGqp p F σ) 1 * B x y` for all `σ`, `x`, and `y`.

| Declaration | Statement |
|---|---|
| `translate_eq_tr`, `polarizationFamily_eq_phiPt` (private) | The native translation and geometric specialization agree with the morphism and class used in the Weil formula. |
| `phiPt_isTranslInv`, `phiPt_mul` | The polarization class is translation invariant and multiplicative in the geometric point. |
| `mulN_pic_of_invariant` | Pullback of a translation invariant class by multiplication by `n` is its `n`th tensor power. |
| `exists_nativePolarization` | Each characteristic-zero abelian variety has native quotient data: the isogeny, equal dimension, and the injective equivariant map to actual classes with the polarization formula. |
| `torPow`, `NativePolarization.clTor_isDualTors` (private) | The multiplicative point underlying a torsion point is killed by the same exponent; the corresponding class is translation invariant and killed by that exponent. |
| `NativePolarization.scalar_exists`, `scalar_formula`, `weil_formula` (private) | The formula is a constant root of unity; the chosen scalar and the constructed pairing have that formula, for any trivialization in the last statement. |
| `NativePolarization.weil_right`, `weil_perfect` | Vanishing against all elements of `A[n]` forces the quotient torsion point to be zero; the pairing is perfect on both sides for `n > 0`. |
| `NativePolarization.weil_galois`, `weil_compat`, `weil_alt` | The pairing is equivariant, has the compatibility in the exponent, and becomes alternating after composition with the quotient on the right. |
| `wv_eq`, `wv_pow`, `wv_one` | The pairing on all geometric points agrees on torsion, has values killed by `n`, and is trivial at order one. |
| `wv_add_left`, `wv_add_right`, `wv_nsmul_left`, `wv_nsmul_right` | The extended formula is additive and commutes with natural scalars on each torsion group. |
| `wv_compat`, `wv_galois` | The pulled-back finite form obeys the transition identity and commutes with Galois. |
| `tateSeq_mem`, `tatePairing_apply`, `tatePairing_galois` | The values form a compatible tower, give the components of the integral bilinear form, and commute with Galois. |
| `torsion_radical_killed`, `tatePairing_left_ker` | A quasi-inverse kills the finite-level radical by its positive exponent, and the radical on the Tate module is zero. |
| `integral_form`, `rational_form` | The Tate lattice has a separating form with cyclotomic multiplier; the rational Tate module has a nondegenerate form with that multiplier. |
| `tatePolarizationSymmetry_proof` | `TatePolarizationSymmetry`, on the exact local objects used by the degree-one Scholze row. |
| `scholzeH1AbVar_of_dR` | `ScholzeH1AbVarDR → T10Etale.T10_TateDuality → DeRhamScholze.HTMerge.ScholzeH1AbVar`. |

All four modules compile with `lake env lean` on Lean 4.35.0. The [axiom output](../../scratch/tate-polar-sym/axioms.txt) covers all 34 new theorems; each uses only `propext`, `Classical.choice`, and `Quot.sound`.
The [dependency audit](../../scratch/tate-polar-sym/dependencies.txt) checks the transitive proof dependencies for both final theorems and finds no removed Picard input and no use of the old Fil¹ clause. The proof modules do not import `ZInQKernel.OneProof.Main`.

## Count and source issue

The [headline check](../../scratch/tate-polar-sym/discharges.txt) matches `OpenAddedLeaves28.scholzeH1AbVar` exactly. It reports only `ScholzeH1AbVarDR` and `T10_TateDuality` as premises of `scholzeH1AbVar_of_dR`.

The [autofold preview](../../scratch/tate-polar-sym/autofold-dryrun.txt) replaces `scholzeH1AbVar` by `scholzeH1AbVarDR`, rated consequence, GLUE, pending review. Both strict and strictest counts remain **5 LEAF / 26 GLUE** on 31 H rows. The pairing is on-the-spot glue (provenance (c)) and adds no row. No fold was applied.

## Known issues

- **VERIFIED in the manuscript:** L10996 states the numbers without a citation. It omits a justification; no false mathematical assertion was found. The new proof justifies the corresponding number for the filtered comparison object, so the replacement row has no separate Hodge-number clause.
- **VERIFIED from the existing source audit:** the manuscript cites Scholze's 2016 corrigendum, which corrects the period-site definitions. The comparison is used in its corrected form. No primary publication was reread in this task. The journal locators Corollary 1.8 and Theorems 9.1 and 9.3, and the conventional Mumford pairing locators §§20 and 23, are UNVERIFIED here.

## Manuscript check

| Lines in `diophantine_zq.tex` | Verdict |
|---|---|
| L10939–10951 | **OK** — the lemma is stated for a surface; the calculation used here is the one at the field of definition and applies to all dimensions. |
| L10954–10956 | **unverified** — smooth proper analytification and the corrected comparison are invoked in the manuscript; the literature was not reread and the comparison remains an input. |
| L10957–10960 | **unverified** — the algebraic–analytic comparison for the filtered and finite-coefficient models remains in the narrowed row. |
| L10961–10965 | **unverified** — the characteristic-zero invertibility check is correct; the equivariant comparison after inverse limits and rationalization is retained in the narrowed row. |
| L10967–10972 | **OK** — the dual and the direction agree with the unchanged equivariant T10 input. |
| L10973–10994 | **unverified** — closure and descent for the summand are outside the degree-one row calculation. |
| L10996 | **gap filled** — the uncited surface Hodge numbers follow on the comparison side from rank four and cyclotomic self-duality, which balances the two multiplicities. |
| L10997 | **OK** — passing to the dual Tate module gives weights 0 and −1, each twice, in the manuscript's convention. |
| L10998–11000 | **unverified** — the coefficient-embedding and finite-descent conclusions for the summands are outside the new proof. |
