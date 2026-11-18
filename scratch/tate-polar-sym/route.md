# Native route audit

VERIFIED against the base source.

| Old use | Native replacement | Work at the interface |
|---|---|---|
| A very ample class over the base field | `nativeProjectiveEmbeddingExists_proof` and the pullback of `O(1)`; the older `T09Pic.exists_isVeryAmple` independently supplies a class. | The ample bundle is over the original field. `AbVar` itself stores properness, smoothness and geometric integrality; projectivity is a theorem. |
| The `PicRepresentableAbVar` family and the `PicZeroAbVar0` target of `phiAmpleIsogeny0_of_open` | The native finite stabilizer quotient `A → A/K(L)` from `StabilizerAbVarQuotientExists_proof`, with `ReducedGlobalNormalizedSeesaw_proof`. | Use its finite and surjective map as the isogeny. It already has the right dimension and is defined over the base field. No dimension argument involving a represented Picard functor is needed. |
| Identifying points of the Picard-zero target with distinct classes | `exists_quotientPolarizationBundle`, `nativeQuotientDescentCompatibility_of_seesaw`, and `quotientBundle_fieldPoint_injective`. | Specialize the descended class at geometric points and compare it with the existing `PicDict.phiPt` formula. |
| Group law and translation invariance of those classes | `NativeTheoremOfTheSquare_proof`, and lifts of geometric points through a finite surjection. | Prove the Picard class map is multiplicative; it takes torsion points to torsion classes. |
| Multiplication pullback of a translation invariant class in `weilNondegRight0_of_open` | `mul_pullback_class_of_translationInvariant`, from native seesaw. | Iterate along the diagonal to identify `[n]^*M` with `M^n`; the original `formula_nondeg_right` can then be used with a trivialization. |
| `WeilPairingMumford0`: finite-level formula, compatibility and equivariance | `mumfordWeilPairingAC_proof`, `mumfordWeilCompat_of_pairing`, `weilFormulaGaloisEx`, plus the native quotient classes. | `NativePolarization.weil` supplies the family of quotient torsion pairings. Right separation follows by formula descent and injectivity of quotient classes. Equal dimensions and torsion counting give left separation. |
| `t09SymmIsogenyExists0_of_four0`, then `tatePairingZl_field0` and `tateGSp_field0` | The native quotient isogeny, its finite-level form and the existing Tate tower and scalar extension arguments. | `WeilDual.dualEnd` concerns adjoints to every endomorphism. It is unnecessary for this task. Use the finite-level data actually required by the Tate pairing instead of manufacturing a `WeilDual`. |

No manuscript error was found in this step. L10996 gives the Hodge numbers without justification; the pairing proof supplies that justification on the comparison side.
