# rc-eis-form results

- Base: 007d8d6d06a70c116f2f310b426406f2c6017b0b.
- Inherited Frobenius calculation: `O12EisConst.normalizedRep_good` already proves trace and determinant before an analytic form is attached.
- Available Mathlib: weight-two Lipschitz formula, Lambert regrouping; modular construction at principal level only for weight at least three; level-one E2 has a slash correction.
- Inherited issue at tex 9660–9668: a coefficientwise integral Hecke image is not thereby in the diamond-only span.
- Analytic arithmetic: divisor antidiagonal converted to sum over the second argument; norm bound n².
- Verified preliminaries: absolute disk summability, formal radius at least one, HasSum on the upper half plane, holomorphy, period one, boundedness at infinity.
- Remaining analytic proposition: one constant term making the Gamma0 slash law and all non-infinity Gamma1 cusp bounds hold.
- Occurrence interface: one nonzero actual column, labeled complex old line, source level, and compatible coefficient lift; scale recovered at the degeneracy degree.
- First compile pass located elaboration and coercion errors; final pass below records the corrected theorem audits.
- Attachment.lean: PASS (10 theorem audits, only propext, Classical.choice, Quot.sound).
- Occurrence.lean: PASS (4 theorem audits, only propext, Classical.choice, Quot.sound).
- Verified checkpoint: d0abf0a1b (attachment and occurrence).
- Expansion.lean: PASS (10 audits). Width-one Taylor coefficients are the prescribed constant and all ordered divisor sums.
- Lipschitz.lean: PASS (7 audits). Absolute Lambert regrouping; primitive Gauss normalization; equality with Mathlib's weight-two lattice rows.
- Modularity.lean: PASS (5 audits). Both actual pair orders match the lattice rows; slash law and other cusp bounds produce the exact BaseForm.
- Attachment.lean: PASS after generalizing to a common finite avoid set (10 audits). Split Frobenius polynomial and primitive/old Hecke recursion; model RepInput for the explicit split choice.
- Occurrence.lean: PASS (4 audits). Descended nonzero scale, block membership of the normalized old vector, ColumnRealization and RealizedCoordinate.
- Final audit: 36/36; exactly propext, Classical.choice, Quot.sound; no Lean warnings or errors.
