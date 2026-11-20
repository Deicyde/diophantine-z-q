# T10 / Milne 1986 results

- Base: `ae799aef495474d2dfaf16cd8581375011623230`.
- Target: `HDec.HSyn.OpenAddedLeaves28.t10TateDuality : T10Etale.T10_TateDuality`.
- `EllAdicCohomology`: small pro-étale site; coefficients `U ↦ C(U, ℤ_ℓ)`; integral comparison absent from base.
- `T10Milne86.EtaleH1`: inverse limit of `H¹` on the classical étale side with constant `ZMod (ℓ ^ n)` coefficients.
- `T10Milne86.etalePull`: pullback via the first argument of Ext; commutes with change of coefficients.
- `T10Milne86.Milne86Thm15_1a`: `H¹_et(A_Kbar, ℤ_ℓ) ≃ₗ (T_ℓ A)^∨`, natural for abelian variety homomorphisms over `K`; printed locator and wording UNVERIFIED.
- Missing: integral degree-one comparison natural for `1 × Spec(σ)` in the row's conventions; semilinear naturality of the same Milne isomorphism.
- Manuscript `diophantine_zq.tex:10967–10972`: equivariance citation gap; the local audit separately names Remark 12.5 (UNVERIFIED).
- Row status: GLUE; no focused `#discharges`.
- Build 1: failed on the topology's universe argument and missing `MonObj` namespace (with cascading errors).
- Build 2: failed on the small model universe and missing abelian Grothendieck instances.
- Build 3: site and Ext instances resolved; remaining failures in coefficient arithmetic and a missing degree argument in Ext associativity.
- Build 4: the Ext composition lemmas passed their axiom checks; two scalar proofs needed a qualified identity lemma and a definitional equality.
- Build 5: `lake --old --no-cache --log-level=info build ZInQKernel.Contrib.OneProof.T10Milne86.Printed` succeeded; only module style warnings from the imports.
- `#print axioms`: `etalePull`, `changeCoeffs_comp`, `finitePull_changeCoeffs`, `Milne86Thm15_1a` each report `[propext, Classical.choice, Quot.sound]`.
