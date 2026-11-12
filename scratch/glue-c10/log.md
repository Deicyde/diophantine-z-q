# glue-c10 results log

- 23:35 Files: scratch/glue-c10/C10.lean (Galois side), scratch/glue-c10/Trace.lean (pkg-I3 defs + trace independence).
- 23:33 C10.lean compiles (lake env lean, no errors; VERIFIED). #print axioms = [propext, Classical.choice, Quot.sound] for:
  iso_of_trace_eq_frob_finite (finite level, from ChebotarevExists + BrauerNesbittChar0),
  frobDense_of_chebotarev (FrobDense S from ChebotarevExists + FrobLift),
  eq_of_eq_on_frob (continuous functions on G_ℚ agreeing on Frobenius outside S are equal, from FrobDense),
  iso_of_trace_eq_on_frob (G_ℚ-level comparison from BrauerNesbittChar0 + FrobDense).
  Open glue: FrobLift (lift of a finite-level unramified Frobenius to a Frobenius in G_ℚ).
- 23:34 C10.lean: added iso_three_of_five (N5's transport 5 → 3: ι₅ injective gives c p = a p, then iso_of_trace_eq_on_frob) and semisimple_of_le (inferInstance). Compiles, axioms standard (VERIFIED).
- 23:36 Trace.lean (pkg-I3 sections 1-2 verbatim + CharPolyIndepOfEll verbatim) compiles; trace_indep_of_ell, trace_eq_trace_of_ell: axioms [propext, Classical.choice, Quot.sound] (VERIFIED). Note: the CommGroup instance on A.Pt needs `open ... MonObj` as in pkg-I3's leaf section.
- 23:37 C10.lean: trace_half (halving step, ρ ≅ r ⊕ r) compiles, axioms standard (VERIFIED).
- 23:40 Lift.lean: restrictNormal_eq_of_frob (step (c) of FrobLift: a G_ℚ-Frobenius at 𝔓 over unramified Q restricts to the Frobenius τ at Q; uses eq_of_isUnramifiedAt + IsFractionRing.div_surjective) compiles, axioms standard (VERIFIED).
- 23:42 Lift.lean: frobLift_of_frobExistsAt (FrobLift from FrobExistsAt via lying-over Ideal.exists_ideal_over_prime_of_isIntegral + step (c)) compiles, axioms standard (VERIFIED). C10.lean FrobLift now has hypothesis p.Prime (identical to Lift.lean's); recompiled OK.
- 23:46 Lift.lean: frobExistsAt_of_finite (FrobExistsAt from FrobExistsFinite by compactness of G_ℚ: FrobOn sets closed, directed by F₁ ⊔ F₂, nonempty via normal closure; every x ∈ Zbar lies in ℚ(x)) compiles, axioms standard (VERIFIED).
- 23:45 Lift.lean: frobExistsFinite (finite layer from Mathlib: IsArithFrobAt.exists_of_isInvariant with Algebra.isInvariant_of_isGalois, liftNormal) and frobLift : FrobLift compile, axioms standard (VERIFIED). FrobLift is now PROVED, no leaf needed.
