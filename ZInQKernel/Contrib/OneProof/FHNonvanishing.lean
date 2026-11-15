import ZInQKernel.Contrib.OneProof.FHNonvanishing.TwistFE

/-!
# `ZInQ.GZDecomp.FHNonvanishing` from Friedberg–Hoffstein alone

Task gz-fh (report `docs/research/gz-fh.md`). `FHNonvanishing` (hypothesis `hL2` of
`ZInQ.OneProof.frozenTarget`) follows from the single printed leaf
`ZInQ.GZFH.FriedbergHoffsteinB_FE` (Friedberg–Hoffstein, Ann. of Math. 142 (1995), Theorem B,
with the root number written as the sign of the functional equation), with all glue proved:

* `FHNonvanishing/Basic.lean`: the leaf statements, Dirichlet's theorem for the auxiliary
  discriminant `D₀ = −q`, local squares in `ℚ_p` to the Heegner hypothesis;
* `FHNonvanishing/FE.lean`: the functional-equation form of the leaf and the reduction
  `fhNonvanishing_of_printed_fe`;
* `FHNonvanishing/TwistFE.lean`: the twisted functional equation `twistFunctionalEquation`
  (the twist `f ⊗ χ_D` is a `W_{N D²}`-eigenvector with eigenvalue `χ_D(−N) ε_N(f)`).

An alternative with two printed leaves is `ZInQ.GZFH.fhNonvanishing_of_printed`
(`FriedbergHoffsteinB`, `TwistNewformRootNumber`).
-/

namespace ZInQ.GZFH

/-- **`FHNonvanishing` from Friedberg–Hoffstein Theorem B (functional-equation form).** -/
theorem fhNonvanishing_of_friedbergHoffsteinB_FE (hFH : FriedbergHoffsteinB_FE) :
    ZInQ.GZDecomp.FHNonvanishing :=
  fhNonvanishing_of_printed_fe hFH twistFunctionalEquation

end ZInQ.GZFH
