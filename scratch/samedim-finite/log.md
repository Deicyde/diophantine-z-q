# Results log

- VERIFIED (source): base `248d50d4a` gives the exact `ShimuraSteps.SameDimSurjectiveFinite`
  proposition over `PkgI3.AbVar`; `dim` is absolute topological Krull dimension.
- VERIFIED (source): `Dim.FunctionField` compares Krull dimension and transcendence degree;
  Mathlib has essential finite type of stalk maps, additivity of transcendence degree,
  and the proper quasi-finite criterion. `PicDict.finiteOfFiniteKerPts` supplies that
  criterion for abelian variety homomorphisms with finitely many geometric kernel points.
- VERIFIED (source): the manuscript invokes Shimura's construction and Euler-factor identity
  at L770–773. It gives no uniqueness proof. The prior page read records the p. 526 misprint
  in the conjugate-form sentence; it is outside the quotient clauses used here.
- VERIFIED (Lean): `SameDimFinite.lean` compiles with no warnings. The equal-dimension
  comparison gives quasi-finiteness at the generic point, then a finite generic fibre.
  Translation after field extension gives finitely many geometric kernel points.
- VERIFIED (Lean): `ShimuraSteps.sameDimSurjectiveFinite : ShimuraSteps.SameDimSurjectiveFinite`;
  `ShimuraSteps.shimuraThm1Af_of_printed'` takes only the print form and the Hecke bridge.
- VERIFIED (Lean): `Axioms.lean` lists only `propext`, `Classical.choice` and `Quot.sound`
  for all eleven new theorems. `DischargesFocused.lean` matches the exact quotient row
  type and reports that the new theorem assumes only `ShimuraThm1AsPrinted` and
  `ShimuraHeckeRelations`. The full assembly was not checked.
- VERIFIED (dry run): strict and strictest both change from 5 LEAF / 24 GLUE (29 rows)
  to 6 LEAF / 24 GLUE (30 rows). No files in the assembly were changed.
