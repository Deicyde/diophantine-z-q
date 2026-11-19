# Results log

- VERIFIED: worktree starts at `15c9e93d3`. The requested row is in `TailZ87.lean`; the adjacent
  character-polynomial and standard-model rows are out of scope.
- VERIFIED by source search: the tree has composite Hecke operators on modular forms and abstract
  double-coset rings. The Jacobian interface has independent prime and diamond actions; `xiSq` is
  defined as the ring expression. No independent action for composite ξ_n on this Jacobian found.
- STANDARD (Dirichlet, Mathlib `Nat.forall_exists_prime_gt_and_eq_mod`): two distinct primes in a
  prescribed unit class allow integral reverse generation by Bézout.
- VERIFIED (Lean): the positive integer multiple of an endomorphism has the same
  scheme-theoretic image. The two generated subrings agree integrally, and the image
  families and quotient universal properties agree under `HeckeRelations`.
- VERIFIED (Lean): the normalized coefficient recurrences and the composite
  operator laws extend clause (ii) from prime and good-square indices to every
  positive index. The reverse restriction uses the independently stated square relation.
- VERIFIED (Lean): every competitor kills the annihilator, including cancellation in
  rationalized endomorphisms. It therefore factors through the constructed quotient.
  `KerConnected` makes the factor an isomorphism if it is finite.
- Scoped stop: `SameDimSurjectiveFinite` states exactly the finiteness input; the missing
  Lean argument is generic fibre dimension and its transport to other fibres.
- VERIFIED (Lean): the print form and the two named GLUE inputs imply the exact
  `R16Thm1b.ShimuraThm1Af` type.
- VERIFIED: the final contribution compiles with `lake env lean`; all 39
  `#print axioms` entries use only standard axioms (see `Axioms-output.txt`).
- VERIFIED: the stock `#discharges` command matches the exact row type in
  `DischargesFocused.lean`. The full assembly check is provided separately; the
  cached assembly is from `TailZ62` and the `TailZ87` assembly has 2,276 missing
  local import artifacts. The full assembly check was not run.
- VERIFIED: `autofold.py --dry-run` rejects 5/24 → 6/25 in both counts.
  No fold or count change.
