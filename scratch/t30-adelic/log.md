# t30-adelic results log

## T30 (LeafSqrtCrit from LocalKroneckerWeber)
- 22:40 SqrtCrit.lean part 1 compiles (VERIFIED, `lake env lean`): roots-of-unity CRT (`act_crt`),
  `exists_emb` (resp p σ is restriction along an embedding ℚ̄ → ℚ̄_p), `cyc_resp_eq`,
  `cyc_resp_eq_one`, `cyc_resp_eq_u` (σ inverts μ_{p^k}, fixes μ_{N'} ⇒ cyc_N(resp σ) = u),
  `act_of_gal` (action through `galToProd` at level ℚ_p(μ_{p^k m})).
- 22:45 SqrtCrit.lean COMPLETE (VERIFIED, `lake env lean`, 8 s): 
  `T30.leafSqrtCrit_of_localKroneckerWeber (hLKW : ∀ p : Nat.Primes, PkgI6.LocalKroneckerWeber p) : GlueDescent.B2Q.LeafSqrtCrit`.
  `#print axioms`: [propext, Classical.choice, Quot.sound]. No sorry.
  Pieces: `sqrt_of_chi'` ("if", no LKW: inflation from L = ℚ_p(μ_{p^{k+1}(p^{2f}-1)})),
  `chi_of_sqrt'` ("only if": fixed field M of ker φ is finite abelian, LKW puts M in ℚ_p(μ_{p^a b}),
  lift τ₋₁ from ℚ_p(μ_{p^{k+a} N' b}); σ² ∈ ker φ), `exists_sqrt_iff` (ℂˣ divisible ⇒ Baer),
  `restrict_sq_eq_one` (two-torsion part of `sqrt_criterion_level`, copied).
  Kernel pitfall found: `rfl` for `((algebraMap (muField a) (muField b) y : _) : ℚ̄_p) = y` is a
  kernel deterministic timeout (kernel compares the carriers muField a vs muField b); fix: go through
  `IntermediateField.inclusion` + `coe_inclusion`.
