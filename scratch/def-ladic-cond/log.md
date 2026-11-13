# def-ladic-cond results log

## LadicCond.lean (`lake env lean scratch/def-ladic-cond/LadicCond.lean`)

- 23:50 PST: compiles, no `sorry`, no errors (one deprecation warning). VERIFIED (compiled).
- Axioms of every proved theorem: [propext, Classical.choice, Quot.sound]. VERIFIED.
- Definitions (Part B, on `PkgI4.GQp p = Gal(ℚ̄_p/ℚ_p)`, norm of Mathlib's `PadicAlgCl p`):
  `inertiaSet`, `wildSet`, `fixSet L`, `IsUnif`, `ramSet L i` (preimage of `G_i(L/ℚ_p)`),
  `ramCard L i` (= `|G_i(L/ℚ_p)|`, as `Nat.card` of restrictions to `L`), `IsFinGal`,
  `invariants`, `codimInv`, `IsAdapted`, `swanAt`, `swan`, `condExp`, `condAt`, `artinAt`,
  `ramSetR`, `ramCardR`, `phiAt`, `upperSet`, `upperAbs`.
- Proved: `wildSet_subset_inertiaSet`, `codimInv_eq_zero`, `swanAt_eq_zero_of_unramified`,
  `condExp_eq_zero_of_unramified`, `condAt_eq_zero_of_unramified` (sanity a);
  `invariants_eq_of_cover`, `condAt_eq_artinAt` (sanity b, from the stated Props
  `InertiaRestriction L`, `EventuallyTrivial L N`, `ramCard L 0 ≠ 0`);
  `condExp_eq_condAt` (from `SwanIndependent`); `carayolR17_of_R17'`, `carayolR17'_of_R17`.
- Stated, not proved (glue): `SwanIndependent`, `AdaptedExists`, `InertiaRestriction`.
- Leaves stated: `CarayolR17` (∀ adapted level), `CarayolR17'` (canonical `condExp`),
  `SwanIntegral` (L8).
- Fix needed on first compile: `(decomp p).continuous` does not exist; used
  `(Field.absoluteGaloisGroup.map _).continuous_toFun`. VERIFIED.
- 23:52 PST: added `codimInv_le`, `integral_codim_le` (right side of L8 `≤ n·U` when `ρ` is trivial
  on `G^u`, `u > U`; non-integrable case via `integral_undef`), `condAt_le_of_upper`
  (`a(ρ) ≤ n(1+U)` from `SwanIntegral`): glue-conductor D4(i) consumer. Compiles, axioms
  [propext, Classical.choice, Quot.sound]. VERIFIED.
- 23:53 PST: added non-degeneracy checks `fixSet_subset_ramSet`, `isAdapted_one`, `condExp_one`, `one_mem_wildSet`. Compiles. VERIFIED.
- 23:55 PST: added and proved `apply_mem` (conjugates stay in a finite Galois `L`, via
  `IntermediateField.normal_iff_forall_map_le'`), `inertiaSet_subset_ramSet_zero` (first clause of
  `InertiaRestriction`), `norm_p_kbar`, `isUnif_bot` (`p` is a uniformizer of `ℚ_p`: `IsUnif` is
  satisfiable), `finite_restr`, `ramCard_ne_zero` (`g_i ≠ 0`), `condAt_eq_artinAt'` (sanity (b)
  with only the two surjectivity clauses and eventual triviality as hypotheses). File compiles with
  no errors and no `sorry`; 12 `#print axioms`, all [propext, Classical.choice, Quot.sound]. VERIFIED.
- 23:57 PST: proved `IsUnif.norm_eq`, `eventually_not_restr`, `eventuallyTrivial`
  (`G_i(L/ℚ_p) = 1` for large `i`, every finite Galois `L` with a uniformizer; by
  `Set.Finite.induction_on` over the finitely many restrictions), and `condAt_eq_artinAt''`
  (sanity (b) assuming only the two surjectivity facts). Compiles (rc 0, no errors, no `sorry`);
  14 `#print axioms`, all [propext, Classical.choice, Quot.sound]. VERIFIED.
- 23:58 PST: proved `norm_pow_factorial` (`‖y‖^{[L:ℚ_p]!} ∈ p^ℤ` for `y ∈ L^×`, from Mathlib's
  `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`), `exists_isUnif` (every finite `L ⊆ ℚ̄_p`
  has a uniformizer, via `Nat.find`), `condAt_eq_artinAt_of_surj` (sanity (b) for every finite
  Galois `L`, hypotheses: only the two surjectivity facts). First attempt failed: the lemma lives in
  namespace `spectralNorm`. Compiles (rc 0, no `sorry`); 16 `#print axioms`, all
  [propext, Classical.choice, Quot.sound]. VERIFIED.
