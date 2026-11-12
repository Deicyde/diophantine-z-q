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
