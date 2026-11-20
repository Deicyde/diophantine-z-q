# Fixed scale via the period subgroup

**Scoped stop at the independent modular realization.** For the fixed non-CM lattice, `rational_of_modularToWeakWeil` proves that the original `κ` is rational given the existing open `ModularToWeakWeil` input. The precise input needed for the period comparison is `∃ r : ℚ, IsParamScale N f Lat (r : ℂ)`.

The inherited Milne audit identifies a citation error at tex 1784 and 1788: the cited pair does not give the full normalized newform assertion or state the Hecke equality. No new mathematical error was found.

The scaled period subgroup contains an integer multiple of the full lattice. This lets the non-CM multiplier condition compare any independent rational scale with `κ`. The Jacobian bridge extracts a reference scale from an independent map `aj0 ≫ φ` and its analytic comparison at any nonzero scale. Supplying that map and identifying its differential on the rational model at tex 1779–1787 remain open.

All four proof modules and both audit files compile. The five wrappers derive their scale witnesses for the prepared, missing, ring, genus and Elkik results. All 16 axiom entries contain only the three standard axioms. The seven audited proof closures contain 11,092 project declarations in total and have no witness-consuming `ParamJoin` or `AtScale` dependency. See `docs/research/rc-kappa-rational2.md`.
