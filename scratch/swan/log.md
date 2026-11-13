# swan log

Task: SwanIndependent, SwanIntegral, AdaptedExists (kernel `ZInQKernel/HDecomp/Conductor/LadicCond.lean`,
used by scratch/g0-mod-newform G15). Lean: scratch/swan/Swan.lean (imports the kernel module only).

## Statements (verbatim copies in Swan.lean §0, `rfl`-checked against `LadicCond.*`)

## Truth analysis (by hand)
- AdaptedExists: TRUE. Elementary proof: wild γ has p-power order on each finite Galois level
  (trace trick: T x = Σ_{j<m} δ^j x is norm-preserving for p ∤ m, so injective, so onto, image δ-fixed);
  ultrametric estimate ‖((1+A)^{p^k} − 1)_{ij}‖ = ‖A_{ij}‖ for the max entry when ‖A‖ < 1 and ℓ ≠ p;
  continuity gives finite Galois L with ρ(G_L) ⊆ {‖g − 1‖ < r}. No Baire, no compactness. SPECULATIVE until compiled.
- SwanIntegral: TRUE (Serre, Corps locaux IV §3, VI §2; Serre–Tate 1968 §2; numbering UNVERIFIED). Continuity
  and p ≠ ℓ are not needed; only adaptedness.
- SwanIndependent: TRUE for any field k and any (not necessarily continuous) hom; same proof (both levels have the
  integral over the absolute upper filtration).

## Compile outcomes
- 04:35 Swan.lean §0-§2 (verbatim copies + rfl, wild p-power order `wild_pow_fix`, matrix estimate `Bd.pow_sub`): compiles, no errors. VERIFIED.
- 04:45 **AdaptedExists PROVED**: `Swan.adaptedExists : LadicCond.AdaptedExists (p := p)` compiles, `#print axioms` = [propext, Classical.choice, Quot.sound]. VERIFIED (lake env lean scratch/swan/Swan.lean, exit 0, no sorry).
