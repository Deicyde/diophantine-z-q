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
- 04:55 §5 reduction compiles: `swanIntegral_of`, `swanIndependent_of`, `swan_all` from
  H1 `SwanAtIntegral` (finite-level change of variables), H2 `UpperAbsWild` (G^u ⊆ P for u>0),
  H3 `UpperAbsSurj` (G^u → G^u(L) onto). Axioms standard. VERIFIED.
  Key lemma `invariants_upperAbs`: V^{G^u} = V^{G^u(L) ∩ P} for L adapted, u > 0.
- 05:05 §6 compiles: `upperAbsSurj_of_herbrand : HerbrandUpper → UpperAbsSurj` (finite intersection
  property + Mathlib's `CompactSpace Gal(K/k)` for Galois K/k), `swan_all'` (H1, H2, HerbrandUpper ⇒ all
  three). Leaf `HerbrandUpper` = Serre IV §3 Prop. 14 (UNVERIFIED numbering) over LadicCond's upperSet;
  same theorem as PkgI6.HerbrandQuotient (I6.8). Axioms standard. VERIFIED.
