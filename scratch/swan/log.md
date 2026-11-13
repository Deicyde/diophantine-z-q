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
- Swan.lean §0-§2 (verbatim copies + rfl, wild p-power order `wild_pow_fix`, matrix estimate `Bd.pow_sub`): compiles, no errors. VERIFIED.
- **AdaptedExists PROVED**: `Swan.adaptedExists : LadicCond.AdaptedExists (p := p)` compiles, `#print axioms` = [propext, Classical.choice, Quot.sound]. VERIFIED (lake env lean scratch/swan/Swan.lean, exit 0, no sorry).
- §5 reduction compiles: `swanIntegral_of`, `swanIndependent_of`, `swan_all` from
  H1 `SwanAtIntegral` (finite-level change of variables), H2 `UpperAbsWild` (G^u ⊆ P for u>0),
  H3 `UpperAbsSurj` (G^u → G^u(L) onto). Axioms standard. VERIFIED.
  Key lemma `invariants_upperAbs`: V^{G^u} = V^{G^u(L) ∩ P} for L adapted, u > 0.
- §6 compiles: `upperAbsSurj_of_herbrand : HerbrandUpper → UpperAbsSurj` (finite intersection
  property + Mathlib's `CompactSpace Gal(K/k)` for Galois K/k), `swan_all'` (H1, H2, HerbrandUpper ⇒ all
  three). Leaf `HerbrandUpper` = Serre IV §3 Prop. 14 (UNVERIFIED numbering) over LadicCond's upperSet;
  same theorem as PkgI6.HerbrandQuotient (I6.8). Axioms standard. VERIFIED.
- 04:36 §7 part 1 compiles: `wildAt_of_ramSet_one` (σ ∈ ramSet L 1 ⇒ ‖σx−x‖<‖x‖ on L^×), WildAt closure. VERIFIED.
- §7 compiles: **H2 `UpperAbsWild` PROVED** (`Swan.upperAbsWild`): `upperSet_subset_ramSet_one` (ψ_L(u) > 0 via
  t/g_0 ≤ φ_L(t) ≤ t·|Gal|/g_0 for t ≥ 0, φ_L ≤ 0 on [−1,0]; antitone integrand ⇒ interval integrable),
  `wildAt_of_ramSet_one`, `exists_finGal_mem` (normal closure of ℚ_p(x)). VERIFIED.
- §8 `swan_final (h1 : SwanAtIntegral) (hH : HerbrandUpper)` : SwanIndependent ∀p ∧ SwanIntegral ∧ AdaptedExists ∀p.
  Axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- §7b compiles: **H1 `SwanAtIntegral` PROVED** (`Swan.swanAtIntegral`): φ_L(j) = Φ_j = Σ_{i≤j} g_i/g_0
  (`phiAt_nat`), φ_L affine on [j, j+1] (`phiAt_piece`), G^u(L) = G_{j+1}(L) for Φ_j < u ≤ Φ_{j+1}
  (`upperSet_eq`), integrand = Σ_j c_{j+1}·1_{(Φ_j,Φ_{j+1}]} on (0,∞), integral = Σ c_{j+1}(Φ_{j+1} − Φ_j).
- **`swan_main (hH : HerbrandUpper)` : SwanIndependent ∀p ∧ SwanIntegral ∧ AdaptedExists ∀p.** Axioms
  [propext, Classical.choice, Quot.sound]. `lake env lean scratch/swan/Swan.lean` exit 0, 0 errors
  (only deprecation warnings for if_pos/if_neg). Output in scratch/swan/compile.out. VERIFIED.
- Leaf `HerbrandUpper` weakened to `0 < v` (only range used). Recompiled: exit 0, 0 errors, all 10 printed declarations standard axioms. VERIFIED.
- Bridge.lean compiles (exit 0, 0 errors): `SwanBridge.herbrandUpper_of_quotient : PkgI6.HerbrandQuotient → HerbrandUpper`
  (verbatim copy of Swan.HerbrandUpper). 𝓞_E = {x ∈ E : ‖x‖ ≤ 1} as Subalgebra ℤ_[p] ℚ̄_p; IsIntegralClosure (integral ⇔
  ‖·‖ ≤ 1 via spectralValue_le_one_iff); DVR via ofHasUnitMulPowIrreducibleFactorization; Module.Finite via
  IsIntegralClosure.finite; IsGalois (FractionRing ℤ_p) (FractionRing 𝓞_E) via IsGalois.of_equiv_equiv; res E =
  galRestrict ∘ restrictNormalHom, surjective; lowerRam ↔ ramSet, Nat.card lowerRamR = ramCardR, herbrandPhi = phiAt,
  upperRam ↔ upperSet. Axioms standard. VERIFIED.
- Kernel I6Base definitions lowerRam, mem_lowerRam, lowerRamR, herbrandPhi, upperRam, lowerRam_tower, HerbrandQuotient
  are character-for-character equal to scratch/t-different/Herbrand.lean (python comparison). VERIFIED.
- **All.lean** (build.sh: kernel imports + t-different Herbrand.lean lines 60-1248 + proof of PkgI6.herbrandQuotient +
  Swan.lean + Bridge.lean + final_part.lean), 2713 lines: `lake env lean scratch/swan/All.lean` exit 0, 0 errors, ~33 s.
  **`Swan.swanIndependent_proved`, `Swan.swanIntegral_proved`, `Swan.adaptedExists_proved`, `Swan.swan_proved`: axioms
  [propext, Classical.choice, Quot.sound].** Output: scratch/swan/all_compile.out. VERIFIED.
