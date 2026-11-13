# tc-survey results log

Task tc-survey (2026-11-13). Read-only survey of Tau Ceti (~/tc-main 4d91513e, Lean v4.36.0-rc2,
2026-11-13; ~/tc-oct16 5a01f5fe, Lean v4.35.0) against the open leaves of
docs/research/h-decomposition.md (base 883c4ddf).

## Leaf status at base (VERIFIED from docs/research/*.md at 883c4ddf)
- Proved elsewhere (not to survey in depth): T2 (t-brauer-purity), T13, T19 (t-skolem-kw),
  T20/T21 local forms, T22a/b (t-different), T32 (glue), T12 (glue target), T30 = glue from T16
  (t30-adelic). T15 real-place conjunct proved (t-brauer-purity).
- In progress elsewhere: T18 (cheb-bridge), T17 (kw-new), T16 (lkw), T20/T21 global (diff-bridge);
  other host: T14, T15, T1, T2, T10, T28.

## Findings
### Tooling
- `scratch/tc-survey/clos.py ROOT MOD...`: closure size + count of modules NOT already vendored on
  origin/wip/kw-new (d639402b; 1162 files under ZInQKernel/Contrib/TauCeti, list in
  `scratch/tc-survey/vendored-kwnew.txt`). VERIFIED: tc-port vendored port1 (397) and 714 oct16
  modules of kw-rest; kw-new vendored the 44 nov01 modules.

### In-progress leaves (brief)
- T18: TC `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet (C : ConjClasses (L ≃ₐ[K] L)) :
  NumberField.Set.HasNaturalDensity (frobeniusPrimeSet K L C) ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L))`,
  oct16 `Chebotarev/PrimeCounting/FrobeniusPrimeCount.lean:108` (VERIFIED read). Leaf `PkgI6.ChebotarevExists`
  (exists p ∉ S unramified, Q | p, IsArithFrobAt σ Q) is a CONSEQUENCE (density > 0 ⇒ infinitely many):
  DIFFERENT OBJECTS (frobeniusPrimeSet vs IsArithFrobAt; bridge = cheb-bridge). Closure oct16: 292
  modules, 57.6k lines, 0 not vendored (VERIFIED, clos.py).
- T17: TC `TauCeti.ClassFieldTheory.kroneckerWeber (E : Type) [Field E] [NumberField E] [IsAbelianGalois ℚ E] :
  ∃ n : ℕ, n ≠ 0 ∧ Nonempty (E →ₐ[ℚ] CyclotomicField n ℚ)` (tc-main ClassFields/KroneckerWeber.lean:178;
  not at oct16). Leaf `KroneckerWeber`: IsGalois + commuting automorphisms, n : ℕ+. SAME up to
  IsAbelianGalois ↔ (IsGalois ∧ commutative) and ℕ+ ↔ n ≠ 0 (cheap bridge). Closure nov01: 949, 0 not
  vendored; main: 1035 modules, 86 not vendored (VERIFIED).
- T20 global: TC `IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one :
  multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) = ∑ᶠ i : ℕ, (Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i) - 1)`
  (oct16 LocalGlobal/Different/Exponent.lean:239). Leaf `GlueConductor.HilbertDifferentFormula`: ∃ n, G_n = ⊥ and exact
  power ∑_{i<n}(|G_i|-1). DIFFERENT OBJECTS (TC ramificationGroup vs leaf `(P^(i+1)).inertia`; finsum vs finite
  sum + existence of n): bridge = diff-bridge. Closure 156 (Exponent+Permutation), 0 not vendored.
- T21 global: TC `multiplicity_differentIdeal_le_ramificationIdx_sub_one_add_multiplicity_span :
  multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) ≤ e - 1 + multiplicity w.asIdeal (span {(e : 𝓞 L)})`
  (oct16 LocalGlobal/Different/Wild.lean:47). Leaf `GlueConductor.SerreDifferentBound`:
  ¬ P^(e-1+e·v_p(e)+1) ∣ D over ℚ. SAME after bridge v_P(e) = e·v_p(e), multiplicity ↔ ∣. Closure Wild:
  177 modules, 11 not vendored (1.2k lines) (VERIFIED).
