# pkg-I4 results log

## Step 1 (2026-11-11): survey of objects
- Mathlib v4.35 (grep of .lake/packages/mathlib), VERIFIED:
  - `Field.absoluteGaloisGroup` with `absoluteGaloisGroup.map` (continuous, gives `G_{ℚ_p} → G_ℚ`).
  - `PadicAlgCl p := AlgebraicClosure ℚ_[p]` (spectral norm), `PadicComplex p = ℂ_[p]` (completion), `PadicComplexInt`.
  - `spectralNorm_eq_of_equiv`: `ℚ_p`-automorphisms of `ℚ̄_p` are isometries.
  - `UniformSpace.Completion.mapRingHom`: extension to `ℂ_p`.
  - `cyclotomicCharacter L p : (L ≃+* L) →* ℤ_[p]ˣ`.
  - `BDeRhamPlus R p`, `BDeRham R p` (RingTheory/Perfectoid/BDeRham.lean): rings only; no Galois action, no filtration, no `ℚ_p`-algebra instance; TODO list in file. `fontaineTheta` has no naturality lemma; `AdicCompletion.map` is linear over a fixed ring and ideal only.
  - Modular forms: `CuspForm`, `Gamma0/Gamma1`, `qExpansion`, `petersson` (integrand only). No Hecke operators, no old/new spaces, no Petersson integral.
  - No `B_st`, no de Rham/pst predicates, no Tate modules of abelian varieties, no `J₁(N)`, no ℓ-adic conductors.
- Pan Thm 1.0.4 hypothesis is *potentially semistable* (not de Rham): h-a011 §1.1 (VERIFIED there from arXiv v2). So Berger is needed to pass from de Rham (C3) to Pan.
- hdec-faithful (origin/wip/hdec-faithful) already has cheap Galois/eigenform definitions and L27a, L27b, L28a; reused in §0/§2.

## Step 2: scratch/pkg-I4/I4.lean
- COMPILES (`lake env lean`, ~15 s after cache), no errors; `#print axioms` of `weight_match`, `weight_match_coh`, `cpAct_algebraMap`: propext, Classical.choice, Quot.sound.
- New genuine definitions: `GQp`, `decomp`, `restrictLocal`, `cpAct` (G_{ℚ_p} on ℂ_[p], proved continuous via isometry), `cyc`, `cycPow`, `htSpace` (Submodule; closure proofs done), `htMult`, `HasHTWeights`, `LocalHasHTWeights`, `HasHTWeightsAtSelf`, `DistinctHTWeights`; `scaleH`, `oldSpace`, `IsNewform`; `GaloisChar`, `AttachedUpToTwist`, `FinitelyRamified`.
- Leaves statable now (def : Prop): EigenformRepExists, EigenformHT (new: statable thanks to htMult), DeligneSerreFinite, EigenformTwist, NewformOfEigenform (new), CarayolUnramified (new).
- Templates (not leaves): PanFor IsPst, BergerFor IsDR IsPst, CarayolFor a.
- Glue proved: weight_match (Tate normalization, multisets), weight_match_coh (Pan normalization).

## Step 3: research note docs/research/pkg-I4.md (first version)
- Per-input analysis §1 (10 inputs), readings §2 (Pan trace form: normalization-independence argument; pst vs dR and the merged leaf Pan∘Berger; HT convention check V=ℚ_p(1) ↦ weight −1; newforms via old space), Lean §3, coarse alternative §4, glue §5, obstacle §6.
- Correction recorded: Pan's hypothesis is pst (h-a011 §1.1), not de Rham (task statement, wk-h §2).
- Correction recorded: HT representations are cheap over Mathlib v4.35 (wk-h §3.1 and hdec-faithful said "large").

## Step 4: scratch/pkg-I4/DeRham.lean
- PROVED (compiles; axioms propext, Classical.choice, Quot.sound): for any ring map f : R →+* S between p-adically complete rings (with ¬IsUnit p): `modPMap`, `preTiltMap` (R♭ → S♭), `untilt_preTiltMap` (naturality of untilt, via `Perfection.teichmuller_spec`), `fontaineTheta_naturality` (θ_S ∘ W(f♭) = f ∘ θ_R, via `WittVector.eq_of_apply_teichmuller_eq` mod p^n and Hausdorffness). ~70 lines.
- FINDING: Mathlib has no `IsAdicComplete (span {p}) 𝓞_ℂ_[p]` (nor `Fact ¬IsUnit p`) instance, so `BDeRham (PadicComplexInt p) p` does not typecheck yet; this is an extra piece for IsDR.
