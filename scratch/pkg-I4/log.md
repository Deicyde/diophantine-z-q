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
- Step 4b: DEFINED and compiled (standard axioms): `adicMap` (ring map of adic completions for g(J) ⊆ J', via `AdicCompletion.liftRingHom`; `factorPow_evalₐ` proved), `locMap`, `locMapBase`, `fontaineThetaInvertP_naturality` (proved), `ker_le_comap_locMap` (proved), `bdrPlusMap : BDeRhamPlus R p →+* BDeRhamPlus S p` (functoriality of B_dR^+). ~150 lines total in DeRham.lean.
- Step 4c: PROVED (standard axioms), merged into DeRham.lean (namespace PkgI4.Cp): `mem_O_iff` (x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1), `norm_p`, `mem_span_pow_iff` (x ∈ p^n𝓞 ↔ ‖x‖ ≤ ‖p‖^n), `smodEq_iff`, instances `notIsUnit_p : Fact ¬IsUnit (p : 𝓞_ℂ_[p])`, `isHausdorff`, `isPrecomplete`, `isAdicComplete`. So `BDeRham (𝓞_ℂ_[p]) p` now typechecks.
- Step 4d: PROVED/DEFINED (standard axioms): inverse-pair lemmas (`modPMap_comp_eq_id`, `preTiltMap_comp_eq_id`, `wittMap_comp_eq_id`, `locMap_comp_eq_id`), `ker_eq_span_locMap` (generators of ker θ[1/p] go to generators under an isomorphism), `adicMap_evalₐ`, `adicMap_of`, `genMonoid` (the submonoid Mathlib's `BDeRham` inverts), `genMonoid_le_comap`, `bdrMap` (functoriality of B_dR for ring isomorphisms).

## Step 5: de Rham predicate in I4.lean (DeRham.lean merged into I4.lean; Cp.lean merged earlier)
- DEFINED/PROVED (compiles; `#print axioms` of `bdrAct_qpToBdR`, `IsDeRham`: propext, Classical.choice, Quot.sound):
  `continuous_cpAct`, `norm_cpAct` (isometry on ℂ_p), `cpAct_inv_apply`, `oAct` (σ on 𝓞_ℂ_[p]), `BdR p := Localization (genMonoid p 𝓞_ℂ_[p])` with `example : BdR p = BDeRham 𝓞_ℂ_[p] p := rfl`, `bdrAct` (G_{ℚ_p} on B_dR), `isLocalization_padic` (ℚ_p = ℤ_p[1/p]), `zpToW`, `qpToLoc`, `ofLoc`, `qpToBdR` (ℚ_p → B_dR), `bdrAct_qpToBdR` (G fixes ℚ_p), `Algebra ℚ_[p] (BdR p)`, `bdrAct_smul`, `ddrSpace` (Hom_{ℚ_p}(V, B_dR)^G = D_dR(V^∨), submodule proofs done), `IsDeRham` (finrank = n[E:ℚ_p]), `LocalIsDeRham` (ℚ̄_p-valued, ∃ finite E).
- Size of the whole de Rham layer (Cp + DR + §1b): ~420 lines.
- Step 5b: `PanBerger : Prop := PanFor (LocalIsDeRham)` — Pan∘Berger leaf statable now over genuine definitions; `BergerDR IsPst` template. File compiles, 955 lines, no `sorry` anywhere; `#print axioms PkgI4.PanBerger`: propext, Classical.choice, Quot.sound.

## Step 6: research note updated
- Summary, §1.1-1.3, §2.2, §2.5, §3 (definitions table, statements table, de Rham layer table with line counts, §3.4 non-vacuity checks), §4 statability, §6 obstacle and recommendations revised for the de Rham construction and PanBerger.

## Step 7: sanity checks (proved; standard axioms)
- `htMult_cycRep_eq_zero`: given Tate (ℂ_p(j)^G = 0, j ≠ 0) as hypothesis, htMult of ℚ_p(1) (`cycRep`) is 0 at every w ≠ −1. Confirms the convention (cyclotomic weight −1).
- `isDeRham_trivial`: given B_dR^G ⊆ ℚ_p and ℚ_p → B_dR injective as hypotheses, the trivial 1-dim representation satisfies `IsDeRham`. Confirms ddrSpace and the dimension normalization.
- I4.lean ~1060 lines, compiles, no sorry.

## Step 8: G_F versions and the C3 leaf
- DEFINED (compiles): `gfToGqp` (G_F → G_{ℚ_p}), `ddrSpaceOver`, `IsDeRhamOver`, `htSpaceOver`, `htMultOver` for a Mathlib `Representation ℚ_[p] (absoluteGaloisGroup F) V`, F/ℚ_p finite.
- Copied pkg-I3's definitions (origin/wip/pkg-I3 @ 7406c0ae, scratch/pkg-I3/I3.lean lines 26-335, unchanged: Tate module, AbVar, Pt, V, galRep) into I4.lean; they compile under `import Mathlib`.
- New statable leaf `DeRhamComparison` (C3: V_p(A) de Rham over F with HT weights 0, −1 of multiplicity g). `#print axioms`: propext, Classical.choice, Quot.sound.
