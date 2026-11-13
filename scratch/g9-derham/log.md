# g9-derham results log

## 2026-11-13 03:1x PST: route check
- VERIFIED (read): h-decomposition.md §1 "Recommendation: route P for the announced decomposition,
  route K as the fallback" (about line 466); the glue table row G9 (line 1035) is on route P;
  route K (GK1, GK2) replaces G9 only on the fallback route. So G9 is still needed.
- VERIFIED (read): manuscript L10939-11000, Lemma `lem:de-rham-descent` (K/ℚ_ℓ, F/K finite, A/F
  abelian surface, r : G_K → GL₂(C_ℓ), V_ℓ(A) ⊗ C_ℓ ≅ r|G_F ⊕ r|G_F ⇒ r de Rham, HT weights 0, −1).
- VERIFIED (read): h-trust C3 "Galois choice": N5 applies the lemma with K = ℚ₅, and F may be
  taken Galois over ℚ_ℓ.
- VERIFIED (read): R10 = `PkgI4.DeRhamComparison` is stated directly for `V_p(A)` (pkg-I3's
  `galRep`), so T10 (`T10_TateDuality`, an `opaque` placeholder) carries no content and is not
  needed as a hypothesis.

## 03:15 I4Layer.lean
- `ZInQKernel/Contrib/G9/I4Layer.lean`: verbatim copy of Leaves.lean L3230-4735 (PkgI4Sec), in
  namespace `ZInQ.Contrib.G9`. VERIFIED: `lake env lean` exit 0, no errors (1m44s);
  `lake build ZInQKernel.Contrib.G9.I4Layer` OK.

## 03:3x-04:3x compiled layers (all `lake env lean`, exit 0, no errors)
- Speiser.lean: `speiser_finrank` (dim_K M = [L:K]·dim_K M^Γ for semilinear Γ = Gal(L/K) action).
- Descent.lean: `Dsp act ρ S` (S-equivariant maps V → B); `descent_finrank`:
  dim Dsp(ker γ) = [L:K]·dim Dsp(G) given γ : G ↠ Gal(L/K), ι : L →ₐ B semilinear.
- Galois.lean: `range_gfToGqp : (gfToGqp p F).range = (gammaF p F).ker` for F/ℚ_p finite Galois,
  `fieldF p F ⊆ ℚ̄_p` a copy of F (`finrank_fieldF`, IsGalois instance).
- OverF.lean: `overF_count`: C ⊗_K V ≅ U × U equivariant, Dsp(V) ≠ 0 ⇒ [C:K]·dim Dsp(V) = 2·dim Dsp(U).
- Local.lean: `htMult_eq_one_of_R10` (G9 HT part): from `DeRhamComparison` (R10) and G8's local
  output (F/ℚ_p finite Galois, A/F with dim 2, e : C ⊗ V_p(A) ≃ₗ[C] C² × C² G_F-equivariant via
  `gfToGqp`), `htMult p r 0 = 1 ∧ htMult p r (-1) = 1`. T23, T10 not used.
- FINDING (VERIFIED by reading the Lean): R10's Lean form gives only the multiplicities at 0 and −1
  (`htMultOver … 0 = g`, `… (−1) = g`), not the vanishing at other weights; so `HasHTWeights p r
  {0, −1}` (all w) does not follow from R10 as stated. Also htMultOver is a truncated division;
  the F'-structure on htSpaceOver (`finrank_dvd_Dsp`) makes it exact.

## (previous run, committed) Speiser.lean, Descent.lean, Galois.lean
- `speiser_finrank` (Speiser's lemma, dimension form), `descent_finrank` (finite Galois descent for
  spaces `Dsp` of equivariant maps), `range_gfToGqp` (image of `G_F` in `G_{ℚ_p}` = kernel of
  `G_{ℚ_p} → Gal(F'/ℚ_p)`). VERIFIED: modules build (commits f07b7788, ac5c3c70, 685af793).

## 03:40 OverF.lean
- `finrank_Dsp_congr`, `finrank_Dsp_pi`, `finrank_Dsp_prod`, `overF_count`. VERIFIED:
  `lake build ZInQKernel.Contrib.G9.OverF` OK.

## 03:45 integrator update: target is g0-mod-galois's `G9Glue`
- Merged origin/main (c303557d) without conflict.
- VERIFIED (read, `git show origin/wip/g0-mod-galois:scratch/g0-mod-galois/ModGalois.lean`,
  L20241): `G9Glue : Prop := PkgI4.DeRhamComparison → (∀ p [Fact p.Prime], PkgI4.T23_FontaineClosure p) →
  ∀ K [NumberField K] (A : PkgI3.AbVar K) ℓ r e, A.dim = 2 → Intertwines (tate A ℓ) (r ∘ resQ K) e → G9Out r`,
  `G9Out r := LocalIsDeRham ℓ 2 (r.restrictLocal ℓ) ∧ r.HasHTWeightsAtSelf ℓ {0, -1}`.
- Finding F1 (VERIFIED, read of the definitions): `HasHTWeights p ρ S` is `∀ w, htMult p ρ w = S.count w`,
  so `G9Out` requires `htMult = 0` at every `w ∉ {0, −1}`. R10 (`DeRhamComparison`) gives
  `htMultOver` only at `0` and `−1`. No hypothesis of `G9Glue` bounds `htMultOver` at other weights;
  that needs Tate's theorem `ℂ_p(j)^{G_F} = 0` (j ≠ 0) and Sen's independence, which are not in
  Mathlib (bdr-kertheta.md "What remains" (b)). So `G9Glue` is not derivable from R10 + T23 without
  formalizing Tate–Sen; the published R10 (HT decomposition `ℂ_p ⊗ V_p(A) ≅ ℂ_p^g ⊕ ℂ_p(1)^g`)
  contains the vanishing, the Lean R10 drops it.
- Finding F2 (VERIFIED, read): R10 is stated for `PkgI4.I3.AbVar F` over a finite `F/ℚ_ℓ`; `G9Glue`'s
  `A` is a `PkgI3.AbVar K` over a number field. Using R10 needs base change `A ↦ A_F` and the
  comparison `V_ℓ(A_F) ≅ V_ℓ(A)|G_F`, i.e. that every `ℓⁿ`-torsion point of `A` over `F̄` is defined
  over `K̄` (finiteness of `A[ℓⁿ]`, Mumford §4/§6, not in Mathlib, not among the hypotheses).
- Finding F3 (VERIFIED, read): the descent `F → ℚ_ℓ` for `D_dR` needs an equivariant embedding
  `F' → B_dR` (`ℚ̄_p ⊆ B_dR^+`, Hensel in the complete DVR `B_dR^+`); pkg-I4 and bdr-kertheta do not
  construct it (bdr-kertheta "What remains" (a): compatibility with `bdrAct` unchecked). For `ℂ_p`
  (Hodge–Tate part) the embedding `F' ⊆ ℚ̄_p ⊆ ℂ_p` is available.
- Plan: prove the local core (descent + counting) and `G9Glue` from R10, T23 and named bridge Props
  for F1-F3.

## 03:50 I3Layer.lean, Statement.lean
- `I3Layer.lean`: verbatim Leaves.lean L1927-3228 (PkgI3Sec; identical to ModGalois L1920-3221,
  VERIFIED by diff). `I4Layer.lean` is identical to ModGalois L3223-4728 (VERIFIED by diff).
- `Statement.lean`: verbatim ModGalois L20049-20111, L20178-20182, L20229-20246 (`resQ` … `Intertwines`,
  `G9Out`, `G9Glue`) in namespace `ZInQ.Contrib.G9.G0Galois`. VERIFIED:
  `lake build ZInQKernel.Contrib.G9.Statement` OK (linter warnings only, from the verbatim text).

## 04:15 BdRAct.lean
- `PkgI4.bdrAct_mul`, `bdrAct_one` (functoriality of Mathlib's B_dR construction through
  `modPMap`/`preTiltMap`/`locMap`/`adicMap`/`bdrPlusMap`/`bdrMap`), `cpAct_mul_apply`,
  `cpAct_one_apply`, `cycPow_mul`, `cycPow_one`; monoid homs `htAct p i`, `drAct p`.
  VERIFIED: `lake env lean` no errors.

## 04:35 LocalCore.lean
- `core_ht` (VERIFIED, builds): F/ℚ_p finite Galois, ρ : G_F-rep on V over ℚ_p, E ⊆ ℚ̄_p finite,
  ρE : G_{ℚ_p} →* GL₂(E), eE : E ⊗ V ≃ₗ[E] E²×E² intertwining (ρ σ).baseChange with
  matRep(ρE(gf σ)) ⊕ same; htMultOver ρ 0 = 2, htMultOver ρ (-1) = 2, htMultOver ρ w = 0 (w ∉ {0,-1})
  ⇒ `HasHTWeights p ρE {0, -1}`.
- `core_dR` (VERIFIED, builds): same data + `ιB : ℚ̄_p →ₐ[ℚ_p] B_dR` equivariant + `IsDeRhamOver p ρ`
  ⇒ `IsDeRham p ρE`.
- Aux: `overF_count_gen` (no finiteness), `finrank_dvd_Dsp`, `core_count`, `Dsp_gf_eq`,
  identifications `ddrSpace_eq_Dsp`, `htSpace_eq_Dsp`, `ddrSpaceOver_eq_Dsp`, `htSpaceOver_eq_Dsp`.

## 03:50 G9 proved (VERIFIED: lake build ZInQKernel.Contrib.G9.G9 OK; #print axioms = propext,
## Classical.choice, Quot.sound for every theorem below)
- KerTheta.lean: verbatim copy of scratch/bdr-kertheta/KerTheta.lean minus its PkgI4.Cp block
  (diff-identical to I4Layer's), namespace ZInQ.Contrib.G9.
- HenselEmb.lean: `exists_hensel_lift`, `hensel_lift_natural`, `root_eq_of_theta` (abstract).
- BdREmb.lean: `bdrAct_mul`, `bdrAct_one`, `bdrActHom`; `thetaPlusCp_bdrPlusMap` (θ⁺ equivariant);
  `thetaPlusCp_qpToPlus` (θ⁺ is ℚ_p-linear; proof: separatedness, ring homs ℤ_p → 𝓞_ℂ_p agree).
- G9.lean: `iotaDR`, `bdrAct_iotaDR` (F' ⊆ B_dR equivariantly); `isDeRham_of_R10`; `g9_deRham`
  (IsDeRham p r ∧ htMult p r 0 = 1 ∧ htMult p r (-1) = 1); `g9_localIsDeRham` (LocalIsDeRham form).
- Hypotheses of g9_deRham: R10 (`DeRhamComparison`) + G8 local output; T23 and T10 NOT used.
- Scope: K = ℚ_p and F/ℚ_p Galois (h-trust C3 "Galois choice"); N5's lemma allows K/ℚ_ℓ finite and
  F/K arbitrary finite — not covered.

## 05:00 CoefDescent.lean
- `coef_descent` (VERIFIED, `lake env lean` no errors): F/ℚ_p finite Galois, ρ : G_F-rep on V,
  R : G_{ℚ_p} →* GL₂(ℚ̄_p), e' : ℚ̄_p ⊗ V ≃ₗ[ℚ̄_p] ℚ̄_p²×ℚ̄_p² intertwining ρ|G_F with R∘gf ⊕ R∘gf ⇒
  ∃ E ⊆ ℚ̄_p finite, ρE : G_{ℚ_p} →* GL₂(E) with map ρE = R, eE : E ⊗ V ≃ₗ[E] E²×E² intertwining.
  No topology (coset representatives of the finite G_{ℚ_p}/G_F replace Baire).

## 05:15 Reduction.lean
- Bridges (named Props, namespace `ZInQ.Contrib.G9.G9Bridge`): `LocalModel` (F2), `R10Weights` (F1),
  `BdRContainsQbar` (F3).
- `g9Glue_of_bridges : G9Bridge.LocalModel → G9Bridge.R10Weights → G9Bridge.BdRContainsQbar → G9Glue`.
  VERIFIED: `lake build ZInQKernel.Contrib.G9.Reduction` OK; `#print axioms` →
  [propext, Classical.choice, Quot.sound] for g9Glue_of_bridges, core_ht, core_dR, coef_descent.
- T23 is not used by the proof (the counting replaces Fontaine's closure properties).

## 04:2x session g9-derham-3c (parallel run): weights, dedup, handover
- G9Weights.lean (VERIFIED: builds; axioms propext, Classical.choice, Quot.sound):
  `DeRhamComparisonWeights` (R10's weight clause: htMultOver w = 0 for w ∉ {0,−1});
  `htMult_eq_zero_of_R10w`; `g9_hasHTWeights : R10 → R10w → … → IsDeRham p r ∧ HasHTWeights p r {0,−1}`;
  `g9_local : … → LocalIsDeRham p 2 ρ ∧ LocalHasHTWeights p ρ {0,−1}` (E ⊆ ℚ̄_p finite).
- OverF.lean refactor: `DspPiEquiv`, `DspProdEquiv`, `overF_pos_rev` (Dsp(U) ≠ 0 ⇒ Dsp(V) ≠ 0);
  lemma signatures unchanged; CoefDescent chain rebuilds (VERIFIED).
- Local.lean imports I3Layer for `GlueI3.repBaseChange` (duplicate removed); renamed
  `finrank_dvd_Dsp_of_emb`, `htSpace_eq_DspAct`, `htSpaceOver_eq_DspAct`, `ddrSpace_eq_DspAct`,
  `ddrSpaceOver_eq_DspAct` (clashes with LocalCore). VERIFIED: a file importing G9Weights and
  CoefDescent together compiles.
- Coordination: the parallel session g9-derham-c7 owns Reduction.lean (G9Glue), docs/research/g9-derham.md
  and .fleet/g9-derham.md; it will import G9.lean (`iotaDR`, `bdrAct_iotaDR`) to drop its
  BdRContainsQbar bridge. This session writes no further Lean.
