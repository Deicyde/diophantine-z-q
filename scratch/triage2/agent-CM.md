# agent-CM: can CMPairsExistT2 be proved without babaGranathRationalAb?

Read-only, no Lean run. VERIFIED = read at file:line (paths relative to worktree root). SPECULATIVE = judgement.

## (1) Does the tree already build CM QM surfaces?
- There is no unconditional producer over ℚ̄. Every theorem concluding `∃ P, HasCM* P.q` goes through R1R2fp/BG,
  so all are circular (VERIFIED):
  - `cm_objects_of_props` (TailE:688);
  - `cmObjectsExist_of_R1R2fp` (TailL:246-265);
  - Pin.lean:323;
  - `cm_lift` (TailZ20:310), which needs `hE` from BG.
- Over ℂ, the CM step is ALREADY PROVED, conditional only on T11a (VERIFIED):
  - `CMFixedHasCM` (TailJ:1220);
  - `cmFixedHasCM_of (hR : T11aRiemannEnd) : CMFixedHasCM` (TailJ:1270-1375). If `Q : QML3 ℂ` has
    `HasQMPeriod Q τ` (TailJ:1150) and `g = ι(x)` fixes τ, with x ∈ 𝒪 and x² = −1 (resp. x²−x+1 = 0, x² = −6),
    then HasCM4 (resp. HasCM3, HasCM24) Q.q.
- The explicit fixed points are ALREADY PROVED (VERIFIED). Each matches CMFixedHasCM's hypothesis shape exactly:
  - `cm4_exists` (TailJ:255): x4 = i+j, τ = √2+i;
  - `cm3_exists` (TailJ:271): x3 = (1+j)/2, τ = i√3;
  - `cm24_exists` (TailJ:275): x24 = 2j+k, τ = i√(9+6√2), not i(√3+√6).

  All three are in namespace HDec.HSyn.G0Split.FibreQM.PeriodMap.
- `descend_main` (TailO:1177) / `cmDescends_of` (TailO:1302), VERIFIED read:
  - **hST (STQM) and hR (T11b):** used for A₀, κ = β⁻¹∘conjE, q₀ (TailO:1181-1191).
  - **hTD:** used only for the level structure η₀ (TailO:1194-1243).
  - **hRep:** used only at TailO:1245-1246, as `hR1.2.2.2.1`, the R1fp naturality clause. It produces Q' and
    `IsBaseChangeOf`, and nothing else.
  - **What CMPairsExistT2 needs:** QMPair has no level structure, so only P = ⟨A₀, hdim, q₀⟩ and κφ ∈ com q₀ are
    needed. Those come from TailO:1181-1191 plus `com_of` and the equation transport (TailO:1305-1322). Neither
    hTD nor hRep is needed.

## (2) Lattice uniformization and the lift
- **Q with HasQMPeriod Q τ, for every τ:** comes from shimuraMainThmIDeligneY3AbU (RayClassShimura:1152), with
  two possible sources (VERIFIED):
  - DeligneBodyAt's 4th conjunct `IsShimuraHolFamily Y Φ (fun τ => Ψ τ 1)` (RSh:1121), whose first clause
    (RSh:255-260) is exactly HasQMPeriod's body;
  - ModuliAtUnits at u = 1 (RSh:1135; this also needs 1 ∈ OhatU via `OhatQ_one`, RSh:1235). Not needed.
- **Lifting a lattice-preserving linear map:** `T11aRiemannEnd` (TailC:7866). It is obtained as
  `t11aRiemannEnd_of_hom` (TailJ:1852) ∘ `t11aRiemannHom_of_corr4` (TailK:63) ∘ `AvSplit.Final.h69 HL HG`
  (TailQ:2380), where HL = uniformizationLeafAll and HG = gagaMorphism. This is exactly the chain already used
  at TailK:91-93 (VERIFIED).
- **Fields used (VERIFIED):** `t.uniformizationLeafAll` and `t.gagaMorphism` (TailZ34:106);
  `l.shimuraTaniyamaQbar` (TailZ34:121) → `stqm_of` (TailU:1727) = `stQM_lf7` (TailX:61); T11b is
  `t11b_of_exists5 t11bExists_lf8` (TailN:57, TailZ4:60; proved).

## (3) Plan (SPECULATIVE as a whole, pieces VERIFIED). Tier T1 (about 2-4 h, mostly name resolution)
```
theorem cmPairsExistT2_of (hU : RayClassCFT.ShimuraMainThmIDeligneY3AbU)
  (HL : UniformizationLeafAll) (HG : GAGAMorphism) (hS : ShimuraTaniyamaQbar) : CMPairsExistT2
  hCF := cmFixedHasCM_of (t11aRiemannEnd_of_hom (t11aRiemannHom_of_corr4 (AvSplit.Final.h69 HL HG)))
  obtain ⟨Y,Φ,-,Ψ,⟨-,-,-,⟨hmod,-⟩,-⟩,-⟩ := hU      -- hmod τ : ∃ P, Φ.. ∧ ∃ Φu, IsUnif ∧ IotaCompatible
  -- for each of (cm4_exists, x4_sq, .1), (cm3_exists, .2.1), (cm24_exists, .2.2):
  obtain ⟨x,hx,hsq,g,hg,τ,hτ⟩ := cm4_exists; obtain ⟨Q,-,hQ⟩ := hmod τ
  have c4 : HasCM4 Q.q := ((hCF Q τ hQ x g hx hg hτ).1 hsq)
  -- descent lemma (copy of TailO:1181-1191 + 1305-1311, no hTD/hRep):
  pairOf (hST : STQM) (hR : T11b_Rigidity) (A : AbVar ℂ) (q : QMStr A) (hA : A.dim = 2) (hcm : _∨_∨_) :
    ∃ (P : QMPair Qbar) (κ : End A →+* End P.A), ∀ a, κ (q.iota a) = P.q.iota a
  then the equation transport as in TailO:1312-1322.
```
- **Risks (SPECULATIVE):**
  - alias/namespace clashes: Qbar abbrevs, PkgI1 vs HDec.PkgI1, QML3 export aliases (memory: Qbar ambiguity);
  - the anonymous-constructor depth when destructuring DeligneBodyAt.

  None is mathematical.
- **Fold:** `babaGranathRationalAb_of_elkiesT2` (ProbeB, compiled), with ElkiesEquationsX6Ab from
  `elkiesEquationsX6Ab_of_printed` (ElkiesX6Star:118). The bundle converter needs r, t and l. Note that
  `openResearchLeaves20_of_OpenResearchLeaves21` (TailZ34:83) takes only (n, t). So either thread l into it, or
  do the replacement at sixContactMin_of_open28 (TailZ34:171), which has r, t, l and g. That is fold work and
  T1-T2.
