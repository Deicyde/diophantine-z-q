# gap-triage: what to attack next among the open statements of `ZInQ.OneProof.frozenTarget`

Task gap-triage, 2026-11-14/15. Base e38375b3 (w62: 59 bundle fields + 6 top statements). The next integration
origin/wip/w63 (b5ff0474, 61 fields) was read with `git show` wherever it changes a field. Read-only triage: the only
Lean written is two probe files, `scratch/gap-triage/GlueProbe.lean` and `VerifyProbe.lean`, which compile (exit 0)
against a build of e38375b3. The table with one row per statement is `scratch/gap-triage/triage.tsv` (generator
`mk_triage.py`). The results log is `scratch/gap-triage/log.md`, and the six reading agents' notes are
`scratch/gap-triage/agent-*.md`. Model work, with no human review.

Marks:
- **VERIFIED**: read in a named file, or compiled in a probe (`log.md` says which).
- **STANDARD**: published, with an exact reference.
- **SPECULATIVE**: a judgement or an untested route.
- **UNVERIFIED**: a theorem number recalled without a source; this host has no network.

Agent claims are SPECULATIVE unless I re-checked them. Section 3 lists what I re-checked.

## 0. Findings that change the plan

1. **`bdRInvariants` is used only syntactically** (VERIFIED by reading). The field becomes `t23` (TailX L235). `t23`
   reaches only `g8_g11`/`g8_g12` (TailA L2203–2250; TailD L138, L172), where it is passed on only as `h9g hR10 hT23 …`.
   Every proof of `G9Glue` on the chain (TailK L330, TailD L591) goes through `ZInQ.Contrib.G9.g9Glue_of_fieldEmb`
   (`Contrib/G9/Reduction.lean` L128; the copy actually in the closure is `HDec.ZInQ.Contrib.G9.g9Glue_of_fieldEmb`, TailC L14082). Both start `intro hR10 _hT23 …` and never use the T23 argument. A closure probe (`ClosureProbe.lean`, compiled) shows that the only `t23` consumers in the closure of `sixContactMin_of_open12` are `g8_g11`, `g8_g12`, `g8_g12_of_leaves3` and `afterG7_of3`.
   PruneScan cannot see this, because the projection is present in the term. Plumbing removes the field (A1).
2. **On w63, `raynaudKernelBound` is also used only syntactically** (VERIFIED by reading).
   - `transfer_core` (LPrefix L12153) uses R20 only as `(abs_le.mp hvar).1`, i.e. h(P) ≤ h(J) + ½ log deg ψ.
   - In `faltingsLemma5_of_printed` (w63 TailZ19 L432), that half comes from `FaltingsLemma5Printed` and
     `kerOmegaLog_nonneg` alone. `RaynaudKernelBound` gives only the other half.
   - Plumbing removes it (A1).
3. **`CoverModelOfHeckeN` and Lemma NV are not needed under the glue field** (VERIFIED, compiled in GlueProbe).
   - mcr-quot uses `hCov` only through `modelYIrreducible_of_coverModelN hT hCov` (MCRQuot.lean L7624, L7741).
   - The body of `MCRQuot.ModelYIrreducible` is the body of the chain's `HDec.PropTSGlue.HeckeIrreducible`. The probe
     checks `example : HDec.PropTSGlue.HeckeIrreducible = ModelYIrreducibleCopy := rfl`.
   - The chain proves it from the existing field `deligneComponentsY3Printed`:
     `GapTriage.modelYIrreducible_of_open9 (l : HDec.HSyn.OpenAddedLeaves9) : ModelYIrreducibleCopy`, with standard
     axioms.
   - So mcr-quot's composite needs only L1–L6, T5, `CurveBijIso`, `P1SchemeQ` and `CMStabObj`. Compiled:
     `GapTriageMCR.modelCoordinateResidue_final10` (`scratch/gap-triage/MCRQuotNV.lean`, which is MCRQuot.lean
     verbatim plus 20 lines) takes `hYI : ModelYIrreducible` in place of `hCov`, via `final4`, with standard axioms.
4. **`P1SchemeQ` is within reach of the vendored CloudW07 library** (VERIFIED: every declaration below passes
   `#check`). Available pieces:
   - `projectiveLine k` (`Proj k[X₀,X₁]`), `isProper_toSpec`, `smoothOfRelativeDimension_toSpec`, `chartSpecIso`,
     `isAffineOpen_chart`, `polyEquivChart`;
   - on the relative line, `ProjectiveSpace.homOfSections`, `homOfSections_preimage_standardOpen`, `hom_ext`,
     `ProjectiveLine.normalized`, `normalized_eq_of_mul_eq_one`;
   - Mathlib's `Scheme.Cover.glueMorphisms`.
5. **Igusa's ψ₄ and χ₁₀ are applied at two matrices only** (VERIFIED by grep of every `hT` use).
   - `ThetaModularity` is applied as `hT M hM (Omega z) …` only in `g8Auto_of_sp`/`g20Auto_of_sp`.
   - Those are reached only through `g8Auto_g4/g6`, `g20Auto_g4/g6`, i.e. at `M4`, `M6` (TailJ L4116ff).
   - So two Siegel-modular-form leaves reduce to explicit theta transformations at two matrices (A2).
6. **The valence formula and Shimizu's covolume serve one group** (VERIFIED: definitions and the
   `gammaStarFromO1_proof'` route read). Every use has Γ = `PkgI1.GammaStar`. `shimizuCovolumeO1` enters only through
   `GammaStarCocompactArea` (vol = π/6), which can be proved directly for the (2,4,6) group (A6).
7. **t5-glue's tip is not merged** (VERIFIED by `git merge-base`).
   - origin/wip/t5-glue 39bb3cd2 reduces `ShimuraReciprocityModFn` to two printed leaves plus the glue
     `RingClassLattice`.
   - The tip is in neither the base nor w63; the base has only the earlier merge 8882ff19.
   - The brief's "merged" holds only for that earlier state.
8. **Owner decisions that need no agent:**
   - **GZ swap** (VERIFIED by reading `Contrib/GZStatements/Weak.lean`, in the tree):
     `frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd` already takes the
     restricted `FHNonvanishingCd`, `GrossZagierHeegnerCd`.
   - **`dsThm966`** is used only to exclude weight 1. Reading Pan's output as "regular algebraic, k ≥ 2" would drop
     it, but that is a change to `r11r12`'s reading and needs a reviewer (agent EF, SPECULATIVE).
   - **`R1pi0Props`** is discarded by `R1R2fp_of_rep` (VERIFIED, LPrefix L5228), and **`R1recProps`** probably has no
     reader (agent A, SPECULATIVE). If confirmed, x6-glue's split of `r1r2` loses `RayClassCM`. This is a note for
     x6-fold.

## 1. Ranked attack list (free statements; at most 12 one-agent tasks)

Expected value per unit of work. "−n" is the number of bundle hypotheses a success removes. Base every task on
**origin/wip/w63** (the next integration); line numbers below are at e38375b3 unless marked w63. Every result must
be a scratch theorem with exact hypotheses: folds stay with the integration lead.

| rank | task | removes | tier | success odds (SPECULATIVE) |
|---|---|---|---|---|
| A1 | semantic prune: `bdRInvariants` and (w63) `raynaudKernelBound` | −2 | T1 | high |
| A2 | `ThetaModularityM46`: Igusa ψ₄, χ₁₀ at M4, M6 | −2 | T1–T2 | medium-high |
| A3 | `P1SchemeQ` from CloudW07, plus the NV-free mcr-quot composite | glue: 2 of mcr-quot's 3 glue Props | T1 | high |
| A4 | (w63) `egaIV_8_10_5_openImm` proved | −1 | T1 | high |
| A5 | `qmCentralizerCMC` by the complex lattice | −1 | T2 | medium |
| A6 | `GammaStarCocompactArea` directly (drops `shimizuCovolumeO1`) | −1 | T2 | medium |
| A7 | `RingClassLattice` (t5-glue tip): `hS` becomes 2 printed leaves | GLUE → 2 LEAF | T2 | medium |
| A8 | (w63) `neronSchemeModelExistsDVR` from N1 + `blr_1_2_4` | −1 (reading call on r6) | T1–T2 | medium |
| A9 | `yuThm11` specialized to `YuB6Alg`, by the lattice | −1 | T2 | medium-low |
| A10 | (w63) `blr_1_2_4`, the direction used | −1 | T2 | medium |
| A11 | `milneIsogenyQuasiInverse` in characteristic 0 | −1 | T2 | medium-low |
| A12 | `CMStabObj` (glue under `quotientP1Coordinate`) | glue: 1 | T2 | medium-low |

Why this order:
- A1 and A4 are near-certain field removals.
- A2 removes two published leaves with Mathlib's theta functional equation and cm24-value's genus-2 inversion.
- A3 has high probability. It does not remove a field by itself: mcr-quot's fold still adds L1–L6 (leaf-fold9 §5).
  But it clears all project glue but `CMStabObj` below the one GLUE field.
- A5–A11 are bounded library pieces, each worth one field. A12 pays only together with L1, L3, L5, L6.

Conflicts and owners:
- leaf-fold11 §5 lists `QuotientP1Coordinate` as "running or queued (another project task)": **check with the lead before A3 and
  A12.**
- A8 touches the consumers of fields under review (r6).
- A9 should follow A5, since it shares A5's lattice set-up.

---

### A1. Semantic prune: `bdRInvariants` and `raynaudKernelBound`

- **Target:** a top theorem with `frozenTarget`'s H signature, whose proof never projects `t.bdRInvariants` nor
  `r.raynaudKernelBound`. PruneScan then reports both UNUSED, and the lead prunes them as for r3/t10.
- **Statements made redundant (verbatim):**
  ```lean
  -- textbook field (TailZ11 L28): bdRInvariants : ∀ (p : ℕ) [Fact p.Prime], _root_.ZInQ.Contrib.HodgeSplit.BdRInvariants p
  def BdRInvariants : Prop :=
    ∀ x : BdR p, (∀ σ : GQp p, bdrAct p σ x = x) → x ∈ Set.range (qpToBdR p)
  -- w63 TailZ19 L399
  def RaynaudKernelBound : Prop :=
    ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
      ∀ (𝒩A : GroupModel A K) (𝒩B : GroupModel B K), 𝒩A.IsNeronModel → 𝒩B.IsNeronModel →
        IsSemistable 𝒩A → IsSemistable 𝒩B →
        ∀ (φ𝒩 : 𝒩A.G ⟶ 𝒩B.G) (hφ𝒩 : IsMonHom φ𝒩), ExtendsIsogeny φ 𝒩A 𝒩B φ𝒩 →
          kerOmegaLog φ𝒩 hφ𝒩 ≤ Module.finrank ℚ K * Real.log (isogDeg φ)
  ```
- **Inputs:** the w63 bundles minus these two fields; the kernel and chain theorems.
- **Plan:**
  1. Part (a): define `G9GlueNoT23 := PkgI4.DeRhamComparison → ∀ K … , G9Out r`, i.e. `G9Glue` without its second
     argument. Prove it as `g9Glue_of_fieldEmb` does (copy, dropping `_hT23`).
  2. Copy `g8_g11`, `g8_g12` (TailA L2203–2250) and their live callers `afterG7_of3`, `g8_g12_of_leaves3` (TailD L138,
     L172) with `G9GlueNoT23` and without `hT23`.
  3. Part (b): define `R20Upper` (the half `−½ log deg ≤ h(J) − h(P)`). Prove the upper-half variants of
     `faltingsLemma5_of_printed` / `faltingsLemma5BC_of_printed` without `RaynaudKernelBound`, then `transfer_core'`.
  4. Re-derive the one-line stack `glueOutputs_of_leaves3` … `sixContactMin_of_open15` over the copies.
  5. Check with PruneScan (`origin/wip/prune-scan:scratch/one-proof/PruneScan.lean`) and `#print axioms`.
- **Risks:**
  - The number of intermediate bundle generations (genus-fold's `prune_edit.py` is the precedent).
  - Other callers of `g8_g11` off the live chain (TailA L2522, L2739, L4700) are left as they are.
- **Scratch theorem for the fold:**
  ```lean
  theorem GapPrune.sixContactMin_of_open15' (r : HDec.HSyn.OpenResearchLeaves12) (t : HDec.HSyn.OpenTextbookLeaves10)
      (l : HDec.HSyn.OpenAddedLeaves11) (g : HDec.HSyn.OpenGlue7) : ZInQ.SixContactMin
  -- with PruneScan: bdRInvariants UNUSED, raynaudKernelBound UNUSED
  ```

### A2. `ThetaModularityM46`: Igusa ψ₄, χ₁₀ at the two matrices used

- **Target:** both fields, in the specialized form every consumer needs (VERIFIED: only `M4`, `M6`, `Omega z`).
- **Statements (verbatim, TailU L1797, L1807):**
  ```lean
  def IgusaPsi4 : Prop :=
    ∀ M ∈ Matrix.symplecticGroup (Fin 2) ℤ, ∀ Ω ∈ SiegelH2,
      psi4 (spAct M Ω) = spFactor M Ω ^ 4 * psi4 Ω
  def IgusaChi10 : Prop :=
    ∀ M ∈ Matrix.symplecticGroup (Fin 2) ℤ, ∀ Ω ∈ SiegelH2,
      chi10 (spAct M Ω) = spFactor M Ω ^ 10 * chi10 Ω
  ```
  Specialized target (implied by the two leaves, since `M4_symp`, `M6_symp`, `omegaSiegel_proof` are proved):
  ```lean
  def ThetaModularityM46 : Prop :=
    ∀ M ∈ ({M4, M6} : Set (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)), ∀ z : ℂ, 0 < z.im →
      psi4 (spAct M (PkgI1.Omega z)) = spFactor M (PkgI1.Omega z) ^ 4 * psi4 (PkgI1.Omega z) ∧
      chi10 (spAct M (PkgI1.Omega z)) = spFactor M (PkgI1.Omega z) ^ 10 * chi10 (PkgI1.Omega z)
  ```
- **Inputs:** none from the bundles. Mathlib `jacobiTheta₂_functional_equation` (VERIFIED `#check`); cm24-value's
  `pi0` (genus-2 partial inversion, origin/wip/cm24-value `scratch/cm24-value/T1.lean` L87, now in w63 TailZ18);
  theta-glue's summability on 𝔥₂ (branch).
- **Plan:**
  1. Transformation of `thetaConst` under translations `Ω ↦ Ω + B`, rotations `Ω ↦ UΩUᵀ` and the partial inversion.
  2. Write `M4`, `M6` as explicit words in these generators, with `spAct`/`spFactor` cocycle bookkeeping by 2×2 matrix
     algebra.
  3. Phases: 8th powers of 8th roots of unity for Σθ⁸; a finite product of 4th roots for ∏θ² (by `decide`).
  4. Then `g8Auto_of_sp'`/`g20Auto_of_sp'` with the specialized hypothesis, and a `ThetaModularity`-free
     `s8WeightExact_of'`, `s20WeightExact_of'`.
- **Risks:**
  - branch cuts in `spFactor` powers (use `cpow_nat_mul`);
  - the word for M6 may need a conjugated partial inversion.
- **Scratch theorems for the fold:**
  ```lean
  theorem GapTheta.thetaModularityM46 : GapTheta.ThetaModularityM46
  theorem GapTheta.s8WeightExact_of' (hT : GapTheta.ThetaModularityM46) (hG : GammaStarGen) : S8WeightExact
  theorem GapTheta.s20WeightExact_of' (hT : GapTheta.ThetaModularityM46) (hG : GammaStarGen) : S20WeightExact
  ```
  The fold then reroutes TailK L99/L319, TailO L2779 and TailZ4 L237 (agent A2 lists the sites).

### A3. `P1SchemeQ` from CloudW07, and the NV-free mcr-quot composite

- **Target (verbatim, `scratch/mcr-quot/MCRQuot.lean` L8549):**
  ```lean
  def P1SchemeQ : Prop :=
    ∃ (P : Over (Spec (CommRingCat.of ℚ))) (τ : ToP1 P.left),
      IsProper P.hom ∧ SmoothOfRelativeDimension 1 P.hom ∧ IsP1CoordinateQ P τ ∧
      ∀ (Z : Over (Spec (CommRingCat.of ℚ))) (σ : ToP1 Z.left),
        ∃ (m : Z ⟶ P) (eU : m.left ⁻¹ᵁ τ.U = σ.U) (eV : m.left ⁻¹ᵁ τ.V = σ.V),
          m.left.app τ.U τ.f = Z.left.presheaf.map (eqToHom eU).op σ.f ∧
          m.left.app τ.V τ.g = Z.left.presheaf.map (eqToHom eV).op σ.g
  ```
- **Inputs:** the field `deligneComponentsY3Printed` (or `y3Connected`), for `ModelYIrreducible`.
- **Plan:**
  1. Take `P := projectiveLineOver ℚ` (proper, smooth of relative dimension 1: VERIFIED `#check`). Build `τ` from
     `chart ℚ 0`, `chart ℚ 1` with `polyEquivChart`, and prove `IsP1CoordinateQ` (affine, `ℚ[X] ≃ Γ`).
  2. For `σ : ToP1 Z`, glue `m` from the chart maps `σ.U → chart 0` (`t ↦ σ.f`) and `σ.V → chart 1` (`s ↦ σ.g`).
     They agree on `U ⊓ V` because `f·g = 1`. Use `Scheme.Cover.glueMorphisms`, or `normalized` +
     `normalized_eq_of_mul_eq_one` on the relative line `ℙ(ULift (Fin 2); Spec ℚ)` with an iso to `projectiveLine`.
  3. Preimages: the chart preimage of `D₊(X₀)` is `U_σ` because `basicOpen_f = U ⊓ V` (cf.
     `homOfSections_preimage_standardOpen`).
  4. Compose with mcr-quot. Copy MCRQuot.lean (parts 1–24) into the scratch and add `final10` below.
- **Risks:**
  - the `eqToHom` transport in the last clause;
  - universe and `Over` plumbing;
  - MCRQuot.lean is ~8.7k lines with its own copies (`MCRGlue`/`PropTSGlue` namespaces), so its composite must be
    restated against the chain's constants. The probe shows `ModelYIrreducible`'s body is the chain's.
- **Scratch theorems for the fold:**
  ```lean
  theorem GapGlue.p1SchemeQ : MCRQuot.P1SchemeQ
  -- compiled already (MCRQuotNV.lean, as GapTriageMCR.modelCoordinateResidue_final10, with hP : P1SchemeQ as an input):
  theorem GapGlue.modelCoordinateResidue_final10 (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
      (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint) (hCyc : TameInertiaCyclic)
      (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso) (hYI : ModelYIrreducible) (hO : CMStabObj) :
      ModelCoordinateResidue
  -- := MCRQuot.modelCoordinateResidue_final4 hAF hQE hTS hP1 hFix hCyc hT hC hYI MCRQuot.quotientDescendsQ
  --      (MCRQuot.toP1BijIsCoordinateQ_of hC GapGlue.p1SchemeQ) (MCRQuot.cMStabInvolution_of hC hYI hO)
  theorem GapGlue.modelYIrreducible_of_open9 (l : HDec.HSyn.OpenAddedLeaves9) : ModelYIrreducible  -- compiled (GlueProbe)
  ```

### A4. (w63) `egaIV_8_10_5_openImm` proved

- **Target (verbatim, w63 TailZ19 L281):**
  ```lean
  def EGAIV_8_10_5_openImm : Prop :=
    ∀ (J : Type) [Preorder J] [IsDirectedOrder J] [Nonempty J] (D : Jᵒᵖ ⥤ Scheme.{0})
      [∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
      [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D), IsLimit c →
      ∀ (i : Jᵒᵖ) (Xi Yi : Over (D.obj i)), LocallyOfFinitePresentation Xi.hom → QuasiCompact Xi.hom →
        QuasiSeparated Xi.hom → LocallyOfFinitePresentation Yi.hom → QuasiCompact Yi.hom →
        QuasiSeparated Yi.hom → ∀ fi : Xi ⟶ Yi,
        IsOpenImmersion ((Over.pullback (c.π.app i)).map fi).left →
        ∃ (j : Jᵒᵖ) (a : j ⟶ i), IsOpenImmersion ((Over.pullback (D.map a)).map fi).left
  ```
- **Inputs:** none.
- **Library** (VERIFIED `#check`):
  - Mathlib `AlgebraicGeometry.exists_preimage_eq` (AffineTransitionLimit.lean L338, Stacks 01Z4);
  - CloudW01 `AlgebraicGeometry.exists_isIso_baseChange_of_isIso_limitBaseChange` (StacksFrontier/…/Isomorphism.lean
    L180, Stacks 081E-type) and `baseChangeConeIsLimit`.
- **Plan:**
  1. The image `U` of the open immersion at the limit is a quasi-compact open. It descends to some `U_j` by
     `exists_preimage_eq`.
  2. `X_j → U_j` becomes an isomorphism at the limit, so it is an isomorphism at some `j' ≥ j` by 081E.
  3. Compose to get an open immersion.
- **Risks:** checking the image's quasi-compactness; finite-presentation side conditions of 081E.
- **Scratch theorem:** `theorem GapEGA.egaIV_8_10_5_openImm : CToPrinted.EGAIV_8_10_5_openImm`.

### A5. `qmCentralizerCMC` by the complex lattice

- **Target (verbatim, TailU L1484):**
  ```lean
  def QMCentralizerCMC : Prop :=
    ∀ (A : PkgI3.AbVar ℂ), A.dim = 2 → ∀ q : LeafQM.AV.QMStr A,
      Nonempty (LeafQM.AV.com q ≃+* ℤ) ∨
      ∃ (k : Type) (_ : Field k) (_ : NumberField k), IsTotallyComplex k ∧ Module.finrank ℚ k = 2 ∧
        ∃ Φ : k →ₐ[ℚ] B, Nonempty (LeafQM.AV.com q ≃+* LeafQM.O.comap Φ.toRingHom)
  ```
- **Inputs:** the textbook fields `uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed` (through
  `AvSplit.Final.h38`, `h69`, VERIFIED `#check`); the chain's `qmComplexUnif_of_textbook`, `qmSkolemNoetherC_proof`,
  `qmClassNumberOne_proof` (VERIFIED `#check`).
- **Plan:**
  1. A `QMStr` version of the uniformization: `A ≅ ℂ²/ι(𝒪)(τ,1)ᵀ`, `ι`-compatibly.
  2. The commutant of `{qmMat a}` in `M₂(ℂ)` is `ℂ` (explicit matrices).
  3. Via `T11aRiemannEnd`, `com q ≅ {x ∈ 𝒪 : ι(x)v_τ ∈ ℂ v_τ}`.
  4. `C(τ)` is ℚ or an imaginary quadratic field: the centralizer of a noncentral element of a quaternion division
     algebra is a quadratic field, and the eigenvalue is non-real.
  5. Conclude `com q ≅ O.comap Φ`.
- **Risks:** the `QMStr` versus `QML3` interface (level structure not needed); the explicit construction of
  `Φ : k →ₐ[ℚ] B`.
- **Scratch theorem:**
  ```lean
  theorem GapQM.qmCentralizerCMC_of (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
      (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) : HDec.QMSplit.Aut.QMCentralizerCMC
  ```

### A6. `GammaStarCocompactArea` directly (drops `shimizuCovolumeO1`)

- **Target (verbatim, TailZ2 L93):**
  ```lean
  def GammaStarCocompactArea : Prop :=
    IsCocompactFuchsian PkgI1.GammaStar ∧
      ∃ s, IsFundDomain PkgI1.GammaStar s ∧ MeasureTheory.volume s = ENNReal.ofReal (Real.pi / 6)
  ```
  It replaces the field (verbatim, TailZ2 L1018):
  ```lean
  def ShimizuCovolumeO1 : Prop :=
    IsCocompactFuchsian Gamma1 ∧
      ∃ s, IsFundDomain Gamma1 s ∧ MeasureTheory.volume s = ENNReal.ofReal (2 * Real.pi / 3)
  ```
- **Inputs:** none from the bundles. Chain: `gammaStarGen_proof`, `gs_fuchsian`, `fix_null`, orbit descents (TailO,
  TailZ3). Mathlib: invariant measure on ℍ (`SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ volume`, VERIFIED),
  `IsFundamentalDomain.measure_eq` (VERIFIED), properly discontinuous action of discrete subgroups of SL(2,ℝ).
- **Plan:**
  1. Discreteness from integrality of `ι(𝒪)`.
  2. An explicit Dirichlet (2,4,6) polygon, covering by leafq-check's descent certificates.
  3. A.e. disjointness by a finite enumeration of integral elements.
  4. Area π/6 by Fubini with `∫ dy/y²` (arcsine antiderivative after a Möbius move).
- **Risks:** the measure-theoretic bookkeeping of `IsFundDomain`; the polygon's boundary pairing.
- **Scratch theorem:** `theorem GapGamma.gammaStarCocompactArea : HDec.LeafQCheck.HM.QMSplit.GammaStarCocompactArea`.
  The fold replaces `gammaStarFromO1_proof' l.shimizuCovolumeO1` at TailZ4 L237, L249 (and inside
  `qmHauptmodulBase3_of_shimizu`).

### A7. `RingClassLattice`: the top hypothesis `hS` becomes two printed leaves

- **Target (verbatim, origin/wip/t5-glue 39bb3cd2 `scratch/t5-glue/T5Glue.lean` L2303):**
  ```lean
  def RingClassLattice : Prop :=
    ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
    ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus)
      (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)),
      ringClassIdeleQuotient (conductorOrder (QNeg m) f) (icl s) =
        (conductorOrder (QNeg m) f).picClass J →
      ∃ k : QNeg m, k ≠ 0 ∧ idealOf m f s = (fun x => k * x) '' idealMeetOrder m f J
  ```
- **Inputs:** Tau Ceti (in tree): `ringClassIdeleQuotient`, `rayClassQuotient_mk_of_mem`, `mem_ker_rayClassToPic`,
  `exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup`. These names are taken from t5-glue's docstring, not
  re-checked here.
- **Plan:** t5-glue §2.4:
  1. Move `s` by a principal idele into the congruence subgroup of the conductor.
  2. Identify the ray class of `s_f`'s ideal.
  3. Write `I = J·(βγ)`.
  4. Compare local lattices at `p ∤ f` and `p ∣ f`.
- **Risks:**
  - 500–1000 lines (t5-glue's estimate);
  - the tip must be merged first (lead);
  - `RingClassLattice` was reviewed TRUE (t5-glue review 2).
- **Scratch theorem:** `theorem GapT5.ringClassLattice : T5Glue.RingClassLattice`. With
  `T5Glue.shimuraReciprocityModFn_of_t5''`, `hS` becomes `ShimuraMainCM` + `X0ModuliGalois`.

### A8. (w63) `neronSchemeModelExistsDVR` from N1 and `blr_1_2_4`

- **Target (verbatim, TailZ7 L238):**
  ```lean
  def NeronSchemeModelExistsDVR : Prop :=
    ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O] (A : PkgI3.AbVar K),
      ∃ (N : Over (Spec (CommRingCat.of O))) (_ : Smooth N.hom) (_ : IsSeparated N.hom)
        (_ : QuasiCompact N.hom) (e : (Over.pullback (jO O)).obj N ≅ A.X),
        ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
          Function.Bijective fun f : Y ⟶ N => (Over.pullback (jO O)).map f ≫ e.hom
  ```
- **Inputs:** `neronSchemeExtensionExists` (N1); w63 `blr_1_2_4`.
- **Plan:**
  1. Prove the number-field form (`K` a number field, `O` a DVR of `K`) as w63's `neronLocalizesDVR_of_printed`
     does: localize N1's model with `blr_1_2_4.mp`.
  2. Then restate the consumers (r6 via `raynaudCriterion_leaves`, SS1, SS3) over number fields.
- **Risks:**
  - The field as stated is over every DVR, so the proof covers only the restriction.
  - r6's consumers involve `raynaudSemistable`, which is under review (reduct-b): coordinate with reduct-b. It is a
    reading call for the integrator.
- **Scratch theorem:**
  ```lean
  theorem GapNeron.neronSchemeModelExistsNF (hN1 : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists)
      (hB : CToPrinted.BLR_1_2_4) : GapNeron.NeronSchemeModelExistsDVRNF
  ```
  plus the restated consumers `raynaudCriterion_leavesNF`, `semistableReductionThm_finalNF`, `semistablePersists_finalNF`.

### A9. `yuThm11` specialized (`YuB6Alg`) by the lattice route

- **Target (verbatim, TailU L443):**
  ```lean
  def YuThm11 : Prop :=
    ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : AbVar k), A.dim = 2 →
      ∀ a b : ℚ, QuatIndefinite a b → (∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x) →
        Nonempty (ℍ[ℚ, a, b] →ₐ[ℚ] End0 A) →
          Nonempty (End0 A ≃ₐ[ℚ] ℍ[ℚ, a, b]) ∨
            ∃ d : ℚ, d < 0 ∧
              Nonempty (End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) ∧
              Nonempty ((AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) ⊗[ℚ] ℍ[ℚ, a, b] ≃ₐ[AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)]
                Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)))
  ```
  Used only via `qmDichotomyYu_of_yu`, which drops the splitting clause, at `(a, b) = (2, −3)` and `k` algebraic over
  ℚ (agent A, SPECULATIVE: consumers not re-read). Weaker target: `YuB6Alg` (agent-A.md §9).
- **Inputs:** as A5, plus `T11b_Rigidity` (from the textbook bundle's `t11bExists`).
- **Plan:**
  1. A5's lattice set-up.
  2. `End⁰(A_ℂ) = ι(B)·com⁰` by the double centralizer.
  3. `com⁰ ∈ {ℚ, imaginary quadratic}`, hence `End⁰ ≅ B` or `M₂(k)`.
  4. Transport `k ↪ ℂ` by T11b.
- **Risks:** the double centralizer is not in Mathlib (an Azumaya API exists); the consumer refactor from `YuThm11`
  to `QMDichotomyYu` for B6.
- **Scratch theorem:** `theorem GapQM.qmDichotomyYuB6_of (hU …) (hG …) (hM …) (hR : ZInQ.LeafPush2.T11b_Rigidity) :
  GapQM.QMDichotomyYuB6`, with the consumers restated at B6.

### A10. (w63) `blr_1_2_4`, the direction used

- **Target (verbatim, w63 TailZ19 L63; only `.mp` is used, with `R = 𝓞_L`):**
  ```lean
  def BLR_1_2_4 : Prop :=
    ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
      (X : Over (Spec (CommRingCat.of R))) [Smooth X.hom] [IsSeparated X.hom] [QuasiCompact X.hom],
      IsNeronModelOver R K X ↔
        ∀ (𝔭 : Ideal R) [𝔭.IsMaximal] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
          [IsLocalization.AtPrime R𝔭 𝔭] [Algebra R𝔭 K] [IsScalarTower R R𝔭 K],
          IsNeronModelOver R𝔭 K ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))).obj X)
  ```
- **Inputs:** none from the bundles.
- **Plan:** "Néron over `R` ⇒ Néron at each localization":
  1. Given smooth `Y/R_𝔭` and `Y_K → X_K`, spread `Y` and the map out to `R[1/s]` (CloudW01: Stacks 01ZM, 0C0C,
     agent CD).
  2. Extend over `R[1/s]` by the Néron property of `X` over `R`. This needs smooth `R`-models of the spread-out
     piece, so check the precise statement of `IsNeronModelOver`.
  3. Glue by uniqueness.
- **Risks:** the extension over `R` needs a smooth model of `Y` over all of `R`, not just `R[1/s]`. The standard proof
  uses Néron's local-to-global property, so this may need the "if" direction's machinery (SPECULATIVE).
- **Scratch theorem:** `theorem GapBLR.blr_1_2_4_mp : GapBLR.BLR_1_2_4_MP` (the `.mp` half). A fold also needs
  `neronLocalizesDVR_of_printed` restated on the `.mp` half.

### A11. `milneIsogenyQuasiInverse` in characteristic 0

- **Target (verbatim, TailQ L1207):**
  ```lean
  def MilneIsogenyQuasiInverse : Prop :=
    ∀ (K : Type) [Field K] (A B : AbVar K) (f : Hom A B), IsIsogenyMor f.hom →
      ∃ d : ℕ, 0 < d ∧ ∃ g : Hom B A,
        f.hom ≫ g.hom = (((d : ℤ) : End A)).hom ∧ g.hom ≫ f.hom = (((d : ℤ) : End B)).hom
  ```
  Every use is in characteristic 0 (agent B, SPECULATIVE), so the target is the `[CharZero K]` restriction, with
  consumers restated.
- **Inputs:** `mumfordTorsionAlgClosed` (kernel finite of order d), T5.
- **Plan:**
  1. `ker f` is finite étale in characteristic 0, so `ker f ⊆ A[d]` with `d = #ker f(K̄)`.
  2. `[d]` factors through the quotient `A → B`: generalize coarse-factor's `factorThroughSurj`
     (`scratch/coarse-factor/Factor.lean`; the graph image, finite bijective onto a normal target, ZMT).
- **Risks:**
  - quotients of abelian varieties are not in the tree;
  - the factorization lemma is proved only for curves over ℚ;
  - possibly T3.
- **Scratch theorem:** `theorem GapAV.milneIsogenyQuasiInverseChar0 : GapAV.MilneIsogenyQuasiInverseChar0`, plus the
  restated `h54`.

### A12. `CMStabObj` (glue under `quotientP1Coordinate`)

- **Target (verbatim, MCRQuot.lean L7648):**
  ```lean
  def CMStabObj : Prop :=
    ∀ P : QML3 Qbar, (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
      ∃ (α : LeafQM.O ≃+* LeafQM.O) (u : (LeafQM.O)ˣ),
        M3.twist α (M3.rightMul u (M3.mk P)) = M3.mk P ∧
        (∀ m : M3 Qbar, M3.twist α (M3.rightMul u (M3.twist α (M3.rightMul u m))) = m) ∧
        ∃ m : M3 Qbar, M3.twist α (M3.rightMul u m) ≠ m
  ```
- **Inputs:** `qmCentralizerCMC` (or A5's theorem), T5 (`Level3.torsor`), `exists_unit_congr` (mcr-quot),
  `ALFixedPoints` (from `rows_of_C`).
- **Plan:**
  1. ℤ[i]: `α = id` and `u` a lift of the action of `i` on `A[3]`. Then `u² ≡ −1`, which acts trivially on classes.
  2. ℤ[ζ₃] and ℤ[√−6]: Atkin–Lehner-type twists from the normalizer of `ι(𝒪)` in `End A`.
  3. `T ≠ id` from an object with automorphism group `±1`.
- **Risks:**
  - a non-CM `ℚ̄`-object must exist;
  - integrality of the normalizer element (mcr-quot §3, SPECULATIVE);
  - the field pays only after L1, L3, L5, L6.
- **Scratch theorem:** `theorem GapGlue.cmStabObj_of (hC : HDec.QMSplit.Aut.QMCentralizerCMC) (hT : ObjBridge.TorsionStructure) :
  MCRQuot.CMStabObj`.

**Next after the twelve:**
- `ValenceFormulaGammaStarEq` (the Jensen route; it replaces `valenceFormulaCocompactEq` and, with A6, the covolume);
- `sga3_VIB_3_10` over a DVR (T1) or over `𝓞_L` (T2);
- `mulEtaleAbelianScheme` elimination (T2; it conflicts with the `mumfordTorsionAlgClosed` reduction);
- `shimuraTaniyamaQbar` by fixed points (T3; it needs the converse of `ALFixedPoints`);
- `gonzalezRotgerCountX6` specialized (T3; class number formula for orders).

## 2. Triage of every statement

One row per statement, with all seven items, is in `scratch/gap-triage/triage.tsv`: 65 base rows (59 fields and 6
tops) plus 7 w63 rows.
- Constants and defining files are from `defs.tsv` (grep at e38375b3).
- Consumers are agent-traced; the rows marked V were re-checked.

Summary (tier = the cheapest route found; owner as of 2026-11-14 evening):

| statement | row | form | use | tier | strategy | status |
|---|---|---|---|---|---|---|
| r1r2 | H-1 | comp | b (Y3, X6) | T4 | keep cited (x6-glue split) | in flight (route A → w63 r1r2Ab; x6-glue/x6-fold) |
| shimuraFamily | H-139 | c | b (own π) | T4 | keep cited | in flight (c-to-printed brief; shimura-cft) |
| igusaPsi4 | H-131 | pub | b (M4, M6) | T1–T2 | specialize, compute | **free: A2** |
| igusaChi10 | H-132 | pub | b (M4, M6) | T1–T2 | specialize, compute | **free: A2** |
| r7a | H-5 | pub | b (QM, 3^k) | T4 | cite | blocked |
| r9a, r9b | H-6, H-7 | pub | b | T4 | cite | free |
| hodgeTateDecompAbVar, deRhamH1AbVarT | H-122, H-123 | pub | b (p = 5) | T4 | cite | free |
| r11r12 | H-9 | comp | b (p = 5) | T4 | cite | free |
| eigenformHTNew | H-127 | c | b (ℓ = 5) | T4 | fold c-to-printed2 | in flight (c-to-printed2) |
| dsThm965 | H-125 | pub | b (ℓ = 3, 5) | T4 | cite | free |
| dsThm966 | H-126 | pub | b (ℓ = 5, k = 1) | T4 (T1 after a reading) | remove (decision) | free |
| r16 | H-13 | comp | b (ℓ = 5) | T4 | cite | free |
| r17 | H-21 | c | b | T4 | fold c-to-printed2 | in flight (c-to-printed2) |
| semistableNeronBaseChange, faltingsLemma5BC, neronLocalizesDVR | H-107, H-111, — | c | b | — | — | done in w63 (c-to-printed) |
| bostLowerBound, javanpeykarBound, pazukiCor13Upper, gaudronRemondThm14 | H-112, H-109, H-113, H-110 | pub | b | T4 | cite | free |
| semistableReductionDVR, semistableUnipotent, raynaudSemistable, semistablePersistsDVR | H-146, H-147, H-160, H-162 | pub (pending) | b | T3–T4 | not ranked | under review (reduct-b; sh-route) |
| neronSchemeModelExistsDVR | H-148 | pub (pending) | b (NF DVRs) | T1–T2 | reduce to N1 + BLR | **free: A8** |
| gonzalezRotgerCountX6 | H-145 | pub/cand. | b | T3 | cite | free |
| mulEtaleAbelianScheme | H-101 | pub | b | T2 (eliminate) | eliminate | free (next) |
| mumfordTorsionAlgClosed | H-102 | pub | b (char 0) | T2 restricted | reduce | free |
| homFree…, charPoly…, poincareComplement | H-70, H-71, H-72 | pub | b | T3 | — | in flight (cloud) |
| cartierSmooth, geomConnOfRationalPoint, groupSchemeEquidim | H-98, H-99, H-100 | pub | b | T2 | — | in flight (cloud) |
| uniformizationLeafAll | H-103 | pub | b weakly | T4 | cite | free |
| gagaMorphism | H-105 | pub | b (dim 2 QM) | T3–T4 | cite | free |
| bdRInvariants | H-124 | pub | **unused in substance** | T1 | plumbing | **free: A1** |
| yuThm11 | H-128 | pub | b ((2,−3), k/ℚ algebraic) | T2 | specialize, prove | **free: A9** |
| genusX1Field | H-79 | comp | b | — | — | done in w63 (genus-fold) |
| regularSmoothPerfect, igusaGL2 | H-118, H-117 | pub | b | T2 | — | in flight (cloud) |
| neronSchemeExtensionExists | H-77 | pub (weak) | a | T4 | cite | blocked |
| thetaRatiosAlgebraic | H-44 | comp | b | T2 | — | in flight (theta-split, theta-glue) |
| qmCentralizerCMC | H-129 | pub | a (for O) | T2 | prove | **free: A5** |
| tateTwistInvariants, axSenTate | H-120, H-121 | pub | b (p = 5) | T2–T3 | — | in flight (cloud) |
| t09SymmIsogenyExists | H-53 | c | b (ℓ = 5, g = 2) | T3 | cite / Pic route | queued (c-to-printed2 left it; t09-pic empty) |
| milneIsogenyQuasiInverse | H-104 | pub (weak) | b (char 0) | T2 | prove | **free: A11** |
| x6ConicModel | H-43 | c | b | T4 | cite (x6-glue) | in flight (x6-glue/x6-fold) |
| shimuraTaniyamaQbar | H-130 | pub | b (6 CM classes) | T3 | specialize | free (next) |
| egaIV_8_10_5_xii | H-65 | pub | b | T2 | — | in flight (cloud) |
| shimuraGoodReductionNoGuard | H-119 | comp | b (Y3, p > 324) | T4 | cite | in flight (cloud) |
| valenceFormulaCocompactEq | H-135 | pub | b (Γ*) | T2–T3 | specialize | free (next) |
| shimizuCovolumeO1 | H-136 | pub | b (Γ*'s area) | T2 | prove `GammaStarCocompactArea` | **free: A6** |
| igusaCMValue24 | H-144 | pub | b | — | — | done (cm24-value, w63) |
| deligneComponentsY3Printed | — | pub/cand. | b (Y3 connected) | T4 | cite | free |
| quotientP1Coordinate | glue | pg | b | T3 overall | mcr-quot + glue Props | queued (another project task); **A3, A12** |
| h11 TYZThm11Integral | T-1 | pub | a | T4 | cite | in flight (cloud) |
| h29 TYZLemma29Mod2 | T-3 | comp | a | T4 | cite | in flight (cloud) |
| hS ShimuraReciprocityModFn | T-13, T-14 | comp | b (N = 32) | T2 glue / T4 leaves | reduce + prove glue | **free: A7** |
| h33 TYZThm33 | T-12 | pub | a | T4 | cite | free |
| hL2 FHNonvanishing | Z-1 | comp | b (C_d) | T4 (swap T1) | owner swap to `FHNonvanishingCd` | free |
| hL3 GrossZagierHeegner | Z-2 | comp | b (C_d) | T4 (swap T1) | owner swap to `GrossZagierHeegnerCd` | free |
| (w63) blr_1_2_4 | — | pub | b (.mp, 𝓞_L) | T2 | prove .mp | **free: A10** |
| (w63) faltingsLemma5Printed | — | pub | b, one-sided | T4 (T2 bypass) | cite | free |
| (w63) raynaudKernelBound | — | pub | **unused in substance** | T1 | plumbing | **free: A1** |
| (w63) sga3_VIB_3_10 | — | pub | b (DVR/𝓞_L) | T2 (DVR T1) | specialize | free (next) |
| (w63) sga7_IX_3_3 | — | pub | b | T4 | cite | free |
| (w63) egaIV_8_10_5_openImm | — | pub | b | T1 | prove | **free: A4** |
| (w63) mumfordRigidityCore | — | pub | b (converts …Ab fields) | T3 | cite | route-a-fold (w63) |

**Tier counts** (65 base statements; tier of the cheapest route in the tsv's `tier` column; SPECULATIVE beyond the
VERIFIED findings of §0):

| cheapest tier | count | statements |
|---|---|---|
| T1 | 8 | bdRInvariants (plumbing); igusaPsi4, igusaChi10 (T1–T2 specialized); neronSchemeModelExistsDVR (NF form, T1–T2); quotientP1Coordinate (only its parts P1SchemeQ and the NV removal; T3 overall); dsThm966, hL2, hL3 (T1 only as owner/reviewer decisions, not proofs) |
| T2 | 17 | mulEtaleAbelianScheme, mumfordTorsionAlgClosed, yuThm11, qmCentralizerCMC, milneIsogenyQuasiInverse, valenceFormulaCocompactEq (Γ* form), shimizuCovolumeO1, hS (RingClassLattice); in flight: cartierSmooth, geomConnOfRationalPoint, groupSchemeEquidim, regularSmoothPerfect, igusaGL2, thetaRatiosAlgebraic, tateTwistInvariants, axSenTate, egaIV_8_10_5_xii |
| T3 | 10 | gonzalezRotgerCountX6, shimuraTaniyamaQbar, t09SymmIsogenyExists, gagaMorphism, neronSchemeExtensionExists (by gluing); in flight or under review: homFree, charPoly, poincareComplement, semistableUnipotent, semistablePersistsDVR |
| T4 | 25 | r1r2, shimuraFamily, r7a, r9a, r9b, hodgeTateDecompAbVar, deRhamH1AbVarT, r11r12, eigenformHTNew, dsThm965, r16, r17, bostLowerBound, javanpeykarBound, pazukiCor13Upper, gaudronRemondThm14, semistableReductionDVR, raynaudSemistable, uniformizationLeafAll, x6ConicModel, shimuraGoodReductionNoGuard, deligneComponentsY3Printed, h11, h29, h33 |
| done / superseded (w63) | 5 | igusaCMValue24, genusX1Field, semistableNeronBaseChange, faltingsLemma5BC, neronLocalizesDVR |

w63's new fields: T1 raynaudKernelBound (plumbing) and egaIV_8_10_5_openImm; T2 blr_1_2_4 (.mp) and sga3_VIB_3_10
(DVR form T1); T3 mumfordRigidityCore; T4 faltingsLemma5Printed (T2 bypass) and sga7_IX_3_3.

Status counts (base, from the tsv):
- free 32;
- in flight 20;
- done in w63 or done 5;
- under review 4;
- blocked 2;
- queued 2.

## 3. What was checked, and how

- **Compiled** (`run_probe.sh`: plain `lean`, with the LEAN_PATH of the main checkout ~/dzq at e38375b3, after its
  `lake build ZInQKernel.OneProof.Main` exited 0):
  - `GlueProbe.lean`: finding 3, the `rfl`, the theorem and its axioms; the P¹ `#check`s.
  - `VerifyProbe.lean`: 24 `#check`s of the Mathlib, vendored and chain declarations cited above.
  - `MCRQuotNV.lean`: mcr-quot's composite without `CoverModelOfHeckeN` (finding 3).
  - `ClosureProbe.lean`: membership of the `t23` consumers and of the glue-route constants in the closure of
    `HDec.HSyn.sixContactMin_of_open12` (212 392 constants).
  - The GZStatements module is not in that build, so its statements were read instead (`Weak.lean` L46–145).
- **Read by me:** findings 1, 2, 5, 6, 7 and 8 (GZ, R1pi0Props).
  - The `hT` uses of `ThetaModularity`.
  - `transfer_core` and w63's `faltingsLemma5_of_printed`.
  - mcr-quot's `hCov` uses, `ModelYIrreducible`, `HeckeIrreducible`, `Y3Connected`.
  - t5-glue's tip and `RingClassLattice`.
  - Every verbatim statement in §1.
  - The fleet notes of c-to-printed2, x6-glue, shimura-cft and theta-glue.
- **Agent-only (SPECULATIVE):** all other consumer traces and objects in the tsv. The "use (b)" restrictions marked
  "S" in the tsv's `marks` column were not re-read. In particular:
  - p = 5 only for the Hodge fields;
  - characteristic 0 for `milneIsogenyQuasiInverse`, `mumfordTorsionAlgClosed`;
  - the r6 consumers of `neronSchemeModelExistsDVR`;
  - `yuThm11`'s consumers.
- **Upstream issue numbers:** there is no mapping in the tree. The CloudW06 NOTICE puts H-72 under #81 (and
  T11bExists.lean puts H-75 under #82), CloudW02 puts H-67 under #80, and CloudW07/W08 put H-36, H-80, H-33 under
  #83. The `issue` column is otherwise "—" (UNVERIFIED).

## 4. Not checked

- The success odds and every proof route in §1 (all SPECULATIVE).
- Whether `IsNeronModelOver` allows A10's spread-out argument without the "if" direction.
- Whether a non-CM `ℚ̄`-object is available for A12.
- The consumer side of the w63 restatements beyond TailZ17 (agent A: only conversions).
- The R1recProps clause scan.
