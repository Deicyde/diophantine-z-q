import ZInQKernel.OneProof.H.TailZ19

/-!
# sh-route, top level: the three strict-henselization leaves of reduct-glue from one Néron leaf
# and commutative algebra

Task sh-route (2026-11-14). Namespace `ShRoute`. Appended after `ReductGlue.lean` (a verbatim copy of
`scratch/reduct-glue/ReductGlue.lean` = `Base.lean` + `Body.lean`), so the reduct-glue statements are
used, never restated.

* `IsSHUnram O O₁ hO`: `O₁ ⊇ O` is a strictly henselian DVR, `K₁/K` algebraic, a uniformizer of `O`
  stays a uniformizer of `O₁` (ramification index 1), and `κ(O₁)/κ(O)` is separable.
* LEAF `NeronBaseChangeSH` (BLR, *Néron models*, §7.2 Thm. 1 / §1.2 Prop. 2; UNVERIFIED): Néron models
  base change along such `O → O₁`. In characteristic 0 these hypotheses force `O₁ ≅ O^sh` (see the
  report), so the leaf is the print's "Néron models commute with strict henselization".
* commutative algebra (GLUE, proved in `CA.lean` or named here): `SHExists0`, `SHInside0`, `SHPair0`.
* the three reduct-glue leaves in characteristic 0 with perfect residue field
  (`StrictHenselizationNeron0`, `StrictHenselizationPair0`, `StrictHenselizationInside0`: the
  verbatim statements with the two hypotheses `[CharZero K]`, `[PerfectField κ(O)]` added) are
  theorems from these;
* the resulting char-0 forms of reduct-glue's general-DVR leaves: `RaynaudSemistable0`,
  `SemistablePersistsDVR0`, `SemistableUnipotent0`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety Pts torsion galAct IsInertia UnipSq HasGoodReduction)
open ReductSplit ReductGlue
set_option linter.style.haveILetI false

namespace ShRoute

/-- `O₁ ⊇ O` is an unramified strictly henselian extension: `O₁` is a strictly henselian DVR,
`K₁/K` is algebraic, a uniformizer of `O` is a uniformizer of `O₁`, and the residue extension is
separable. (In characteristic 0 this characterizes the strict henselization of `O`; see the report.) -/
def IsSHUnram {K K₁ : Type} [Field K] [Field K₁] [Algebra K K₁] (O : ValuationSubring K)
    (O₁ : ValuationSubring K₁) (hO : O₁.comap (algebraMap K K₁) = O) : Prop :=
  IsStrictlyHenselianDVR O₁ ∧ Algebra.IsAlgebraic K K₁ ∧
    (∀ ϖ : O, Irreducible ϖ → Irreducible (comapHom hO ϖ)) ∧
    (letI := (resMap hO).toAlgebra
     Algebra.IsSeparable (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O₁))

/-- **LEAF `NeronBaseChangeSH`** (Néron models commute with strict henselization:
Bosch–Lütkebohmert–Raynaud, *Néron models*, §7.2 Thm. 1 and §1.2 Prop. 2; numbers UNVERIFIED). `K` of
characteristic 0, `O ⊆ K` a DVR, `O₁ ⊇ O` an unramified strictly henselian extension with `K₁/K`
algebraic (`IsSHUnram`); then the base change of a Néron model of `A` over `O` is a Néron model of
`A_{K₁}` over `O₁`. In characteristic 0 the hypotheses force `O → O₁` to be (isomorphic over `O` to)
the strict henselization `O → O^sh` (report §3), so this is the printed statement for `O^sh`. -/
def NeronBaseChangeSH : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K₁ : Type) [Field K₁] [Algebra K K₁] (O₁ : ValuationSubring K₁)
    (hO : O₁.comap (algebraMap K K₁) = O), IsSHUnram O O₁ hO →
    ∀ (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O), 𝒩.IsNeronModel → (bcDVR hO 𝒩).IsNeronModel

theorem isSHNeronExt_of (hN : NeronBaseChangeSH) {K K₁ : Type} [Field K] [CharZero K] [Field K₁]
    [Algebra K K₁] {O : ValuationSubring K} [IsDiscreteValuationRing O] {O₁ : ValuationSubring K₁}
    {hO : O₁.comap (algebraMap K K₁) = O} (h : IsSHUnram O O₁ hO) : IsSHNeronExt O O₁ hO := by
  refine ⟨h.1, ?_, hN K O K₁ O₁ hO h⟩
  letI := (resMap hO).toAlgebra
  have := h.2.2.2
  exact Algebra.IsSeparable.isAlgebraic _ _

/-! ## The commutative algebra (GLUE; proved in `CA.lean`, see the report) -/

/-- **GLUE `SHExists0`** (existence of the strict henselization of a DVR as an unramified strictly
henselian extension: EGA IV₄ 18.8.8/18.8.13; here built as the valuation ring of the inertia field in
an algebraic closure). -/
def SHExists0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)],
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (O' : ValuationSubring K')
      (hO : O'.comap (algebraMap K K') = O), IsSHUnram O O' hO

/-- **GLUE `SHInside0`** (the valuation ring of the inertia field of `w` in an algebraic closure is
an unramified strictly henselian extension of `O`, and the inertia group of `w` fixes the inertia
field). -/
def SHInside0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O →
    ∃ (E : IntermediateField K Ω) (hE : (w.comap (algebraMap E Ω)).comap (algebraMap K E) = O),
      IsSHUnram O (w.comap (algebraMap E Ω)) hE ∧
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → ∀ x ∈ E, σ x = x

/-- **GLUE `SHPair0`** (strict henselizations nest along a finite extension: for `O' ⊆ K'` over
`O ⊆ K` with `K'/K` finite, unramified strictly henselian extensions `P ⊇ O`, `P' ⊇ O'` with
`E'/E` finite and `P'` over `P`; here the inertia fields of one valuation ring `w` of an algebraic
closure of `K'`, over `K` and over `K'`). -/
def SHPair0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K K') = O),
    ∃ (E E' : Type) (_ : Field E) (_ : Field E') (_ : Algebra K E) (_ : Algebra K' E')
      (_ : Algebra E E') (_ : Algebra K E') (_ : IsScalarTower K E E') (_ : IsScalarTower K K' E')
      (_ : FiniteDimensional E E') (P : ValuationSubring E) (P' : ValuationSubring E')
      (hP : P.comap (algebraMap K E) = O) (hP' : P'.comap (algebraMap K' E') = O'),
      IsSHUnram O P hP ∧ IsSHUnram O' P' hP' ∧ P'.comap (algebraMap E E') = P

/-! ## The three reduct-glue leaves in characteristic 0 (verbatim plus `[CharZero K]`,
`[PerfectField κ(O)]`) -/

/-- `StrictHenselizationNeron` (reduct-glue) for `K` of characteristic 0 with perfect residue field. -/
def StrictHenselizationNeron0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)],
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (O' : ValuationSubring K')
      (hO : O'.comap (algebraMap K K') = O),
      IsStrictlyHenselianDVR O' ∧
      (letI := (resMap hO).toAlgebra
       Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')) ∧
      ∀ (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O), 𝒩.IsNeronModel → (bcDVR hO 𝒩).IsNeronModel

/-- `StrictHenselizationPair` (reduct-glue) for `K` of characteristic 0 with perfect residue
field. -/
def StrictHenselizationPair0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K K') = O),
    ∃ (E E' : Type) (_ : Field E) (_ : Field E') (_ : Algebra K E) (_ : Algebra K' E')
      (_ : Algebra E E') (_ : Algebra K E') (_ : IsScalarTower K E E') (_ : IsScalarTower K K' E')
      (_ : FiniteDimensional E E') (P : ValuationSubring E) (P' : ValuationSubring E')
      (hP : P.comap (algebraMap K E) = O) (hP' : P'.comap (algebraMap K' E') = O'),
      IsSHNeronExt O P hP ∧ IsSHNeronExt O' P' hP' ∧ P'.comap (algebraMap E E') = P

/-- `StrictHenselizationInside` (reduct-glue) for `K` of characteristic 0 with perfect residue
field. -/
def StrictHenselizationInside0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O →
    ∃ (E : IntermediateField K Ω) (hE : (w.comap (algebraMap E Ω)).comap (algebraMap K E) = O),
      IsSHNeronExt O (w.comap (algebraMap E Ω)) hE ∧
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → ∀ x ∈ E, σ x = x

theorem strictHenselizationNeron0_of (hN : NeronBaseChangeSH) (hC : SHExists0) :
    StrictHenselizationNeron0 := by
  intro K _ _ O _ _
  obtain ⟨K', _, _, O', hO, h⟩ := hC K O
  exact ⟨K', inferInstance, inferInstance, O', hO, isSHNeronExt_of hN h⟩

theorem strictHenselizationPair0_of (hN : NeronBaseChangeSH) (hC : SHPair0) :
    StrictHenselizationPair0 := by
  intro K _ _ O _ _ K' _ _ _ O' _ hO
  obtain ⟨E, E', _, _, _, _, _, _, _, _, _, P, P', hP, hP', h1, h2, h3⟩ := hC K O K' O' hO
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  exact ⟨E, E', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, P, P', hP, hP',
    isSHNeronExt_of hN h1, isSHNeronExt_of hN h2, h3⟩

theorem strictHenselizationInside0_of (hN : NeronBaseChangeSH) (hC : SHInside0) :
    StrictHenselizationInside0 := by
  intro K _ _ O _ _ Ω _ _ _ w hw
  obtain ⟨E, hE, h, hfix⟩ := hC K O Ω w hw
  exact ⟨E, hE, isSHNeronExt_of hN h, hfix⟩

/-! ## The general-DVR leaves of reduct-glue in characteristic 0 -/

/-- `RaynaudSemistable` (reduct-split; SGA 7 IX 4.7) for `K` of characteristic 0 with perfect
residue field. -/
def RaynaudSemistable0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)] (A : PkgI3.AbVar K)
    (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    SemistableNeronModels A O

/-- `SemistablePersistsDVR` (reduct-split; SGA 7 IX 3.3, first assertion) for `K` of
characteristic 0 with perfect residue field. -/
def SemistablePersistsDVR0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'], O'.comap (algebraMap K K') = O →
    ∀ A : PkgI3.AbVar K, HasSemistableReduction A O → SemistableNeronModels (A.baseChange K') O'

/-- `SemistableUnipotent` (reduct-split; SGA 7 IX 3.5) for `K` of characteristic 0 with perfect
residue field. -/
def SemistableUnipotent0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

open ZInQ.Contrib.AbVarBC in
/-- **SGA 7 IX 4.7 over a DVR of a characteristic-0 field from its strictly henselian form**: the
proof of reduct-glue's `raynaudSemistable_of_SH'`, with `StrictHenselizationNeron0`. -/
theorem raynaudSemistable0_of (hR : RaynaudSemistableSH) (hSN : StrictHenselizationNeron0)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : RaynaudSemistable0 := by
  intro K _ _ O _ _ A m hm3 hmu htors 𝒩 h𝒩
  obtain ⟨K', _, _, O', hO, hSH, halg, hbc⟩ := hSN K O
  haveI : IsDiscreteValuationRing O' := hSH.1
  have hmu' : IsUnit (m : O') := by
    have := hmu.map (comapHom hO)
    rwa [map_natCast] at this
  rw [isSemistable_bcDVR_iff hO halg]
  refine hR K' O' hSH (A.baseChange K') m hm3 hmu' ?_ _ (hbc A 𝒩 h𝒩)
  intro x hx
  have hmK : (m : K) ≠ 0 := natCast_ne_zero_of_isUnit O hmu
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K' := IsAlgClosed.lift
  obtain ⟨p, hp, hpx⟩ := torsion_descends_etale hE A κ m hmK x hx
  obtain ⟨z, hz⟩ := htors p hp
  refine ⟨(bcPt A K').symm (extPt A (Algebra.ofId K K') z), ?_⟩
  rw [← hpx, ← hz]
  apply (bcPt A (AlgebraicClosure K')).injective
  rw [MulEquiv.apply_symm_apply, bcPt_extPt, MulEquiv.apply_symm_apply, extPt_extPt, extPt_extPt]
  congr 1
  ext a
  simp

/-- **SGA 7 IX 3.3 (first assertion) over a DVR of a characteristic-0 field from the strictly
henselian form**: the proof of reduct-glue's `persistsFromSH_of`, with `StrictHenselizationPair0`. -/
theorem semistablePersistsDVR0_of (hSH : SemistablePersistsSH) (hPair : StrictHenselizationPair0) :
    SemistablePersistsDVR0 := by
  intro K _ _ O _ _ K' _ _ _ O' _ hO A hA 𝒩' h𝒩'
  obtain ⟨E, E', _, _, _, _, _, _, _, _, _, P, P', hP, hP', ⟨hSHP, halgP, hbcP⟩,
    ⟨hSHP', halgP', hbcP'⟩, hPP'⟩ := hPair K O K' O' hO
  haveI : IsDiscreteValuationRing P := hSHP.1
  haveI : IsDiscreteValuationRing P' := hSHP'.1
  have hAE : HasSemistableReduction (A.baseChange E) P := by
    obtain ⟨𝒩, h𝒩, hs⟩ := hA
    exact ⟨bcDVR hP 𝒩, hbcP A 𝒩 h𝒩, (isSemistable_bcDVR_iff hP halgP 𝒩).mp hs⟩
  have h1 : SemistableNeronModels ((A.baseChange E).baseChange E') P' :=
    hSH E P hSHP E' P' hPP' (A.baseChange E) hAE
  have he : IsMonHom (bcbcIso A E E' ≪≫ (bcbcIso A K' E').symm).hom := by
    haveI := bcbcIso_isMonHom A E E'
    have : IsMonHom (bcbcIso A K' E').inv := by
      haveI := bcbcIso_isMonHom A K' E'
      infer_instance
    exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ (bcbcIso_isMonHom A E E') this
  have h2 : SemistableNeronModels ((A.baseChange K').baseChange E') P' :=
    semistableNeronModels_transport (bcbcIso A E E' ≪≫ (bcbcIso A K' E').symm) he h1
  rw [isSemistable_bcDVR_iff hP' halgP']
  exact h2 _ (hbcP' (A.baseChange K') 𝒩' h𝒩')

/-- **SGA 7 IX 3.5 over a DVR of a characteristic-0 field from the strictly henselian form**:
reduct-glue's `unipotentFromSH_of` applied through `StrictHenselizationInside0`. -/
theorem semistableUnipotent0_of (hSH : SemistableUnipotentSH) (hIn : StrictHenselizationInside0) :
    SemistableUnipotent0 := by
  intro K _ _ O _ _ Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t
  obtain ⟨E, hE, ⟨hSHP, halg, hbc⟩, hfix⟩ := hIn K O Ω w hw
  haveI : IsDiscreteValuationRing (w.comap (algebraMap E Ω)) := hSHP.1
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) E⟩
  have hAE : HasSemistableReduction (A.baseChange E) (w.comap (algebraMap E Ω)) := by
    obtain ⟨𝒩, h𝒩, hs⟩ := hA
    exact ⟨bcDVR hE 𝒩, hbc A 𝒩 h𝒩, (isSemistable_bcDVR_iff hE halg 𝒩).mp hs⟩
  have hℓP : IsUnit (ℓ : w.comap (algebraMap E Ω)) := by
    have := hℓ.map (comapHom hE)
    rwa [map_natCast] at this
  let σ₁ := toE E σ (hfix σ hσ)
  have hσ₁ : IsInertia w σ₁ := isInertia_toE E w σ (hfix σ hσ) hσ
  let φ : TΩ (A.baseChange E) Ω ℓ →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive (ZInQ.Contrib.AbVarBC.bcPt A Ω).toMonoidHom)
  let ψ : TΩ A Ω ℓ →ₗ[ℤ_[ℓ]] TΩ (A.baseChange E) Ω ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive (ZInQ.Contrib.AbVarBC.bcPt A Ω).symm.toMonoidHom)
  have hφψ : φ (ψ t) = t := by
    apply Subtype.ext
    funext n
    change Additive.ofMul (ZInQ.Contrib.AbVarBC.bcPt A Ω ((ZInQ.Contrib.AbVarBC.bcPt A Ω).symm
      (Additive.toMul (t.1 n)))) = t.1 n
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hcomm : ∀ s, φ (galTΩ (A.baseChange E) ℓ σ₁ s) = galTΩ A ℓ σ (φ s) := by
    intro s
    apply Subtype.ext
    funext n
    change Additive.ofMul (ZInQ.Contrib.AbVarBC.bcPt A Ω ((A.baseChange E).galAct σ₁
      (Additive.toMul (s.1 n)))) =
      Additive.ofMul (A.galAct σ (ZInQ.Contrib.AbVarBC.bcPt A Ω (Additive.toMul (s.1 n))))
    rw [ZInQ.Contrib.AbVarBC.bcPt_galAct, toE_restrictScalars]
  have key := hSH E (w.comap (algebraMap E Ω)) hSHP Ω w rfl (A.baseChange E) hAE ℓ hℓP σ₁ hσ₁
    (ψ t)
  have := congrArg φ key
  simp only [map_add, map_sub, map_nsmul, map_zero, hcomm, hφψ] at this
  exact this

/-- **The route, assembled**: the char-0 general-DVR leaves 4.7, 3.3a, 3.5 from the printed
(strictly henselian) SGA 7 leaves, the bundle leaf `MulEtaleAbelianScheme`, the Néron leaf
`NeronBaseChangeSH` and the commutative algebra. -/
theorem route (hR : RaynaudSemistableSH) (hP : SemistablePersistsSH)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) (hN : NeronBaseChangeSH) (hC : SHExists0)
    (hC2 : SHPair0) : RaynaudSemistable0 ∧ SemistablePersistsDVR0 :=
  ⟨raynaudSemistable0_of hR (strictHenselizationNeron0_of hN hC) hE,
   semistablePersistsDVR0_of hP (strictHenselizationPair0_of hN hC2)⟩

end ShRoute


open IsLocalRing

set_option linter.style.haveILetI false

namespace ShRoute

/-! ## A. Valuation rings over a Dedekind domain are localizations -/

section Loc

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F]

/-- `R → W` for a valuation subring `W` of `Frac R` containing `R`. -/
def toW (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) : R →+* W :=
  (algebraMap R F).codRestrict W.toSubring hW

/-- The center `R ∩ 𝔪_W`. -/
def ctr (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) : Ideal R :=
  (maximalIdeal W).comap (toW W hW)

theorem mem_ctr_iff (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) (r : R) :
    r ∈ ctr W hW ↔ algebraMap R F r ∈ W.nonunits := by
  change toW W hW r ∈ maximalIdeal W ↔ _
  rw [ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff]
  rfl

instance ctr_isPrime (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) :
    (ctr W hW).IsPrime := Ideal.comap_isPrime _ _

theorem isUnit_toW (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) {s : R}
    (hs : s ∉ ctr W hW) : IsUnit (toW W hW s) := by
  by_contra h
  exact hs ((mem_maximalIdeal _).mpr h)

theorem mem_of_mul_eq' (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) {x : F}
    {a s : R} (hs : s ∉ ctr W hW) (h : x * algebraMap R F s = algebraMap R F a) : x ∈ W := by
  obtain ⟨u, hu⟩ := isUnit_toW W hW hs
  have h1 : ((u : W) : F) = algebraMap R F s := by rw [hu]; rfl
  have h2 : (((u⁻¹ : Wˣ) : W) : F) * ((u : W) : F) = 1 :=
    congrArg (fun z : W => (z : F)) (Units.inv_mul u)
  have : x = algebraMap R F a * (((u⁻¹ : Wˣ) : W) : F) := by
    rw [← h, h1.symm, _root_.mul_assoc, mul_comm ((u : W) : F), h2, _root_.mul_one]
  rw [this]
  exact mul_mem (hW a) (u⁻¹ : Wˣ).1.2

/-- **A valuation subring `W ⊇ R` of `Frac R` with nonzero center is the localization of `R` at
its center**: every `x ∈ W` is `a/s` with `a, s ∈ R`, `s ∉ 𝔭`. (Generalizes reduct-glue's
`mem_iff_exists` from `𝓞_L` to any Dedekind domain; same proof.) -/
theorem exists_of_mem (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W)
    (h0 : ctr W hW ≠ ⊥) {x : F} (hx : x ∈ W) :
    ∃ a s : R, s ∉ ctr W hW ∧ x * algebraMap R F s = algebraMap R F a := by
  let 𝔭 := ctr W hW
  let B := Localization.AtPrime 𝔭
  haveI : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h0 B
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : (algebraMap R F b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr (nonZeroDivisors.ne_zero hb)
  obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap R B a) (algebraMap R B b)
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl c
  have hinj := IsLocalization.injective B 𝔭.primeCompl_le_nonZeroDivisors
  have hspec := IsLocalization.mk'_spec B r s
  have hs : (s : R) ∉ ctr W hW := s.2
  rcases hc with h | h
  · have h' : a * r = b * s := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hspec]
      ring
    have hL : (algebraMap R F a) * (algebraMap R F r) =
        (algebraMap R F b) * (algebraMap R F s) := by
      rw [← map_mul, ← map_mul, h']
    by_cases hr : r ∈ 𝔭
    · exfalso
      apply hs
      have hX : (⟨_, hx⟩ : W) * toW W hW r = toW W hW s := by
        apply Subtype.ext
        change (algebraMap R F a / algebraMap R F b) * (algebraMap R F r) = algebraMap R F s
        rw [div_mul_eq_mul_div, hL, mul_div_cancel_left₀ _ hb0]
      change toW W hW s ∈ maximalIdeal W
      rw [← hX]
      exact Ideal.mul_mem_left _ _ hr
    · refine ⟨s, r, hr, ?_⟩
      rw [div_mul_eq_mul_div, hL, mul_div_cancel_left₀ _ hb0]
  · have h' : b * r = a * s := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hspec]
      ring
    refine ⟨r, s, hs, ?_⟩
    have hL : (algebraMap R F b) * (algebraMap R F r) =
        (algebraMap R F a) * (algebraMap R F s) := by
      rw [← map_mul, ← map_mul, h']
    rw [div_mul_eq_mul_div, ← hL, mul_div_cancel_left₀ _ hb0]

end Loc

/-! ## B. The inertia field of a finite Galois extension is unramified -/

section Key

theorem nonunits_comap {E M : Type*} [Field E] [Field M] (f : E →+* M) (W : ValuationSubring M)
    (x : E) : x ∈ (W.comap f).nonunits ↔ f x ∈ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  simp only [ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

theorem div_mem_nonunits {M : Type*} [Field M] (W : ValuationSubring M) {n d : M}
    (hn : n ∈ W.nonunits) (hd : d ∈ W) (hd' : d ∉ W.nonunits) : n / d ∈ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hn hd' ⊢
  have h1 : W.valuation d = 1 :=
    le_antisymm ((W.valuation_le_one_iff d).mpr hd) (not_lt.mp hd')
  rw [map_div₀, h1, div_one]
  exact hn

theorem div_mem {M : Type*} [Field M] (W : ValuationSubring M) {n d : M}
    (hn : n ∈ W) (hd : d ∈ W) (hd' : d ∉ W.nonunits) : n / d ∈ W := by
  rw [← W.valuation_le_one_iff] at hn ⊢
  rw [ValuationSubring.mem_nonunits_iff] at hd'
  have h1 : W.valuation d = 1 :=
    le_antisymm ((W.valuation_le_one_iff d).mpr hd) (not_lt.mp hd')
  rw [map_div₀, h1, div_one]
  exact hn

/-- An element of `M` integral over a subring contained in `W` lies in `W`. -/
theorem mem_of_isIntegral {A M : Type*} [CommRing A] [Field M] [Algebra A M]
    (W : ValuationSubring M) (hAW : ∀ a : A, algebraMap A M a ∈ W) {x : M}
    (hx : IsIntegral A x) : x ∈ W := by
  letI : Algebra A W := ((algebraMap A M).codRestrict W.toSubring hAW).toAlgebra
  haveI : IsScalarTower A W M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h2 : IsIntegral W x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]; exact y.2


/-- **Uniformizer from `𝔮 · J ⊆ ϖR` with `J ⊄ 𝔮`.** `R` Dedekind, `W` a valuation subring of
`F = Frac R` over `R` with center `𝔮 ≠ 0`, `ϖ ∈ 𝔮` and `j ∉ 𝔮` with `𝔮 · j ⊆ ϖ R`. Then every nonzero
`y ∈ F` with `y = a/s`, `s ∉ 𝔮`, is `ϖⁿ` times a unit of `W`. -/
theorem unit_mul_pow_of_div {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (W : ValuationSubring F)
    (hW : ∀ r : R, algebraMap R F r ∈ W) (ϖ j : R) (hj : j ∉ ctr W hW)
    (hdiv : ∀ n ∈ ctr W hW, ∃ r : R, n * j = ϖ * r) (hϖ : ϖ ∈ ctr W hW) (hϖ0 : ϖ ≠ 0) :
    ∀ (m : ℕ) (y : F) (a s : R), y ≠ 0 → s ∉ ctr W hW →
      y * algebraMap R F s = algebraMap R F a → a ∉ (ctr W hW) ^ (m + 1) →
      ∃ n : ℕ, y / algebraMap R F ϖ ^ n ∈ W ∧ (y / algebraMap R F ϖ ^ n)⁻¹ ∈ W := by
  set 𝔮 := ctr W hW
  have hϖF : algebraMap R F ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hϖ0
  have unit_case : ∀ (y : F) (a s : R), y ≠ 0 → s ∉ 𝔮 →
      y * algebraMap R F s = algebraMap R F a → a ∉ 𝔮 →
      ∃ n : ℕ, y / algebraMap R F ϖ ^ n ∈ W ∧ (y / algebraMap R F ϖ ^ n)⁻¹ ∈ W := by
    intro y a s hy hs hys ha
    refine ⟨0, ?_, ?_⟩
    · rw [pow_zero, div_one]; exact mem_of_mul_eq' W hW hs hys
    · rw [pow_zero, div_one]
      refine mem_of_mul_eq' W hW (a := s) ha ?_
      rw [← hys]; field_simp
  intro m
  induction m with
  | zero =>
    intro y a s hy hs hys ha
    exact unit_case y a s hy hs hys (by rwa [zero_add, pow_one] at ha)
  | succ m ih =>
    intro y a s hy hs hys ha
    by_cases ha𝔮 : a ∉ 𝔮
    · exact unit_case y a s hy hs hys ha𝔮
    push Not at ha𝔮
    obtain ⟨r, hr⟩ := hdiv a ha𝔮
    have hsj : s * j ∉ 𝔮 := fun h =>
      ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hs hj)
    have hr' : r ∉ 𝔮 ^ (m + 1) := by
      intro hrm
      have h1 : j * a ∈ 𝔮 ^ (m + 1 + 1) := by
        rw [mul_comm, hr, pow_succ']
        exact Ideal.mul_mem_mul hϖ hrm
      rcases Ideal.IsPrime.mul_mem_pow 𝔮 h1 with h | h
      · exact hj h
      · exact ha h
    have hy' : y / algebraMap R F ϖ ≠ 0 := div_ne_zero hy hϖF
    have hys' : y / algebraMap R F ϖ * algebraMap R F (s * j) = algebraMap R F r := by
      have h2 : algebraMap R F a * algebraMap R F j = algebraMap R F ϖ * algebraMap R F r := by
        rw [← map_mul, ← map_mul, hr]
      rw [← hys] at h2
      rw [map_mul]
      field_simp
      linear_combination h2
    obtain ⟨n, h1, h2⟩ := ih (y / algebraMap R F ϖ) r (s * j) hy' hsj hys' hr'
    refine ⟨n + 1, ?_, ?_⟩
    · rwa [pow_succ', ← div_div]
    · rwa [pow_succ', ← div_div]

variable {K M : Type*} [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A K]
  [IsFractionRing A K] [Algebra A M] [IsScalarTower A K M]

instance instSMulCommClassGal : SMulCommClass (M ≃ₐ[K] M) A M where
  smul_comm σ a x := by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply A K M, AlgEquiv.commutes]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **Key lemma (finite level).** `M/K` finite Galois, `A ⊆ K` a DVR with perfect residue field,
`W` a valuation ring of `M` over `A`. If `x ∈ W`, `x ≠ 0` is fixed by every `σ ∈ Gal(M/K)` acting
trivially modulo `𝔪_W`, then `x = ϖⁿ · (unit of W)` for a uniformizer `ϖ` of `A`. -/
theorem key_finite [PerfectField (ResidueField A)]
    (W : ValuationSubring M) (hAW : ∀ a : A, algebraMap A M a ∈ W)
    (hctr : ∀ a : A, algebraMap A M a ∈ W.nonunits ↔ a ∈ maximalIdeal A)
    (ϖ : A) (hϖ : Irreducible ϖ) (x : M)
    (hfix : ∀ σ : M ≃ₐ[K] M, (∀ y ∈ W, σ y - y ∈ W.nonunits) → σ x = x)
    (hxW : x ∈ W) (hx0 : x ≠ 0) :
    ∃ n : ℕ, x / algebraMap A M ϖ ^ n ∈ W ∧ (x / algebraMap A M ϖ ^ n)⁻¹ ∈ W := by
  classical
  -- the ring of integers `S` of `M` over `A`
  let S := integralClosure A M
  haveI : IsDedekindDomain S := integralClosure.isDedekindDomain A K M
  haveI : Module.Finite A S := IsIntegralClosure.finite A K M S
  haveI : IsFractionRing S M := IsIntegralClosure.isFractionRing_of_finite_extension A K M S
  haveI : IsGaloisGroup (M ≃ₐ[K] M) A S := IsGaloisGroup.of_isFractionRing _ A S K M
  have hSW : ∀ s : S, algebraMap S M s ∈ W := fun s =>
    mem_of_isIntegral W hAW s.2
  let p := maximalIdeal A
  let P : Ideal S := ctr W hSW
  have hP : ∀ s : S, s ∈ P ↔ (s : M) ∈ W.nonunits := fun s => mem_ctr_iff W hSW s
  haveI : P.LiesOver p := by
    constructor
    ext a
    rw [Ideal.under_def, Ideal.mem_comap, hP]
    exact (hctr a).symm
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hϖp : ϖ ∈ p := (mem_maximalIdeal _).mpr hϖ.not_isUnit
  have hAinj : Function.Injective (algebraMap A M) := by
    rw [IsScalarTower.algebraMap_eq A K M]
    exact (algebraMap K M).injective.comp (IsFractionRing.injective A K)
  have hP0 : P ≠ ⊥ := by
    intro h
    have : algebraMap A S ϖ ∈ P := by rw [hP]; exact (hctr ϖ).mpr hϖp
    rw [h, Ideal.mem_bot] at this
    apply hϖ0
    apply hAinj
    rw [map_zero]
    exact congrArg (fun z : S => (z : M)) this
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  haveI : PerfectField (A ⧸ p) := ‹PerfectField (ResidueField A)›
  haveI : FaithfulSMul A S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    exact hAinj (congrArg (fun z : S => (z : M)) h)
  haveI : Module.IsTorsionFree A S := by
    rw [Module.isTorsionFree_iff_faithfulSMul]; infer_instance
  haveI : PerfectField p.ResidueField := PerfectField.of_ringEquiv
    (RingEquiv.ofBijective (algebraMap (A ⧸ p) p.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField p))
  have hcard : Nat.card (P.inertia (M ≃ₐ[K] M)) = p.ramificationIdxIn S :=
    Ideal.card_inertia_eq_ramificationIdxIn p P
  -- the inertia field `E` and its ring of integers `R`
  let H := P.inertia (M ≃ₐ[K] M)
  let E : IntermediateField K M := FixedPoints.intermediateField H
  haveI : IsScalarTower A E M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let R := integralClosure A E
  haveI : IsDedekindDomain R := integralClosure.isDedekindDomain A K E
  haveI : Module.Finite A R := IsIntegralClosure.finite A K E R
  haveI : IsFractionRing R E := IsIntegralClosure.isFractionRing_of_finite_extension A K E R
  have hRS : ∀ r : R, IsIntegral A (algebraMap E M (r : E)) := fun r =>
    r.2.map (IsScalarTower.toAlgHom A E M)
  let φ : R →+* S := ((algebraMap E M).comp (algebraMap R E)).codRestrict S (fun r => hRS r)
  letI : Algebra R S := φ.toAlgebra
  haveI : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq (fun a => by
    apply Subtype.ext
    change algebraMap A M a = algebraMap E M (algebraMap A E a)
    rw [← IsScalarTower.algebraMap_apply])
  haveI : IsScalarTower R S M := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.tower_top A
  haveI : IsGaloisGroup H E M := IsGaloisGroup.subgroup (M ≃ₐ[K] M) K M H
  haveI : IsGaloisGroup H R S := IsGaloisGroup.of_isFractionRing H R S E M
  haveI : Module.Finite R S := Module.Finite.of_restrictScalars_finite A R S
  haveI : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply Subtype.ext
    apply (algebraMap E M).injective
    exact congrArg (fun z : S => (z : M)) h
  haveI : Module.IsTorsionFree R S := by
    rw [Module.isTorsionFree_iff_faithfulSMul]; infer_instance
  let 𝔮 : Ideal R := P.under R
  haveI : 𝔮.LiesOver p := Ideal.LiesOver.tower_bot P 𝔮 p
  haveI : Algebra.HasSeparableResidueFieldsAt R S 𝔮 :=
    Algebra.HasSeparableResidueFieldsAt.tower_top p 𝔮
  have hcard' : Nat.card (P.inertia H) = 𝔮.ramificationIdxIn S :=
    Ideal.card_inertia_eq_ramificationIdxIn 𝔮 P
  have htop : P.inertia H = ⊤ := by
    ext h
    simp only [Subgroup.mem_top, iff_true]
    intro s
    exact h.2 s
  have hcardH : Nat.card (P.inertia H) = Nat.card H := by
    rw [htop]; exact Subgroup.card_top
  have he1 := Ideal.ramificationIdxIn_eq_ramificationIdx p P (M ≃ₐ[K] M)
  have he2 := Ideal.ramificationIdxIn_eq_ramificationIdx 𝔮 P H
  have htower := Ideal.ramificationIdx_tower (R := A) 𝔮 P
  have hepos : P.ramificationIdx A ≠ 0 := by
    rw [← he1, ← hcard]; exact Nat.card_pos.ne'
  have he𝔮 : 𝔮.ramificationIdx A = 1 := by
    rw [← he2, ← hcard', hcardH, ← he1, ← hcard] at htower
    have hc : 0 < Nat.card H := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hc (by rw [_root_.one_mul]; exact htower.symm)
  -- `p𝓞_E = 𝔮 · J` with `J ⊄ 𝔮`
  have hpspan : p = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hRinj : Function.Injective (algebraMap A R) := by
    intro a b h
    exact hAinj (congrArg (fun r : R => algebraMap E M (r : E)) h)
  have hpR0 : p.map (algebraMap A R) ≠ ⊥ := by
    rw [hpspan, Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot]
    exact fun h => hϖ0 (hRinj (by rw [h, map_zero]))
  have hmult := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p 𝔮 hpR0
  rw [he𝔮] at hmult
  have h𝔮top : 𝔮 ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have hfin : FiniteMultiplicity 𝔮 (p.map (algebraMap A R)) :=
    FiniteMultiplicity.of_not_isUnit (by rwa [Ideal.isUnit_iff]) hpR0
  obtain ⟨J, hJ⟩ : 𝔮 ∣ p.map (algebraMap A R) := by
    have := pow_multiplicity_dvd 𝔮 (p.map (algebraMap A R))
    rwa [← hmult, pow_one] at this
  have hJ𝔮 : ¬ J ≤ 𝔮 := by
    intro hle
    apply hfin.not_pow_dvd_of_multiplicity_lt (m := 2) (by rw [← hmult]; norm_num)
    rw [hJ, pow_two]
    exact mul_dvd_mul_left 𝔮 (Ideal.dvd_iff_le.mpr hle)
  obtain ⟨j, hjJ, hj𝔮⟩ := IsConcreteLE.not_le_iff_exists.mp hJ𝔮
  let ϖR := algebraMap A R ϖ
  have hϖR : p.map (algebraMap A R) = Ideal.span {ϖR} := by
    rw [hpspan, Ideal.map_span, Set.image_singleton]
  have hdivide : ∀ n ∈ 𝔮, ∃ r : R, n * j = ϖR * r := by
    intro n hn
    have : n * j ∈ p.map (algebraMap A R) := by
      rw [hJ]; exact Ideal.mul_mem_mul hn hjJ
    rw [hϖR, Ideal.mem_span_singleton'] at this
    obtain ⟨r, hr⟩ := this
    exact ⟨r, by rw [← hr, mul_comm]⟩
  have hϖ𝔮 : ϖR ∈ 𝔮 := by
    have : ϖR ∈ p.map (algebraMap A R) := Ideal.mem_map_of_mem _ hϖp
    rw [hJ] at this
    exact (Ideal.mul_le_right (I := J) (J := 𝔮)) (by rwa [mul_comm] at this)
  -- every element of the inertia group acts trivially modulo `𝔪_W` on all of `W`
  have hcond : ∀ σ ∈ H, ∀ y ∈ W, σ y - y ∈ W.nonunits := by
    intro σ hσ y hy
    obtain ⟨a, s, hs, hys⟩ := exists_of_mem W hSW hP0 hy
    have ha : σ (a : M) - a ∈ W.nonunits := by
      have := (hP _).mp (hσ a)
      have e1 : ((σ • a : S) : M) = σ (a : M) := rfl
      rwa [Subalgebra.coe_sub, e1] at this
    have hs' : σ (s : M) - s ∈ W.nonunits := by
      have := (hP _).mp (hσ s)
      have e1 : ((σ • s : S) : M) = σ (s : M) := rfl
      rwa [Subalgebra.coe_sub, e1] at this
    rw [hP] at hs
    have hsW : (s : M) ∈ W := hSW s
    rw [ValuationSubring.mem_nonunits_iff] at ha hs' hs ⊢
    have vs : W.valuation (s : M) = 1 :=
      le_antisymm ((W.valuation_le_one_iff _).mpr hsW) (not_lt.mp hs)
    have vσs : W.valuation (σ (s : M)) = 1 := by
      have : σ (s : M) = (s : M) + (σ (s : M) - s) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [vs]; exact hs'), vs]
    have hs0 : (s : M) ≠ 0 := fun h => by rw [h, map_zero] at vs; exact zero_ne_one vs
    have hσs0 : σ (s : M) ≠ 0 := fun h => by rw [h, map_zero] at vσs; exact zero_ne_one vσs
    have hy' : y = (a : M) / s := by rw [eq_div_iff hs0]; exact hys
    have key : σ y - y = ((σ (a : M) - a) * s - a * (σ (s : M) - s)) / (σ (s : M) * s) := by
      rw [hy', map_div₀]
      field_simp
      ring
    rw [key, map_div₀, map_mul, vσs, vs, _root_.mul_one, div_one]
    have haW : W.valuation (a : M) ≤ 1 := (W.valuation_le_one_iff _).mpr (hSW a)
    rw [sub_eq_add_neg]
    apply Valuation.map_add_lt _
    · rw [map_mul, vs, _root_.mul_one]; exact ha
    · rw [Valuation.map_neg, map_mul]
      calc W.valuation (a : M) * W.valuation (σ (s : M) - s)
          ≤ 1 * W.valuation (σ (s : M) - s) := by gcongr
        _ < 1 := by rw [_root_.one_mul]; exact hs'
  have hxE : x ∈ E := by
    intro h
    exact hfix h (hcond h h.2)
  -- the valuation ring of `E`
  let WE := W.comap (algebraMap E M)
  have hRW : ∀ r : R, algebraMap R E r ∈ WE := fun r => hSW (φ r)
  have hctrE : ctr WE hRW = 𝔮 := by
    ext r
    rw [mem_ctr_iff, nonunits_comap]
    exact (hP (φ r)).symm
  have hϖR0 : algebraMap A R ϖ ≠ 0 := fun h => hϖ0 (hRinj (by rw [h, map_zero]))
  have hctrE0 : ctr WE hRW ≠ ⊥ := by
    rw [hctrE]
    intro h
    rw [h] at hϖ𝔮
    exact hϖR0 hϖ𝔮
  obtain ⟨a, s, hs, hxs⟩ := exists_of_mem WE hRW hctrE0 (x := ⟨x, hxE⟩) hxW
  have hxE0 : (⟨x, hxE⟩ : E) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at hxs
    rcases mul_eq_zero.mp hxs with h' | h'
    · exact hxE0 h'
    · apply hs
      rw [(map_eq_zero_iff _ (IsFractionRing.injective R E)).mp h']
      exact Ideal.zero_mem _
  have hfa : FiniteMultiplicity 𝔮 (Ideal.span {a}) :=
    FiniteMultiplicity.of_not_isUnit (by rwa [Ideal.isUnit_iff])
      (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha0)
  have ham : a ∉ 𝔮 ^ (multiplicity 𝔮 (Ideal.span {a}) + 1) := by
    intro h
    apply hfa.not_pow_dvd_of_multiplicity_lt (lt_add_one _)
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h
  rw [← hctrE] at hdivide hϖ𝔮 hj𝔮 ham
  obtain ⟨n, h1, h2⟩ := unit_mul_pow_of_div WE hRW (algebraMap A R ϖ) j hj𝔮 hdivide hϖ𝔮 hϖR0
    _ _ a s hxE0 hs hxs ham
  have e : ((algebraMap A E ϖ : E) : M) = algebraMap A M ϖ := rfl
  refine ⟨n, ?_, ?_⟩
  · have := h1; simpa [WE, ValuationSubring.mem_comap, e] using this
  · have := h2; simpa [WE, ValuationSubring.mem_comap, e] using this

end Key

end ShRoute


/-!
# sh-route, part C: the inertia field inside an algebraic closure

`K` of characteristic 0, `Ω` an algebraic closure, `w` a valuation ring of `Ω`. The inertia field
`inertiaField w` is the set of `x ∈ Ω` such that, for some finite Galois `M ∋ x`, every
`τ ∈ Aut(Ω/K)` acting trivially modulo `𝔪_w` on `w ∩ M` fixes `x` (the union of the inertia fields
of the finite Galois subextensions).
-/

open IsLocalRing Polynomial

set_option linter.style.haveILetI false

namespace ShRoute

section Omega

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)

/-- `τ` acts trivially modulo `𝔪_w` on `w ∩ M`. -/
def CondM (M : IntermediateField K Ω) (τ : Ω ≃ₐ[K] Ω) : Prop :=
  ∀ y ∈ M, y ∈ w → τ y - y ∈ w.nonunits

theorem CondM.mono {M M' : IntermediateField K Ω} (h : M ≤ M') {τ : Ω ≃ₐ[K] Ω}
    (hτ : CondM w M' τ) : CondM w M τ := fun y hy => hτ y (h hy)

/-- `x ∈ M` is fixed by every `τ` acting trivially modulo `𝔪_w` on `w ∩ M`. -/
def FixVia (M : IntermediateField K Ω) (x : Ω) : Prop :=
  x ∈ M ∧ ∀ τ : Ω ≃ₐ[K] Ω, CondM w M τ → τ x = x

theorem FixVia.mono {M M' : IntermediateField K Ω} (h : M ≤ M') {x : Ω} (hx : FixVia w M x) :
    FixVia w M' x := ⟨h hx.1, fun τ hτ => hx.2 τ (hτ.mono w h)⟩

/-- `M` is finite Galois over `K`. -/
def IsFG (M : IntermediateField K Ω) : Prop := FiniteDimensional K M ∧ IsGalois K M

/-- An inertia automorphism acts trivially modulo `𝔪_w` on all of `w`. -/
theorem condM_of_isInertia {σ : Ω ≃ₐ[K] Ω} (hσ : PkgI2.IsInertia w σ) (M : IntermediateField K Ω) :
    CondM w M σ := by
  intro y _ hy
  obtain ⟨h, hI⟩ := hσ
  have h1 : (⟨σ, h⟩ : w.decompositionSubgroup K) • residue w ⟨y, hy⟩ = residue w ⟨y, hy⟩ := by
    have := congrArg (fun f => f (residue w ⟨y, hy⟩)) (MonoidHom.mem_ker.mp hI)
    exact this
  rw [← IsLocalRing.ResidueField.residue_smul] at h1
  have h2 := (Ideal.Quotient.eq).mp h1
  rw [ValuationSubring.valuation_lt_one_iff] at h2
  rw [ValuationSubring.mem_nonunits_iff]
  exact h2

variable [CharZero K] [IsAlgClosure K Ω]

theorem isFG_of (s : IntermediateField K Ω) [FiniteDimensional K s] :
    ∃ M : IntermediateField K Ω, IsFG M ∧ s ≤ M := by
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  refine ⟨IntermediateField.normalClosure K s Ω, ⟨inferInstance, ?_⟩, IntermediateField.le_normalClosure s⟩
  haveI : Algebra.IsSeparable K (IntermediateField.normalClosure K s Ω) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact ⟨⟩

theorem exists_two {M₁ M₂ : IntermediateField K Ω} (h₁ : IsFG M₁) (h₂ : IsFG M₂) :
    ∃ M : IntermediateField K Ω, IsFG M ∧ M₁ ≤ M ∧ M₂ ≤ M := by
  haveI := h₁.1
  haveI := h₂.1
  obtain ⟨M, hM, hle⟩ := isFG_of (M₁ ⊔ M₂)
  exact ⟨M, hM, le_trans le_sup_left hle, le_trans le_sup_right hle⟩

/-- The inertia field of `w` (over `K`). -/
def inertiaField : IntermediateField K Ω where
  carrier := {x | ∃ M : IntermediateField K Ω, IsFG M ∧ FixVia w M x}
  mul_mem' := by
    rintro x y ⟨M₁, h₁, hx⟩ ⟨M₂, h₂, hy⟩
    obtain ⟨M, hM, l₁, l₂⟩ := exists_two h₁ h₂
    have hx := hx.mono w l₁
    have hy := hy.mono w l₂
    exact ⟨M, hM, M.mul_mem hx.1 hy.1, fun τ hτ => by rw [map_mul, hx.2 τ hτ, hy.2 τ hτ]⟩
  add_mem' := by
    rintro x y ⟨M₁, h₁, hx⟩ ⟨M₂, h₂, hy⟩
    obtain ⟨M, hM, l₁, l₂⟩ := exists_two h₁ h₂
    have hx := hx.mono w l₁
    have hy := hy.mono w l₂
    exact ⟨M, hM, M.add_mem hx.1 hy.1, fun τ hτ => by rw [map_add, hx.2 τ hτ, hy.2 τ hτ]⟩
  algebraMap_mem' c := by
    obtain ⟨M, hM, -⟩ := isFG_of (⊥ : IntermediateField K Ω)
    exact ⟨M, hM, M.algebraMap_mem c, fun τ _ => τ.commutes c⟩
  inv_mem' := by
    rintro x ⟨M, hM, hx⟩
    exact ⟨M, hM, M.inv_mem hx.1, fun τ hτ => by rw [map_inv₀, hx.2 τ hτ]⟩

theorem mem_inertiaField {x : Ω} :
    x ∈ inertiaField (K := K) w ↔ ∃ M : IntermediateField K Ω, IsFG M ∧ FixVia w M x := Iff.rfl

/-- **The inertia group fixes the inertia field.** -/
theorem inertia_fixes {σ : Ω ≃ₐ[K] Ω} (hσ : PkgI2.IsInertia w σ) {x : Ω}
    (hx : x ∈ inertiaField (K := K) w) : σ x = x := by
  obtain ⟨M, -, hM⟩ := hx
  exact hM.2 σ (condM_of_isInertia w hσ M)

/-- Finitely many elements of the inertia field are fixed via one finite Galois `M`. -/
theorem exists_common (s : Finset Ω) (hs : ∀ x ∈ s, x ∈ inertiaField (K := K) w) :
    ∃ M : IntermediateField K Ω, IsFG M ∧ ∀ x ∈ s, FixVia w M x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨M, hM, -⟩ := isFG_of (⊥ : IntermediateField K Ω)
    exact ⟨M, hM, by simp⟩
  | insert a s _ ih =>
    obtain ⟨M₁, h₁, hM₁⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
    obtain ⟨M₂, h₂, hM₂⟩ := hs a (Finset.mem_insert_self a s)
    obtain ⟨M, hM, l₁, l₂⟩ := exists_two h₁ h₂
    refine ⟨M, hM, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hM₂.mono w l₂
    · exact (hM₁ x hx).mono w l₁

end Omega

section Ring

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)

theorem mem_max_iff (b : w) : b ∈ maximalIdeal w ↔ (b : Ω) ∈ w.nonunits := by
  rw [ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff]

theorem mem_max_comap_iff {E : Type} [Field E] (f : E →+* Ω) (a : w.comap f) :
    a ∈ maximalIdeal (w.comap f) ↔ f (a : E) ∈ w.nonunits := by
  rw [ValuationSubring.valuation_lt_one_iff, ← ValuationSubring.mem_nonunits_iff,
    nonunits_comap]

/-- **Roots near a point.** A monic `q ∈ w[X]` with `q(c) ∈ 𝔪_w` has a root `α ∈ w` with
`α ≡ c mod 𝔪_w` (`Ω` algebraically closed, `w` integrally closed). -/
theorem exists_root_near [IsAlgClosed Ω] (q : w[X]) (hq : q.Monic) (c : w)
    (hc : q.eval c ∈ maximalIdeal w) : ∃ α : w, q.IsRoot α ∧ α - c ∈ maximalIdeal w := by
  induction h : q.natDegree generalizing q with
  | zero =>
    exfalso
    rw [hq.natDegree_eq_zero] at h
    rw [h, eval_one] at hc
    exact (maximalIdeal.isMaximal w).ne_top ((Ideal.eq_top_iff_one _).mpr hc)
  | succ n ih =>
    have hdeg : (q.map (algebraMap w Ω)).degree ≠ 0 := by
      rw [hq.degree_map, degree_eq_natDegree hq.ne_zero, h]
      exact_mod_cast Nat.succ_ne_zero n
    obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root (q.map (algebraMap w Ω)) hdeg
    have hβw : β ∈ w := mem_of_isIntegral w (A := w) (fun a => a.2)
      ⟨q, hq, by rwa [IsRoot, Polynomial.eval_map] at hβ⟩
    let β' : w := ⟨β, hβw⟩
    have hr : q.IsRoot β' := by
      apply Subtype.ext
      rw [IsRoot, Polynomial.eval_map] at hβ
      have : algebraMap w Ω (q.eval β') = q.eval₂ (algebraMap w Ω) β := by
        rw [← eval₂_at_apply]; rfl
      exact this.trans hβ
    have hfac := (mul_divByMonic_eq_iff_isRoot).mpr hr
    have hq2 : (q /ₘ (X - C β')).Monic :=
      Monic.of_mul_monic_left (monic_X_sub_C β') (by rw [hfac]; exact hq)
    have hdeg2 : (q /ₘ (X - C β')).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C β'), h, natDegree_X_sub_C]; rfl
    rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at hc
    rcases (maximalIdeal.isMaximal w).isPrime.mem_or_mem hc with h1 | h1
    · exact ⟨β', hr, by rw [← neg_sub]; exact neg_mem h1⟩
    · obtain ⟨α, hα, hαc⟩ := ih (q /ₘ (X - C β')) hq2 h1 hdeg2
      refine ⟨α, ?_, hαc⟩
      rw [IsRoot, ← hfac, eval_mul, hα.eq_zero, mul_zero]

/-- **Two distinct roots with the same residue give a double root modulo `𝔪_w`.** -/
theorem derivative_eval_eq_zero_of_two_roots (q : w[X]) {α β : w} (hα : q.IsRoot α)
    (hβ : q.IsRoot β) (hne : α ≠ β) (hres : residue w α = residue w β) :
    ((q.map (residue w)).derivative).eval (residue w α) = 0 := by
  have hfac := (mul_divByMonic_eq_iff_isRoot).mpr hα
  set q1 := q /ₘ (X - C α)
  have hβ1 : q1.IsRoot β := by
    have := hβ
    rw [IsRoot, ← hfac, eval_mul, eval_sub, eval_X, eval_C] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  have hfac1 := (mul_divByMonic_eq_iff_isRoot).mpr hβ1
  rw [← hfac, ← hfac1]
  simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, derivative_mul,
    derivative_sub, derivative_X, derivative_C, eval_add, eval_mul, eval_sub, eval_X, eval_C,
    hres, sub_self, zero_mul, mul_zero, add_zero]

variable [CharZero K] [IsAlgClosure K Ω]

/-- The valuation ring of the inertia field. -/
abbrev wE : ValuationSubring (inertiaField (K := K) w) :=
  w.comap (algebraMap (inertiaField (K := K) w) Ω)

/-- `wE → Ω`. -/
def ιΩ : wE (K := K) w →+* Ω :=
  (algebraMap (inertiaField (K := K) w) Ω).comp (wE (K := K) w).subtype

/-- `wE → w`. -/
def ιw : wE (K := K) w →+* w :=
  (ιΩ (K := K) w).codRestrict w.toSubring (fun a => a.2)

theorem ιw_coe (a : wE (K := K) w) : ((ιw w a : w) : Ω) = ιΩ w a := rfl

/-- **Core lemma.** A root `α` of a monic `g` over the valuation ring of the inertia field whose
residue is a simple root of `g mod 𝔪_w` lies in the inertia field. -/
theorem mem_inertiaField_of_simple_root (g : (wE (K := K) w)[X]) (α : Ω)
    (hα : (g.map (ιΩ w)).eval α = 0) (hαw : α ∈ w)
    (hs : ((g.map ((residue w).comp (ιw w))).derivative).eval (residue w ⟨α, hαw⟩) ≠ 0) :
    α ∈ inertiaField (K := K) w := by
  classical
  -- the coefficients are fixed via one `M₀`
  obtain ⟨M₀, h₀, hM₀⟩ := exists_common w (g.support.image fun i => ιΩ w (g.coeff i))
    (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact (g.coeff i : inertiaField (K := K) w).2)
  haveI := h₀.1
  have hαint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  haveI : FiniteDimensional K (IntermediateField.adjoin K {α}) :=
    IntermediateField.adjoin.finiteDimensional hαint
  obtain ⟨M, hM, hle⟩ := isFG_of (M₀ ⊔ IntermediateField.adjoin K {α})
  have hαM : α ∈ M := hle (le_sup_right (a := M₀) (IntermediateField.mem_adjoin_simple_self K α))
  refine ⟨M, hM, hαM, fun τ hτ => ?_⟩
  have hτ₀ : CondM w M₀ τ := hτ.mono w (le_trans le_sup_left hle)
  -- `τ α` is a root of `g`
  have hcoef : (g.map (ιΩ w)).map (τ : Ω →+* Ω) = g.map (ιΩ w) := by
    ext i
    rw [coeff_map, coeff_map]
    by_cases hi : i ∈ g.support
    · exact (hM₀ _ (Finset.mem_image_of_mem _ hi)).2 τ hτ₀
    · rw [notMem_support_iff.mp hi, map_zero, map_zero]
  have hτα : (g.map (ιΩ w)).eval (τ α) = 0 := by
    rw [← hcoef, Polynomial.eval_map]
    change eval₂ (τ : Ω →+* Ω) ((τ : Ω →+* Ω) α) _ = 0
    rw [eval₂_at_apply, hα, map_zero]
  have hτw : τ α - α ∈ w.nonunits := hτ α hαM hαw
  by_contra hne
  have hταw : τ α ∈ w := by
    have : τ α = α + (τ α - α) := by ring
    rw [this]
    exact add_mem hαw (ValuationSubring.nonunits_le hτw)
  let gw := g.map (ιw w)
  have root_of : ∀ (x : Ω) (hx : x ∈ w), (g.map (ιΩ w)).eval x = 0 → gw.IsRoot ⟨x, hx⟩ := by
    intro x hx h
    apply Subtype.ext
    have e : g.map (ιΩ w) = gw.map (algebraMap w Ω) := by
      rw [Polynomial.map_map]; rfl
    rw [e, Polynomial.eval_map] at h
    change algebraMap w Ω (gw.eval ⟨x, hx⟩) = algebraMap w Ω 0
    rw [← eval₂_at_apply, map_zero]
    exact h
  have h2 := derivative_eval_eq_zero_of_two_roots w gw (root_of α hαw hα)
    (root_of (τ α) hταw hτα) (fun h => hne (congrArg Subtype.val h).symm)
    (by
      rw [eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_max_iff]
      exact hτw)
  apply hs
  rw [← h2, Polynomial.map_map]


theorem map_ιΩ_eq (g : (wE (K := K) w)[X]) : g.map (ιΩ w) = (g.map (ιw w)).map (algebraMap w Ω) := by
  rw [Polynomial.map_map]; rfl

instance isLocalHom_ιw : IsLocalHom (ιw (K := K) w) := by
  constructor
  intro a ha
  by_contra h
  have h1 : a ∈ maximalIdeal (wE (K := K) w) := h
  rw [mem_max_comap_iff] at h1
  have h2 : ιw w a ∈ maximalIdeal w := by rw [mem_max_iff]; exact h1
  exact h2 ha

/-- **The valuation ring of the inertia field is henselian.** -/
theorem henselian_wE : HenselianLocalRing (wE (K := K) w) where
  is_henselian f hf a₀ h₁ h₂ := by
    let q := f.map (ιw w)
    have hq : q.Monic := hf.map _
    have hc : q.eval (ιw w a₀) ∈ maximalIdeal w := by
      rw [Polynomial.eval_map, eval₂_at_apply, mem_max_iff, ιw_coe]
      exact (mem_max_comap_iff w _ _).mp h₁
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
    obtain ⟨α, hα, hαc⟩ := exists_root_near w q hq _ hc
    have hroot : (f.map (ιΩ w)).eval (α : Ω) = 0 := by
      rw [map_ιΩ_eq, Polynomial.eval_map]
      change eval₂ (algebraMap w Ω) (algebraMap w Ω α) q = 0
      rw [eval₂_at_apply, hα.eq_zero, map_zero]
    have hres : residue w α = residue w (ιw w a₀) := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hαc
    have hsimple : ((f.map ((residue w).comp (ιw w))).derivative).eval
        (residue w ⟨(α : Ω), α.2⟩) ≠ 0 := by
      have e : (⟨(α : Ω), α.2⟩ : w) = α := rfl
      rw [e, hres, derivative_map, Polynomial.eval_map]
      change eval₂ ((residue w).comp (ιw w)) (((residue w).comp (ιw w)) a₀) _ ≠ 0
      rw [eval₂_at_apply, RingHom.comp_apply, residue_ne_zero_iff_isUnit]
      exact h₂.map _
    have hαE := mem_inertiaField_of_simple_root w f (α : Ω) hroot α.2 hsimple
    let a : wE (K := K) w := ⟨⟨α, hαE⟩, by exact α.2⟩
    refine ⟨a, ?_, ?_⟩
    · have h0 : ιΩ w (f.eval a) = 0 := by
        rw [← eval₂_at_apply, ← Polynomial.eval_map]; exact hroot
      apply Subtype.ext
      apply (algebraMap (inertiaField (K := K) w) Ω).injective
      change ιΩ w _ = algebraMap _ Ω 0
      rw [map_zero]
      exact h0
    · rw [mem_max_comap_iff]
      have := (mem_max_iff w _).mp hαc
      exact this

/-- **The residue field of the inertia field is separably closed.** -/
theorem isSepClosed_wE : IsSepClosed (ResidueField (wE (K := K) w)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  apply IsSepClosed.of_exists_root
  intro p hpm hpirr hpsep
  obtain ⟨g, hgp, hgdeg, hgm⟩ := lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective (residue _) residue_surjective p) hpm
  have hdeg : (g.map (ιΩ w)).degree ≠ 0 := by
    rw [hgm.degree_map, degree_eq_natDegree hgm.ne_zero, hgdeg]
    exact_mod_cast (Irreducible.natDegree_pos hpirr).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (g.map (ιΩ w)) hdeg
  have hαw : α ∈ w := by
    letI : Algebra (wE (K := K) w) Ω := (ιΩ w).toAlgebra
    exact mem_of_isIntegral w (A := wE (K := K) w) (fun a => a.2)
      ⟨g, hgm, by rwa [IsRoot, Polynomial.eval_map] at hα⟩
  -- the residue polynomial
  let κm := ResidueField.map (ιw (K := K) w)
  have hgw : g.map ((residue w).comp (ιw w)) = p.map κm := by
    rw [← hgp, Polynomial.map_map, ResidueField.map_comp_residue]
  have hgw0 : (g.map (ιw w)).eval ⟨α, hαw⟩ = 0 := by
    apply Subtype.ext
    change algebraMap w Ω _ = algebraMap w Ω 0
    rw [map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, ← map_ιΩ_eq]
    exact hα
  have hroot' : (p.map κm).eval (residue w ⟨α, hαw⟩) = 0 := by
    rw [← hgw, ← Polynomial.map_map, Polynomial.eval_map, eval₂_at_apply, hgw0, map_zero]
  have hsimple : ((g.map ((residue w).comp (ιw w))).derivative).eval
      (residue w ⟨α, hαw⟩) ≠ 0 := by
    rw [hgw]
    have := (hpsep.map (f := κm)).eval₂_derivative_ne_zero (RingHom.id _) (x := residue w ⟨α, hαw⟩)
      (by rw [← Polynomial.eval]; exact hroot')
    exact this
  have hαE := mem_inertiaField_of_simple_root w g α hα hαw hsimple
  let a : wE (K := K) w := ⟨⟨α, hαE⟩, by exact hαw⟩
  refine ⟨residue _ a, ?_⟩
  have h0 : ιΩ w (g.eval a) = 0 := by
    rw [← eval₂_at_apply, ← Polynomial.eval_map]; exact hα
  have h1 : g.eval a = 0 := by
    apply Subtype.ext
    apply (algebraMap (inertiaField (K := K) w) Ω).injective
    change ιΩ w _ = algebraMap _ Ω 0
    rw [map_zero]
    exact h0
  rw [← hgp, Polynomial.eval_map, eval₂_at_apply, h1, map_zero]

end Ring

section DVR

open ReductSplit ReductGlue

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)
  [CharZero K] [IsAlgClosure K Ω] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [PerfectField (ResidueField O)]

theorem mem_w_of_mem (hw : w.comap (algebraMap K Ω) = O) (a : O) : algebraMap K Ω a ∈ w := by
  have : (a : K) ∈ w.comap (algebraMap K Ω) := hw ▸ a.2
  exact this

theorem nonunits_iff_of (hw : w.comap (algebraMap K Ω) = O) (a : O) :
    algebraMap K Ω a ∈ w.nonunits ↔ a ∈ maximalIdeal O := by
  rw [← nonunits_comap (algebraMap K Ω) w (a : K), hw, ValuationSubring.mem_nonunits_iff,
    ← ValuationSubring.valuation_lt_one_iff]

/-- **Elements of the inertia field are uniformizer powers times units** (from `key_finite`). -/
theorem unit_pow (hw : w.comap (algebraMap K Ω) = O) (ϖ : O) (hϖ : Irreducible ϖ) (x : Ω)
    (hxE : x ∈ inertiaField (K := K) w) (hxw : x ∈ w) (hx0 : x ≠ 0) :
    ∃ n : ℕ, x / algebraMap K Ω ϖ ^ n ∈ w ∧ (x / algebraMap K Ω ϖ ^ n)⁻¹ ∈ w := by
  obtain ⟨M, ⟨hfd, hgal⟩, hxM, hfix⟩ := hxE
  haveI := hfd
  haveI := hgal
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  letI : Algebra O M := ((algebraMap K M).comp (algebraMap O K)).toAlgebra
  haveI : IsScalarTower O K M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let W := w.comap (algebraMap M Ω)
  have hAW : ∀ a : O, algebraMap O M a ∈ W := fun a => mem_w_of_mem w hw a
  have hctr : ∀ a : O, algebraMap O M a ∈ W.nonunits ↔ a ∈ maximalIdeal O := by
    intro a
    rw [nonunits_comap]
    exact nonunits_iff_of w hw a
  have hfix' : ∀ σ : M ≃ₐ[K] M, (∀ y ∈ W, σ y - y ∈ W.nonunits) → σ ⟨x, hxM⟩ = ⟨x, hxM⟩ := by
    intro σ hσ
    let τ : Ω ≃ₐ[K] Ω := σ.liftNormal Ω
    have hτ : ∀ m : M, τ (algebraMap M Ω m) = algebraMap M Ω (σ m) := fun m =>
      AlgEquiv.liftNormal_commutes σ Ω m
    have hcond : CondM w M τ := by
      intro y hyM hyw
      have h1 := hσ ⟨y, hyM⟩ hyw
      rw [nonunits_comap, map_sub, ← hτ] at h1
      exact h1
    have := hfix τ hcond
    apply (algebraMap M Ω).injective
    rw [← hτ]
    exact this
  have hx0' : (⟨x, hxM⟩ : M) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨n, h1, h2⟩ := key_finite (K := K) O W hAW hctr ϖ hϖ ⟨x, hxM⟩ hfix' hxw hx0'
  have e : ((algebraMap O M ϖ : M) : Ω) = algebraMap K Ω ϖ := rfl
  refine ⟨n, ?_, ?_⟩
  · have := h1; simpa [W, ValuationSubring.mem_comap, e] using this
  · have := h2; simpa [W, ValuationSubring.mem_comap, e] using this

theorem hE_eq (hw : w.comap (algebraMap K Ω) = O) :
    (wE (K := K) w).comap (algebraMap K (inertiaField (K := K) w)) = O := by
  rw [ValuationSubring.comap_comap]
  exact hw

theorem ιΩ_injective : Function.Injective (ιΩ (K := K) w) := fun a b h =>
  Subtype.ext (Subtype.ext h)

theorem ιΩ_comapHom (hw : w.comap (algebraMap K Ω) = O) (ϖ : O) :
    ιΩ w (comapHom (hE_eq w hw) ϖ) = algebraMap K Ω ϖ := rfl

theorem assoc_pow (hw : w.comap (algebraMap K Ω) = O) (ϖ : O) (hϖ : Irreducible ϖ)
    {a : wE (K := K) w} (ha : a ≠ 0) : ∃ n : ℕ, Associated (comapHom (hE_eq w hw) ϖ ^ n) a := by
  have hx0 : ιΩ w a ≠ 0 := fun h => ha (ιΩ_injective w (by rw [h, map_zero]))
  obtain ⟨n, h1, h2⟩ := unit_pow w hw ϖ hϖ (ιΩ w a) a.1.2 a.2 hx0
  have hϖ0 : algebraMap K Ω ϖ ≠ 0 := by
    rw [_root_.map_ne_zero]; exact fun h => hϖ.ne_zero (Subtype.ext h)
  have hyE : ιΩ w a / algebraMap K Ω ϖ ^ n ∈ inertiaField (K := K) w :=
    (inertiaField w).div_mem a.1.2 (pow_mem ((inertiaField w).algebraMap_mem _) n)
  have hyE' : (ιΩ w a / algebraMap K Ω ϖ ^ n)⁻¹ ∈ inertiaField (K := K) w :=
    (inertiaField w).inv_mem hyE
  let u : wE (K := K) w := ⟨⟨_, hyE⟩, by exact h1⟩
  let v : wE (K := K) w := ⟨⟨_, hyE'⟩, by exact h2⟩
  have hy0 : ιΩ w a / algebraMap K Ω ϖ ^ n ≠ 0 := div_ne_zero hx0 (pow_ne_zero _ hϖ0)
  have huv : u * v = 1 := ιΩ_injective w (by
    rw [map_mul, map_one]; exact mul_inv_cancel₀ hy0)
  refine ⟨n, Units.mk u v huv (by rw [mul_comm]; exact huv), ιΩ_injective w ?_⟩
  rw [map_mul, map_pow, ιΩ_comapHom w hw]
  change algebraMap K Ω ϖ ^ n * (ιΩ w a / algebraMap K Ω ϖ ^ n) = ιΩ w a
  field_simp

theorem irreducible_comapHom (hw : w.comap (algebraMap K Ω) = O) (ϖ : O) (hϖ : Irreducible ϖ) :
    Irreducible (comapHom (hE_eq w hw) ϖ) := by
  set π := comapHom (hE_eq w hw) ϖ
  have hπ0 : π ≠ 0 := fun h => by
    have := congrArg (ιΩ w) h
    rw [ιΩ_comapHom w hw, map_zero, map_eq_zero] at this
    exact hϖ.ne_zero (Subtype.ext this)
  have hπnu : ¬ IsUnit π := by
    intro h
    have h1 : π ∉ maximalIdeal (wE (K := K) w) := fun hm => hm h
    apply h1
    rw [mem_max_comap_iff]
    exact (nonunits_iff_of w hw ϖ).mpr ((mem_maximalIdeal _).mpr hϖ.not_isUnit)
  refine ⟨hπnu, fun a b hab => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hau, hbu⟩ := hcon
  have ha0 : a ≠ 0 := fun h => hπ0 (by rw [hab, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hπ0 (by rw [hab, h, mul_zero])
  obtain ⟨n, u, hu⟩ := assoc_pow w hw ϖ hϖ ha0
  obtain ⟨m, u', hu'⟩ := assoc_pow w hw ϖ hϖ hb0
  rcases n with _ | n
  · exact hau (by rw [← hu, pow_zero, _root_.one_mul]; exact u.isUnit)
  rcases m with _ | m
  · exact hbu (by rw [← hu', pow_zero, _root_.one_mul]; exact u'.isUnit)
  have key : π * 1 = π * (π * (π ^ (n + m) * ((u : wE (K := K) w) * u'))) := by
    rw [_root_.mul_one]
    conv_lhs => rw [hab, ← hu, ← hu']
    ring
  have := mul_left_cancel₀ hπ0 key
  exact hπnu (isUnit_iff_exists_inv.mpr ⟨_, this.symm⟩)

theorem isDVR_wE (hw : w.comap (algebraMap K Ω) = O) :
    IsDiscreteValuationRing (wE (K := K) w) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, irreducible_comapHom w hw ϖ hϖ, fun hx => assoc_pow w hw ϖ hϖ hx⟩

end DVR

section ResAlg

open ReductSplit ReductGlue

/-- **The residue extension of an algebraic extension of valued fields is algebraic.** -/
theorem res_isAlgebraic {K E : Type} [Field K] [Field E] [Algebra K E] [Algebra.IsAlgebraic K E]
    {O : ValuationSubring K} {A : ValuationSubring E} (hA : A.comap (algebraMap K E) = O) :
    letI := (resMap hA).toAlgebra
    Algebra.IsAlgebraic (ResidueField O) (ResidueField A) := by
  letI := (resMap hA).toAlgebra
  constructor
  intro x
  obtain ⟨a, rfl⟩ := residue_surjective x
  set p := minpoly K (a : E)
  have hp0 : p ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral _)
  obtain ⟨i0, hi0, hmax⟩ := p.support.exists_max_image (fun i => O.valuation (p.coeff i))
    (nonempty_support_iff.mpr hp0)
  set c := p.coeff i0
  have hc0 : c ≠ 0 := mem_support_iff.mp hi0
  have hvc0 : O.valuation c ≠ 0 := by rwa [Ne, Valuation.zero_iff]
  let q := C c⁻¹ * p
  have hq : ∀ i, q.coeff i ∈ Set.range (algebraMap O K) := by
    intro i
    rw [coeff_C_mul]
    by_cases hi : i ∈ p.support
    · refine ⟨⟨_, O.mem_of_valuation_le_one _ ?_⟩, rfl⟩
      show O.valuation (c⁻¹ * p.coeff i) ≤ 1
      rw [map_mul, map_inv₀]
      rw [inv_mul_le_iff₀ (zero_lt_iff.mpr hvc0), _root_.mul_one]
      exact hmax i hi
    · rw [notMem_support_iff.mp hi, mul_zero]; exact ⟨0, map_zero _⟩
  obtain ⟨qO, hqO⟩ := (mem_lifts q).mp ((lifts_iff_coeff_lifts q).mpr hq)
  have hqO1 : qO.coeff i0 = 1 := by
    apply IsFractionRing.injective O K
    rw [← coeff_map, hqO, map_one, coeff_C_mul, inv_mul_cancel₀ hc0]
  refine ⟨qO.map (residue O), ?_, ?_⟩
  · intro h
    have := congrArg (fun r => r.coeff i0) h
    simp only [coeff_map, hqO1, map_one, coeff_zero] at this
    exact one_ne_zero this
  · rw [aeval_def, eval₂_map]
    have e1 : (algebraMap (ResidueField O) (ResidueField A)).comp (residue O) =
        (residue A).comp (comapHom hA) := by
      ext b; exact resMap_residue hA b
    rw [e1, ← hom_eval₂]
    have h0 : qO.eval₂ (comapHom hA) a = 0 := by
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero]
      change A.subtype (qO.eval₂ (comapHom hA) a) = 0
      rw [hom_eval₂]
      have e2 : A.subtype.comp (comapHom hA) = (algebraMap K E).comp (algebraMap O K) := rfl
      rw [e2, ← eval₂_map, hqO]
      change aeval (a : E) q = 0
      rw [map_mul, aeval_C, minpoly.aeval, mul_zero]
    rw [h0, map_zero]

end ResAlg

section Assemble

open ReductSplit ReductGlue

/-- **Extension of a valuation ring to an extension field** (Chevalley; via Mathlib's
`IsLocalRing.exists_factor_valuationRing`). -/
theorem exists_comap_eq {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (O : ValuationSubring K) :
    ∃ w : ValuationSubring Ω, w.comap (algebraMap K Ω) = O := by
  obtain ⟨B, hB, hloc⟩ := IsLocalRing.exists_factor_valuationRing ((algebraMap K Ω).comp O.subtype)
  refine ⟨B, le_antisymm ?_ (fun x hx => hB ⟨x, hx⟩)⟩
  intro x hx
  by_contra hxO
  have hx0 : x ≠ 0 := fun h => hxO (h ▸ O.zero_mem)
  have hinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
  have hunit : IsUnit (((algebraMap K Ω).comp O.subtype).codRestrict B.toSubring hB ⟨x⁻¹, hinv⟩) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K Ω x, hx⟩, Subtype.ext ?_⟩
    change algebraMap K Ω x⁻¹ * algebraMap K Ω x = 1
    rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  obtain ⟨u, hu⟩ := hloc.map_nonunit _ hunit
  apply hxO
  have h1 : ((u : O) : K) * (((u⁻¹ : Oˣ) : O) : K) = 1 :=
    congrArg (fun z : O => (z : K)) (Units.mul_inv u)
  rw [hu] at h1
  change x⁻¹ * _ = 1 at h1
  have : (((u⁻¹ : Oˣ) : O) : K) = x := by
    rw [← inv_inv x]; exact (eq_inv_of_mul_eq_one_right h1)
  rw [← this]; exact (u⁻¹ : Oˣ).1.2

/-- **`SHInside0` is a theorem.** -/
theorem shInside0 : SHInside0 := by
  intro K _ _ O _ _ Ω _ _ _ w hw
  haveI : Algebra.IsAlgebraic K (inertiaField (K := K) w) := inferInstance
  refine ⟨inertiaField (K := K) w, hE_eq w hw,
    ⟨⟨isDVR_wE w hw, henselian_wE w, isSepClosed_wE w⟩, inferInstance,
      fun ϖ hϖ => irreducible_comapHom w hw ϖ hϖ, ?_⟩,
    fun σ hσ x hx => inertia_fixes w hσ hx⟩
  letI := (resMap (hE_eq w hw)).toAlgebra
  haveI := res_isAlgebraic (hE_eq w hw)
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- **`SHExists0` is a theorem.** -/
theorem shExists0 : SHExists0 := by
  intro K _ _ O _ _
  obtain ⟨w, hw⟩ := exists_comap_eq (Ω := AlgebraicClosure K) O
  obtain ⟨E, hE, h, -⟩ := shInside0 K O (AlgebraicClosure K) w hw
  exact ⟨E, inferInstance, inferInstance, _, hE, h⟩

end Assemble

end ShRoute


/-!
# sh-route, part E: strict henselizations nest along finite extensions (`SHPair0`)

For `K'/K` finite and one valuation ring `w` of `Ω = K̄'` over `O' ⊆ K'`: the inertia field of `w`
over `K` lies in the inertia field over `K'`, and the latter lies in `E(K')` for `E` the former, so
it is finite over it.
-/

open IsLocalRing Polynomial

set_option linter.style.haveILetI false

namespace ShRoute

open ReductSplit ReductGlue

section Pair

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)

/-- The elements of `Gal(M/K)` acting trivially modulo `𝔪_w` on `w ∩ M`, as a submonoid. -/
def inertSub (M : IntermediateField K Ω) : Submonoid (M ≃ₐ[K] M) where
  carrier := {σ | ∀ y : M, (y : Ω) ∈ w → ((σ y : M) : Ω) - y ∈ w.nonunits}
  one_mem' := by
    intro y _
    simp only [AlgEquiv.one_apply, sub_self]
    exact zero_mem _
  mul_mem' := by
    intro σ ρ hσ hρ y hy
    have h1 := hρ y hy
    have hρy : ((ρ y : M) : Ω) ∈ w := by
      have : ((ρ y : M) : Ω) = (y : Ω) + (((ρ y : M) : Ω) - y) := by ring
      rw [this]; exact add_mem hy (ValuationSubring.nonunits_le h1)
    have h2 := hσ (ρ y) hρy
    have : (((σ * ρ) y : M) : Ω) - y = (((σ (ρ y)) : M) : Ω) - (ρ y : M) +
        (((ρ y : M) : Ω) - y) := by
      rw [AlgEquiv.mul_apply]; ring
    rw [this]
    exact add_mem h2 h1

/-- The inertia subgroup of `Gal(M/K)` (a submonoid of a finite group is a subgroup). -/
def inertM (M : IntermediateField K Ω) [FiniteDimensional K M] : Subgroup (M ≃ₐ[K] M) :=
  { inertSub w M with
    inv_mem' := by
      intro σ hσ
      have hn := orderOf_pos σ
      have h : σ⁻¹ = σ ^ (orderOf σ - 1) := by
        symm
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel hn, pow_orderOf_eq_one]
      change σ⁻¹ ∈ inertSub w M
      rw [h]
      exact (inertSub w M).pow_mem hσ _ }

theorem mem_inertM {M : IntermediateField K Ω} [FiniteDimensional K M] {σ : M ≃ₐ[K] M} :
    σ ∈ inertM w M ↔ ∀ y : M, (y : Ω) ∈ w → ((σ y : M) : Ω) - y ∈ w.nonunits := Iff.rfl

variable [CharZero K] [IsAlgClosure K Ω]
variable {K' : Type} [Field K'] [Algebra K K'] [FiniteDimensional K K'] [Algebra K' Ω]
  [IsScalarTower K K' Ω] [CharZero K'] [IsAlgClosure K' Ω]

/-- The inertia field over `K` lies in the inertia field over `K'`. -/
theorem inertiaField_le {x : Ω} (hx : x ∈ inertiaField (K := K) w) :
    x ∈ inertiaField (K := K') w := by
  obtain ⟨M, ⟨hfd, hgal⟩, hxM, hfix⟩ := hx
  haveI := hfd
  obtain ⟨t, ht⟩ : M.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  haveI : FiniteDimensional K' (IntermediateField.adjoin K' (t : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun z _ => Algebra.IsIntegral.isIntegral z)
  obtain ⟨M', hM', hNM'⟩ := isFG_of (K := K') (IntermediateField.adjoin K' (t : Set Ω))
  have hMM' : ∀ y ∈ M, y ∈ M' := by
    intro y hy
    rw [← ht] at hy
    have hle : IntermediateField.adjoin K (t : Set Ω) ≤ M'.restrictScalars K :=
      IntermediateField.adjoin_le_iff.mpr
        (fun z hz => hNM' (IntermediateField.subset_adjoin K' _ hz))
    exact hle hy
  exact ⟨M', hM', hMM' x hxM, fun τ hτ =>
    hfix (τ.restrictScalars K) (fun y hy hyw => hτ y (hMM' y hy) hyw)⟩

/-- The inertia field over `K'` lies in `E(t')` for `E` the inertia field over `K` and `t'` a
finite set generating `K'` over `K`. -/
theorem inertiaField_le_adjoin (t' : Finset Ω)
    (ht' : IntermediateField.adjoin K (t' : Set Ω) = (IsScalarTower.toAlgHom K K' Ω).fieldRange)
    {x : Ω} (hx : x ∈ inertiaField (K := K') w) :
    x ∈ IntermediateField.adjoin (inertiaField (K := K) w) (t' : Set Ω) := by
  set E := inertiaField (K := K) w
  set L := IntermediateField.adjoin E (t' : Set Ω)
  obtain ⟨M', ⟨hfd', hgal'⟩, hxM', hfix'⟩ := hx
  haveI := hfd'
  haveI : FiniteDimensional K M' := FiniteDimensional.trans K K' M'
  haveI : FiniteDimensional K (M'.restrictScalars K) := inferInstanceAs (FiniteDimensional K M')
  obtain ⟨M, ⟨hfd, hgal⟩, hM'M⟩ := isFG_of (K := K) (M'.restrictScalars K)
  haveI := hfd
  haveI := hgal
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  have hK'M : ∀ c : K', algebraMap K' Ω c ∈ M := fun c => hM'M (M'.algebraMap_mem c)
  let K'Ω : IntermediateField K Ω := (IsScalarTower.toAlgHom K K' Ω).fieldRange
  let K'M : IntermediateField K M := K'Ω.comap M.val
  let I := inertM w M
  let F := IntermediateField.fixedField I
  let x' : M := ⟨x, hM'M hxM'⟩
  have hx' : x' ∈ IntermediateField.fixedField (IntermediateField.fixingSubgroup (F ⊔ K'M)) := by
    rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_fixedField]
    rintro ⟨σ, hσI, hσK'⟩
    let τ : Ω ≃ₐ[K] Ω := σ.liftNormal Ω
    have hτ : ∀ m : M, τ (algebraMap M Ω m) = algebraMap M Ω (σ m) := fun m =>
      AlgEquiv.liftNormal_commutes σ Ω m
    have hτK' : ∀ c : K', τ (algebraMap K' Ω c) = algebraMap K' Ω c := by
      intro c
      have h1 := hτ ⟨_, hK'M c⟩
      have h2 : σ ⟨_, hK'M c⟩ = ⟨_, hK'M c⟩ :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσK' _ ⟨c, rfl⟩
      rw [h2] at h1
      exact h1
    let τ' : Ω ≃ₐ[K'] Ω := { τ.toRingEquiv with commutes' := hτK' }
    have hcond : CondM w M' τ' := by
      intro y hy hyw
      have h1 := hσI ⟨y, hM'M hy⟩ hyw
      have h2 := hτ ⟨y, hM'M hy⟩
      change τ y - y ∈ w.nonunits
      change τ (algebraMap M Ω ⟨y, hM'M hy⟩) - y ∈ w.nonunits
      rw [h2]
      exact h1
    have h3 : τ x = x := hfix' τ' hcond
    apply Subtype.ext
    change algebraMap M Ω (σ x') = algebraMap M Ω x'
    rw [← hτ]
    exact h3
  rw [IsGalois.fixedField_fixingSubgroup] at hx'
  have hle : F ⊔ K'M ≤ (L.restrictScalars K).comap M.val := by
    apply sup_le
    · intro f hf
      have hfE : (f : Ω) ∈ E := by
        refine ⟨M, ⟨hfd, hgal⟩, f.2, fun τ hτ => ?_⟩
        let σ : M ≃ₐ[K] M := τ.restrictNormal M
        have hσ : ∀ m : M, algebraMap M Ω (σ m) = τ (algebraMap M Ω m) := fun m =>
          AlgEquiv.restrictNormal_commutes τ M m
        have hσI : σ ∈ I := by
          intro y hyw
          change algebraMap M Ω (σ y) - y ∈ w.nonunits
          rw [hσ]
          exact hτ y y.2 hyw
        have := (IntermediateField.mem_fixedField_iff _ _).mp hf σ hσI
        change τ (algebraMap M Ω f) = algebraMap M Ω f
        rw [← hσ, this]
      exact L.algebraMap_mem ⟨_, hfE⟩
    · intro m hm
      have h1 : (m : Ω) ∈ IntermediateField.adjoin K (t' : Set Ω) := by rw [ht']; exact hm
      have h2 : IntermediateField.adjoin K (t' : Set Ω) ≤ L.restrictScalars K :=
        IntermediateField.adjoin_le_iff.mpr (fun z hz => IntermediateField.subset_adjoin E _ hz)
      exact h2 h1
  exact hle hx'

end Pair

section Assemble

theorem isSHUnram_inertia {K : Type} [Field K] [CharZero K] {O : ValuationSubring K}
    [IsDiscreteValuationRing O] [PerfectField (ResidueField O)] {Ω : Type} [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) : IsSHUnram O (wE (K := K) w) (hE_eq w hw) := by
  refine ⟨⟨isDVR_wE w hw, henselian_wE w, isSepClosed_wE w⟩, inferInstance,
      fun ϖ hϖ => irreducible_comapHom w hw ϖ hϖ, ?_⟩
  letI := (resMap (hE_eq w hw)).toAlgebra
  haveI := res_isAlgebraic (hE_eq w hw)
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- **`SHPair0` is a theorem.** -/
theorem shPair0 : SHPair0 := by
  intro K _ _ O _ _ K' _ _ _ O' _ hO
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  let Ω := AlgebraicClosure K'
  haveI : IsScalarTower K K' Ω := inferInstance
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed K', Algebra.IsAlgebraic.trans K K' Ω⟩
  obtain ⟨w, hw'⟩ := exists_comap_eq (Ω := Ω) O'
  have hw : w.comap (algebraMap K Ω) = O := by
    rw [IsScalarTower.algebraMap_eq K K' Ω, ← ValuationSubring.comap_comap, hw', hO]
  haveI : PerfectField (ResidueField O') := by
    letI := (resMap hO).toAlgebra
    haveI := res_isAlgebraic hO
    exact Algebra.IsAlgebraic.perfectField (ResidueField O)
  let E := inertiaField (K := K) w
  let E' := inertiaField (K := K') w
  let φ : E →+* E' :=
    { toFun := fun e => ⟨e, inertiaField_le w e.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra E E' := φ.toAlgebra
  haveI : IsScalarTower K E E' := IsScalarTower.of_algebraMap_eq (fun c => by
    apply Subtype.ext
    change algebraMap K Ω c = algebraMap E' Ω (algebraMap K E' c)
    rw [IsScalarTower.algebraMap_apply K K' E', IsScalarTower.algebraMap_apply K K' Ω]
    rfl)
  -- finiteness of `E'/E`
  let f := IsScalarTower.toAlgHom K K' Ω
  haveI : FiniteDimensional K f.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField f).toLinearEquiv
  obtain ⟨t', ht'⟩ : f.fieldRange.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  let L := IntermediateField.adjoin E (t' : Set Ω)
  haveI : FiniteDimensional E L := IntermediateField.finiteDimensional_adjoin
    (fun z _ => (Algebra.IsIntegral.isIntegral (R := K) z).tower_top)
  let ψ : E' →ₗ[E] L :=
    { toFun := fun x => ⟨x, inertiaField_le_adjoin w t' ht' x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := fun a b h =>
    Subtype.ext (congrArg (fun z : L => (z : Ω)) h)
  haveI : FiniteDimensional E E' := Module.Finite.of_injective ψ hψ
  exact ⟨E, E', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, wE (K := K) w, wE (K := K') w,
    hE_eq w hw, hE_eq w hw', isSHUnram_inertia w hw, isSHUnram_inertia w hw', rfl⟩

end Assemble

end ShRoute

/-! ## Final: the three strict-henselization leaves from the single Néron leaf -/

namespace ShRoute

open ReductSplit ReductGlue

/-- **`StrictHenselizationNeron` (char 0, perfect residue field) from `NeronBaseChangeSH`.** -/
theorem strictHenselizationNeron0_final (hN : NeronBaseChangeSH) : StrictHenselizationNeron0 :=
  strictHenselizationNeron0_of hN shExists0

/-- **`StrictHenselizationPair` (char 0, perfect residue field) from `NeronBaseChangeSH`.** -/
theorem strictHenselizationPair0_final (hN : NeronBaseChangeSH) : StrictHenselizationPair0 :=
  strictHenselizationPair0_of hN shPair0

/-- **`StrictHenselizationInside` (char 0, perfect residue field) from `NeronBaseChangeSH`.** -/
theorem strictHenselizationInside0_final (hN : NeronBaseChangeSH) : StrictHenselizationInside0 :=
  strictHenselizationInside0_of hN shInside0

/-- **The route**: the general-DVR SGA 7 IX leaves 4.7, 3.3 (first assertion) and 3.5, for `K` of
characteristic 0 with perfect residue field, from their strictly henselian forms, the bundle leaf
`MulEtaleAbelianScheme` and the one Néron leaf `NeronBaseChangeSH`. -/
theorem route_final (hR : RaynaudSemistableSH) (hP : SemistablePersistsSH)
    (hU : SemistableUnipotentSH) (hE : AvSplit.T4.MulEtaleAbelianScheme)
    (hN : NeronBaseChangeSH) :
    RaynaudSemistable0 ∧ SemistablePersistsDVR0 ∧ SemistableUnipotent0 :=
  ⟨raynaudSemistable0_of hR (strictHenselizationNeron0_final hN) hE,
   semistablePersistsDVR0_of hP (strictHenselizationPair0_final hN),
   semistableUnipotent0_of hU (strictHenselizationInside0_final hN)⟩

/-! ### Sanity checks: the new statements are no stronger than the old ones -/

/-- The Néron leaf is a specialization of reduct-glue's `NeronBaseChangeUnramifiedDVR` (the general
BLR §7.2 Thm. 1 form: ramification index 1, separable residue extension). -/
theorem neronBaseChangeSH_of_unramified (h : NeronBaseChangeUnramifiedDVR) : NeronBaseChangeSH := by
  intro K _ _ O _ K₁ _ _ O₁ hO hU A 𝒩 h𝒩
  obtain ⟨hSH, halg, hunr, hsep⟩ := hU
  haveI : IsDiscreteValuationRing O₁ := hSH.1
  haveI := halg
  haveI : Algebra.IsSeparable K K₁ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact h K O K₁ O₁ hO inferInstance hunr hsep A 𝒩 h𝒩

/-- Each char-0 leaf is a specialization of reduct-glue's leaf (same statement, two added
hypotheses). -/
theorem char0_of_general :
    (StrictHenselizationNeron → StrictHenselizationNeron0) ∧
    (StrictHenselizationPair → StrictHenselizationPair0) ∧
    (StrictHenselizationInside → StrictHenselizationInside0) ∧
    (RaynaudSemistable → RaynaudSemistable0) ∧
    (SemistablePersistsDVR → SemistablePersistsDVR0) ∧
    (SemistableUnipotent → SemistableUnipotent0) :=
  ⟨fun h K _ _ O _ _ => h K O, fun h K _ _ O _ _ => h K O, fun h K _ _ O _ _ => h K O,
   fun h K _ _ O _ _ => h K O, fun h K _ _ O _ _ => h K O, fun h K _ _ O _ _ => h K O⟩

end ShRoute

#print axioms ShRoute.key_finite
#print axioms ShRoute.henselian_wE
#print axioms ShRoute.isSepClosed_wE
#print axioms ShRoute.isDVR_wE
#print axioms ShRoute.res_isAlgebraic
#print axioms ShRoute.shExists0
#print axioms ShRoute.shInside0
#print axioms ShRoute.shPair0
#print axioms ShRoute.strictHenselizationNeron0_final
#print axioms ShRoute.strictHenselizationPair0_final
#print axioms ShRoute.strictHenselizationInside0_final
#print axioms ShRoute.route_final
#print axioms ShRoute.neronBaseChangeSH_of_unramified
#print axioms ShRoute.char0_of_general

